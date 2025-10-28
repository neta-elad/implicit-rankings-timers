"""
This module provides the framework for easily defining
transition systems and transition-system (parameteric) terms/formulas.

A transition-system term (`TSTerm`) can be thought of
as a term (or formula) with "holes"
for transition-system symbols
(constants, functions, relations)
and free variables.
"""

from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from functools import cached_property
from inspect import signature
from types import MethodType
from typing import (
    Annotated,
    Self,
    get_type_hints,
    get_origin,
    get_args,
    Any,
    TypeAliasType,
    cast,
    Protocol,
    overload,
)

import z3

from helpers import (
    quantify,
    unsat_check,
    print_model_in_order,
    sat_check,
    print_unsat_core,
    unpack_quantifier,
)
from metadata import get_methods, add_marker
from typed_z3 import Fun, Expr, Sort

__all__ = [
    "BaseTransitionSystem",
    "Params",
    "ParamSpec",
    "TSTerm",
    "TSFormula",
    "TermLike",
    "Immutable",
    "TransitionSystem",
    "init",
    "transition",
    "axiom",
]


class BaseTransitionSystem(ABC):
    """
    Abstract base class for all transition-system implementation:
    user-defined (via `TransitionSystem`) or programmatically built
    (like `timers.TimerTransitionSystem`).
    The fields of a `BaseTransitionSystem` represent a state in the system.
    """

    suffix: str

    def __init__(self, suffix: str) -> None:
        self.suffix = suffix

    @property
    @abstractmethod
    def symbols(self) -> dict[str, z3.FuncDeclRef]: ...

    def __getitem__(self, item: str) -> z3.FuncDeclRef:
        return self.symbols[item]

    @abstractmethod
    def clone(self, suffix: str) -> Self: ...

    @cached_property
    def next(self) -> Self:
        """
        :return: a post-state version of the transition system.
        """
        return self.clone(self.suffix + "'")

    @cached_property
    def reset(self) -> Self:
        return self.clone("")

    @property
    @abstractmethod
    def inits(self) -> dict[str, z3.BoolRef]: ...

    @cached_property
    def init(self) -> z3.BoolRef:
        return z3.And(*self.inits.values())

    @property
    @abstractmethod
    def axioms(self) -> dict[str, z3.BoolRef]: ...

    @cached_property
    def axiom(self) -> z3.BoolRef:
        return z3.And(*self.axioms.values())

    @property
    @abstractmethod
    def transitions(self) -> dict[str, z3.BoolRef]: ...

    @cached_property
    def sorts(self) -> set[z3.SortRef]:
        return (
            {
                symbol.domain(i)
                for symbol in self.symbols.values()
                for i in range(symbol.arity())
            }
            | {symbol.range() for symbol in self.symbols.values()}
        ) - {z3.IntSort(), z3.BoolSort()}

    def check_and_print(
        self,
        name: str,
        *args: z3.BoolRef,
        with_axioms: bool = True,
        with_next: bool = False,
        print_calls: bool = False,
    ) -> bool:
        print(f"Checking {name}: ", end="", flush=True)
        if with_axioms:
            args += (self.axiom,)
            if with_next:
                args += (self.next.axiom,)
        result = unsat_check(args, minimize_sorts=self.sorts, print_calls=print_calls)
        if result.unsat:
            print("passed")
            return True
        elif result.timeout:
            print("timeout")
            return False
        else:
            symbols = {symbol for symbol in self.symbols.values()}
            if with_next:
                symbols |= {
                    symbol
                    for symbol in self.next.symbols.values()
                    if symbol not in symbols
                }
            print("failed")
            print_model_in_order(result, symbols, name)
            return False

    def sanity_check(self) -> bool:
        """
        Provides a simple sanity check for the system:
        - Checking the initial state is satisfiable
        - Checking every transition is satisfiable
        - Checking the initial state & disjunction of all transitions is satisfiable
        :return: whether the system is sane
        """
        if not _check_sat("init", self.axiom, self.init):
            return False

        for name, tr in self.transitions.items():
            if not _check_sat(name, self.axiom, self.next.axiom, tr):
                return False

        if not _check_sat(
            f"init and tr",
            self.axiom,
            self.next.axiom,
            self.init,
            z3.Or(*self.transitions.values()),
        ):
            return False

        return True


type TypedTerm[TR: BaseTransitionSystem, *Ts, E: z3.ExprRef] = Callable[[TR, *Ts], E]
type TypedFormula[TR: BaseTransitionSystem, *Ts] = TypedTerm[TR, *Ts, z3.BoolRef]
type RawTSTerm[T] = Callable[[BaseTransitionSystem, Params], T]


class Params(Protocol):
    """
    A protocol representing parameters
    (free variables)
    of a parametric term.
    Can be thought of as a mapping of names (`str`) to Z3 expressions (`z3.ExprRef`).
    """

    def items(self) -> Iterable[tuple[str, z3.ExprRef]]: ...

    def __getitem__(self, item: str) -> z3.ExprRef: ...

    def __contains__(self, item: str) -> bool: ...

    def __or__(self, other: Self) -> Self: ...


class ParamSpec(dict[str, Sort]):
    """
    A specification of parameters:
    a mapping of names (`str`) to sorts (`typed_z3.Sort`, classes derived from `typed_z3.Expr`).
    """

    def primed(self) -> Self:
        return self.__class__({f"{param}'": sort for param, sort in self.items()})

    def doubled(self) -> Self:
        return self.__class__(self | self.primed())

    def prime(self, params: Params) -> Params:
        primed = dict(params.items())
        for param in self:
            primed[param + "'"] = primed[param]
            del primed[param]
        return primed

    def unprime(self, params: Params) -> Params:
        unprimed = dict(params.items())
        for param in self:
            unprimed[param] = unprimed[param + "'"]
            del unprimed[param + "'"]
        return unprimed

    def params(
        self, name_suffix: str = "", variable_suffix: str = ""
    ) -> dict[str, Expr]:
        return {
            f"{param}{name_suffix}": sort(param + variable_suffix)
            for param, sort in self.items()
        }

    def consts(self, suffix: str = "") -> list[Expr]:
        return [sort(param + suffix) for param, sort in self.items()]

    def __le__(self, other: Self) -> bool:
        return all(key in other and other[key] is value for key, value in self.items())


@dataclass(frozen=True)
class TSTerm[T]:
    """
    A transition-system term, producing a term of type `T`.
    """

    spec: ParamSpec
    """The specification for the parameters (free variables) of the term."""

    fun: RawTSTerm[T]
    name: str

    @cached_property
    def params(self) -> Params:
        return self.spec.params()

    @cached_property
    def next(self) -> Self:
        return self.__class__(
            self.spec.primed(),
            lambda ts, params: self(ts.next, self.spec.unprime(params)),
            self.name + "'",
        )

    def __call__(self, ts: BaseTransitionSystem, params: Params | None = None) -> T:
        return self.fun(ts, params or self.params)


type TSFormula = TSTerm[z3.BoolRef]
"""Shorthand for a `TSTerm` the returns a formula (`z3.BoolRef`)."""


def universal_closure(formula: TSFormula, ts: BaseTransitionSystem) -> z3.BoolRef:
    return quantify(True, formula.spec.consts(), formula(ts), qid=formula.name)


def existential_closure(formula: TSFormula, ts: BaseTransitionSystem) -> z3.BoolRef:
    return quantify(False, formula.spec.consts(), formula(ts), qid=formula.name)


type Immutable[T] = Annotated[T, "immutable"]
"""
Annotation for immutable symbols in a user-defined transition system
(see `TransitionSystem`).
"""


class TransitionSystem(BaseTransitionSystem, ABC):
    """
    User-defined transition system.
    A transition system is defined by subclassing this class,
    declaring the signature using fields,
    and annotating methods as
    conjuncts of the initial state ([`@init`](#init)),
    transitions ([`@transition`](#transition)),
    or axioms ([`@axiom`](#axiom)).

    Symbols (constants, functions, relations)
    in the vocabulary of the transition system's state
    are declared with fields, annotated with their sort:
    ```python
    class Thread(Finite): ...

    class TerminationSystem(TransitionSystem):
        # A mutable constant of sort Thread
        running: Thread

        # An immutable constant of sort Thread
        first: Immutable[Thread]

        # A mutable unary relation over threads
        on: Rel[Thread]

        # An immutable binary relation
        gt: Immutable[Rel[Thread, Thread]]

        # An immutable binary relation, declared to be well-founded
        lt: Immutable[WFRel[Thread]]

        # An immutable function from threads to threads
        prev: Immutable[Fun[Thread, Thread]]
    ```

    See also:
    `typed_z3.Expr`, `typed_z3.Fun`, `typed_z3.Rel`, `typed_z3.WFRel`,
    `axiom`, `init`, `transition`.
    """

    def __init__(self, suffix: str = "") -> None:
        super().__init__(suffix)
        _ = self.symbols  # init self.symbols

    def clone(self, suffix: str) -> Self:
        return self.__class__(suffix)

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        symbols = {}
        for field, hint in get_type_hints(self.__class__, include_extras=True).items():
            origin = get_origin(hint) or hint
            mutable = True
            if origin is Immutable:
                mutable = False
                origin = get_args(hint)[0]

            name = field
            if mutable:
                name += self.suffix

            if issubclass(origin, Expr):
                symbol = origin(name, mutable=mutable)
                symbols[field] = symbol.fun_ref
            elif issubclass(origin, Fun):
                symbol = origin(name, mutable=mutable)
                symbols[field] = symbol.fun
            else:
                continue
            object.__setattr__(self, field, symbol)

        return symbols

    @cached_property
    def inits(self) -> dict[str, z3.BoolRef]:
        inits: dict[str, z3.BoolRef] = {}
        for name, method in _get_methods(self, _TS_INIT):
            inits[name] = universal_closure(method, self)
        return inits

    @cached_property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return {
            name: universal_closure(method, self)
            for name, method in _get_methods(self, _TS_AXIOM)
        }

    @cached_property
    def transitions(self) -> dict[str, z3.BoolRef]:
        transitions: dict[str, z3.BoolRef] = {}
        for name, method in _get_methods(self, _TS_TRANSITION):
            transitions[name] = existential_closure(method, self)
        return transitions


class IntersectionTransitionSystem[L: BaseTransitionSystem, R: BaseTransitionSystem](
    BaseTransitionSystem
):
    left: L
    right: R

    def __init__(self, suffix: str, left: L, right: R) -> None:
        assert (
            suffix == left.suffix and left.suffix == right.suffix
        ), f"Malformed intersection system"
        super().__init__(suffix)
        self.left = left
        self.right = right

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        return self.left.symbols | self.right.symbols

    def clone(self, suffix: str) -> Self:
        return self.__class__(suffix, self.left.clone(suffix), self.right.clone(suffix))

    @cached_property
    def inits(self) -> dict[str, z3.BoolRef]:
        return _disjoint_merge(self.left.inits, self.right.inits)

    @cached_property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return _disjoint_merge(self.left.axioms, self.right.axioms)

    @cached_property
    def transitions(self) -> dict[str, z3.BoolRef]:
        return {
            f"{left_name}_X_{right_name}": z3.And(left, right)
            for left_name, left in self.left.transitions.items()
            for right_name, right in self.right.transitions.items()
        }


class UnionTransitionSystem[L: BaseTransitionSystem, R: BaseTransitionSystem](
    BaseTransitionSystem
):
    left: L
    right: R

    def __init__(self, suffix: str, left: L, right: R) -> None:
        assert (
            suffix == left.suffix and left.suffix == right.suffix
        ), f"Malformed union system"
        super().__init__(suffix)
        self.left = left
        self.right = right

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        return self.left.symbols | self.right.symbols

    def clone(self, suffix: str) -> Self:
        return self.__class__(suffix, self.left.clone(suffix), self.right.clone(suffix))

    @cached_property
    def inits(self) -> dict[str, z3.BoolRef]:
        return _disjoint_merge(self.left.inits, self.right.inits)

    @cached_property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return _disjoint_merge(self.left.axioms, self.right.axioms)

    @cached_property
    def transitions(self) -> dict[str, z3.BoolRef]:
        return _disjoint_merge(self.left.transitions, self.right.transitions)


@overload
def ts_term[E: z3.ExprRef](term: TSTerm[E], /) -> TSTerm[E]: ...


@overload
def ts_term[TR: BaseTransitionSystem, *Ts, E: z3.ExprRef](
    term: Callable[[TR, *Ts], E], /
) -> TSTerm[E]: ...


@overload
def ts_term[*Ts, E: z3.ExprRef](term: Callable[[*Ts], E], /) -> TSTerm[E]: ...


@overload
def ts_term[E: z3.ExprRef](term: E, /, **kwargs: Sort) -> TSTerm[E]: ...


@overload
def ts_term[E: z3.ExprRef](term: E, spec: ParamSpec, /) -> TSTerm[E]: ...


@overload
def ts_term[E: z3.ExprRef](term: E, /, *args: Expr) -> TSTerm[E]: ...


def ts_term(term: Any, /, *args: Any, **kwargs: Any) -> TSTerm[Any]:
    if isinstance(term, TSTerm):
        return term
    elif callable(term) and not isinstance(term, MethodType):
        return _ts_term_from_unbound(term)
    elif callable(term):
        return _ts_term_from_bound(term)

    assert isinstance(term, z3.ExprRef)
    return _ts_term_from_expr(term, _spec_for_term(args, kwargs))


def _spec_for_term(args: tuple[Expr, ...], kwargs: dict[str, Sort]) -> ParamSpec:
    if len(args) == 1 and isinstance(args[0], ParamSpec):
        return args[0]
    if args:
        kwargs = {str(arg): arg.__class__ for arg in args}

    return ParamSpec(**kwargs)


def _ts_term_from_unbound[TR: BaseTransitionSystem, *Ts, E: z3.ExprRef](
    term: Callable[[TR, *Ts], E],
) -> TSTerm[E]:
    spec = get_spec(term, z3.ExprRef)
    raw_term = compile_with_spec(term, spec)
    return TSTerm(spec, raw_term, term.__name__)


def _ts_term_from_bound[*Ts, E: z3.ExprRef](term: Callable[[*Ts], E]) -> TSTerm[E]:
    return _ts_term_from_unbound(unbind(term))


def _ts_term_from_expr[E: z3.ExprRef](expr: E, spec: ParamSpec) -> TSTerm[E]:
    def raw_term(ts: BaseTransitionSystem, params: Params) -> E:
        return substitute(expr, ts, params)

    return TSTerm(spec, raw_term, str(expr))


def _ts_term_from_fun[*Ts, E: Expr](fun: Fun[*Ts, E], spec: ParamSpec) -> TSTerm[E]:
    fun_name = str(fun)

    def raw_term(ts: BaseTransitionSystem, params: Params) -> E:
        args = [params[name] for name in spec]
        fun_decl = fun.fun
        if fun_name in ts.symbols:
            fun_decl = ts.symbols[fun_name]
        return cast(E, fun_decl(*args))

    return TSTerm(spec, raw_term, fun_name)


type TermLike[E: z3.ExprRef] = TSTerm[E] | Callable[..., E] | E
"""Any value that can be converted to a `TSTerm`."""


def unbind[T: BaseTransitionSystem, *Ts, R](
    fun: Callable[[*Ts], R],
) -> Callable[[T, *Ts], R]:
    assert isinstance(fun, MethodType), f"{fun} is not a bound method"
    return cast(Callable[[T, *Ts], R], fun.__func__)


def init[T: BaseTransitionSystem, *Ts](
    fun: TypedFormula[T, *Ts],
) -> TypedFormula[T, *Ts]:
    """
    Annotation (decorator) for defining a initial-state conjunct.
    Should only be used inside a subclass of `TransitionSystem`.
    Parameters to the decorated method are implicitly universally quantified.

    ```python
    class TerminationSystem(TransitionSystem):
        # snip...

        @init
        def initially_all_on(T: Thread) -> BoolRef:
            return self.on(T)
    ```
    """
    return add_marker(fun, _TS_INIT)


def axiom[T: BaseTransitionSystem, *Ts](
    fun: TypedFormula[T, *Ts],
) -> TypedFormula[T, *Ts]:
    """
    Annotation (decorator) for defining a axiom.
    Should only be used inside a subclass of `TransitionSystem`.
    Parameters to the decorated method are implicitly universally quantified.

    ```python
    class TerminationSystem(TransitionSystem):
        # snip...

        @axiom
        def first_is_minimal(T: Thread) -> BoolRef:
            return Or(self.first == X, self.lt(self.first, X))
    ```
    """
    return add_marker(fun, _TS_AXIOM)


def transition[T: BaseTransitionSystem, *Ts](
    fun: TypedFormula[T, *Ts],
) -> TypedFormula[T, *Ts]:
    """
    Annotation (decorator) for defining a transition.
    Should only be used inside a subclass of `TransitionSystem`.
    Parameters to the decorated method are implicitly existentially quantified.

    ```python
    class TerminationSystem(TransitionSystem):
        # snip...

        @transition
        def turn_off(t: Thread) -> BoolRef:
            return self.on.update({(t,): false})
    ```
    """
    return add_marker(fun, _TS_TRANSITION)


def get_spec[T: BaseTransitionSystem, *Ts, R: z3.ExprRef](
    term: TypedTerm[T, *Ts, R], *returns: type[z3.ExprRef]
) -> ParamSpec:
    sig = signature(term)
    return_hint = _resolve_type(sig.return_annotation)
    name = term.__name__

    assert any(
        issubclass(return_hint, expected_return) for expected_return in returns
    ), f"{name} returns {return_hint} instead of {", ".join(map(str, returns))}"

    params = list(sig.parameters.values())
    assert params, f"{name} must take at least one argument for the transition system"

    first_hint = _resolve_type(get_origin(params[0].annotation) or params[0].annotation)
    assert params[0].name == "self" or issubclass(
        first_hint, BaseTransitionSystem
    ), f"{name}'s first argument must be self or annotated with a transition system"

    params.pop(0)
    spec = {}
    for param in params:
        hint = _resolve_type(param.annotation)
        assert issubclass(
            hint, Expr
        ), f"parameter {param.name} of {name} must be annotated with a sort"
        spec[param.name] = hint

    return ParamSpec(spec)


def compile_with_spec[T: BaseTransitionSystem, *Ts, R: z3.ExprRef](
    formula: TypedTerm[T, *Ts, R], spec: ParamSpec
) -> RawTSTerm[R]:
    def compiled(ts: BaseTransitionSystem, params: Params) -> R:
        args = []
        for key in spec:
            args.append(params[key])

        return formula(ts, *args)  # type: ignore

    return compiled


_TS_INIT = object()
_TS_AXIOM = object()
_TS_TRANSITION = object()


def _get_methods(
    ts: BaseTransitionSystem, marker: object
) -> Iterable[tuple[str, TSFormula]]:
    for name, member in get_methods(ts, marker):
        yield name, ts_term(member)


def _resolve_type(t: Any) -> type:
    if isinstance(t, TypeAliasType):
        return _resolve_type(t.__value__)
    elif isinstance(t, type):
        return t
    assert False, f"Unresolvable type {t}"


def substitute[T: z3.ExprRef](
    expr: T, ts: BaseTransitionSystem, params: Params | None = None
) -> T:
    if params is None:
        params = cast(Params, {})

    def do_substitute(expr_: z3.ExprRef) -> z3.ExprRef:
        if z3.is_quantifier(expr_):
            variables, body = unpack_quantifier(expr_)
            body = cast(z3.BoolRef, do_substitute(body))
            return quantify(expr_.is_forall(), variables, body)
        decl = expr_.decl()
        name = str(decl)
        children = [do_substitute(child) for child in expr_.children()]
        if decl.kind() == z3.Z3_OP_UNINTERPRETED:
            if decl.arity() == 0 and name in params:
                return params[name]
            if name in ts.symbols:
                return ts.symbols[name](*children)
        return decl(*children)

    return cast(T, do_substitute(expr))


def _disjoint_merge[T](dict1: dict[str, T], dict2: dict[str, T]) -> dict[str, T]:
    if not dict1:
        return dict2
    if not dict2:
        return dict1

    result = {}
    for key, value in dict1.items():
        if key in dict2:
            key = "left-" + key
        result[key] = value

    for key, value in dict2.items():
        if key in dict1:
            key = "right-" + key
        result[key] = value
    return result


def _check_sat(name: str, *args: z3.BoolRef) -> bool:
    result = sat_check(args)
    if result.sat:
        print(f"Checking sat {name}: passed")
        return True
    else:
        print(f"Checking sat {name}: failed")
        print_unsat_core(result, name)
        return False
