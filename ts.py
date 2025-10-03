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
from typed_z3 import Fun, Expr, Sort


class BaseTransitionSystem(ABC):
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

    def check_inductiveness(
        self, inv: Callable[[Self], z3.BoolRef], inv_name: str = "?"
    ) -> bool:
        results = []
        results.append(
            self.check_and_print(f"{inv_name} in init", self.init, z3.Not(inv(self)))
        )

        for name, trans in self.transitions.items():
            results.append(
                self.check_and_print(
                    f"{inv_name} in {name}",
                    inv(self),
                    trans,
                    z3.Not(inv(self.next)),
                    with_next=True,
                )
            )

        return all(results)

    def check_and_print(
        self,
        name: str,
        *args: z3.BoolRef,
        with_next: bool = False,
    ) -> bool:
        print(f"Checking {name}: ", end="", flush=True)
        args += (self.axiom,)
        if with_next:
            args += (self.next.axiom,)
        result = unsat_check(args, minimize_sorts=self.sorts)
        if result.unsat:
            print("passed")
            return True
        else:
            symbols = {symbol: None for symbol in self.symbols.values()}
            if with_next:
                symbols |= {
                    symbol: None
                    for symbol in self.next.symbols.values()
                    if symbol not in symbols
                }
            print("failed")
            print_model_in_order(result, symbols, name)
            return False

    def sanity_check(self) -> bool:
        if not self._check_sat("init", self.axiom, self.init):
            return False

        for name, tr in self.transitions.items():
            if not self._check_sat(name, self.axiom, self.next.axiom, tr):
                return False

        if not self._check_sat(
            f"init and tr",
            self.axiom,
            self.next.axiom,
            self.init,
            z3.Or(*self.transitions.values()),
        ):
            return False

        return True

    def _check_sat(self, name: str, *args: z3.BoolRef) -> bool:
        result = sat_check(args)
        if result.sat:
            print(f"Checking sat {name}: passed")
            return True
        else:
            print(f"Checking sat {name}: failed")
            print_unsat_core(result, name)
            return False


type TypedTerm[TR: BaseTransitionSystem, *Ts, E: z3.ExprRef] = Callable[[TR, *Ts], E]
type BoundTypedTerm[*Ts, E: z3.ExprRef] = Callable[[*Ts], E]
type ErasedBoundTypedTerm[E: z3.ExprRef] = Callable[..., E]

type TypedFormula[TR: BaseTransitionSystem, *Ts] = TypedTerm[TR, *Ts, z3.BoolRef]
type BoundTypedFormula[*Ts] = BoundTypedTerm[*Ts, z3.BoolRef]

type ErasedBoundTypedFormula = ErasedBoundTypedTerm[z3.BoolRef]

type RawTSTerm[T] = Callable[[BaseTransitionSystem, Params], T]


type Immutable[T] = Annotated[T, "immutable"]


class Params(Protocol):
    def items(self) -> Iterable[tuple[str, z3.ExprRef]]: ...

    def __getitem__(self, item: str) -> z3.ExprRef: ...

    def __contains__(self, item: str) -> bool: ...

    def __or__(self, other: Self) -> Self: ...


class ParamSpec(dict[str, Sort]):
    def primed(self) -> Self:
        return self.__class__({f"{param}'": sort for param, sort in self.items()})

    def doubled(self) -> Self:
        return self.__class__(self | self.primed())

    def prime(self, params: Params) -> Params:
        primed = dict(params.items())
        for param in self:
            primed[param + "'"] = primed[param]
        return primed

    def unprime(self, params: Params) -> Params:
        unprimed = dict(params.items())
        for param in self:
            unprimed[param] = unprimed[param + "'"]
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


from typing import TypeVar, Generic

_T = TypeVar("_T", covariant=True, default=z3.ExprRef, bound=z3.ExprRef)


@dataclass(frozen=True)
class TSTerm(Generic[_T]):
    spec: ParamSpec
    fun: RawTSTerm[_T]
    name: str

    @cached_property
    def params(self) -> Params:
        return self.spec.params()

    @cached_property
    def closed(self) -> bool:
        return not self.spec

    @cached_property
    def next(self) -> Self:
        return self.__class__(
            self.spec.primed(),
            lambda ts, params: self(ts.next, self.spec.unprime(params)),
            self.name + "'",
        )

    def __call__(self, ts: BaseTransitionSystem, params: Params | None = None) -> _T:
        return self.fun(ts, params or self.params)


type TSFormula = TSTerm[z3.BoolRef]


def universal_closure(formula: TSFormula, ts: BaseTransitionSystem) -> z3.BoolRef:
    return quantify(True, formula.spec.consts(), formula(ts), qid=formula.name)


def existential_closure(formula: TSFormula, ts: BaseTransitionSystem) -> z3.BoolRef:
    return quantify(False, formula.spec.consts(), formula(ts), qid=formula.name)


class TransitionSystem(BaseTransitionSystem, ABC):
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
                symbol = origin(name, mutable)
                symbols[field] = symbol.fun_ref
            elif issubclass(origin, Fun):
                symbol = origin(name, mutable)
                symbols[field] = symbol.fun
            else:
                continue
            object.__setattr__(self, field, symbol)

        return symbols

    @cached_property
    def next(self) -> Self:
        return self.__class__(self.suffix + "'")

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
        return self.left.inits | self.right.inits

    @cached_property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return self.left.axioms | self.right.axioms

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
        return self.left.inits | self.right.inits

    @cached_property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return self.left.axioms | self.right.axioms

    @cached_property
    def transitions(self) -> dict[str, z3.BoolRef]:
        return self.left.transitions | self.right.transitions


@overload
def ts_term2[E: z3.ExprRef](term: TSTerm[E], /) -> TSTerm[E]: ...


@overload
def ts_term2[TR: BaseTransitionSystem, *Ts, E: z3.ExprRef](
    term: Callable[[TR, *Ts], E], /
) -> TSTerm[E]: ...


@overload
def ts_term2[*Ts, E: z3.ExprRef](term: Callable[[*Ts], E], /) -> TSTerm[E]: ...


@overload
def ts_term2[E: z3.ExprRef](term: E, /, **kwargs: Sort) -> TSTerm[E]: ...


@overload
def ts_term2[E: z3.ExprRef](term: E, spec: ParamSpec, /) -> TSTerm[E]: ...


@overload
def ts_term2[E: z3.ExprRef](term: E, /, *args: Expr) -> TSTerm[E]: ...


# @overload
# def ts_term2[*Ts, E: Expr](term: Fun[*Ts, E], /, *args: *Ts) -> TSTerm[E]: ...


def ts_term2(term: Any, /, *args: Any, **kwargs: Any) -> TSTerm[Any]:
    if isinstance(term, TSTerm):
        return term
    # elif isinstance(term, Fun):
    #     return _ts_term_from_fun(term, _spec_for_term(args, kwargs))
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
    return ts_term(term)


def _ts_term_from_bound[*Ts, E: z3.ExprRef](term: Callable[[*Ts], E]) -> TSTerm[E]:
    return ts_term(unbind(term))


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


def ts_term[T: BaseTransitionSystem, *Ts, R: z3.ExprRef](
    term: TypedTerm[T, *Ts, R],
) -> TSTerm[R]:
    spec = get_spec(term, z3.ExprRef)
    raw_term = compile_with_spec(term, spec)
    return TSTerm(spec, raw_term, term.__name__)


def unbind[T: BaseTransitionSystem, *Ts, R](
    fun: Callable[[*Ts], R],
) -> Callable[[T, *Ts], R]:
    assert isinstance(fun, MethodType), f"{fun} is not a bound method"
    return cast(Callable[[T, *Ts], R], fun.__func__)


def init[T: BaseTransitionSystem, *Ts](
    fun: TypedFormula[T, *Ts],
) -> TypedFormula[T, *Ts]:
    setattr(fun, _TS_METADATA, _TS_INIT)
    return fun


def axiom[T: BaseTransitionSystem, *Ts](
    fun: TypedFormula[T, *Ts],
) -> TypedFormula[T, *Ts]:
    setattr(fun, _TS_METADATA, _TS_AXIOM)
    return fun


def transition[T: BaseTransitionSystem, *Ts](
    fun: TypedFormula[T, *Ts],
) -> TypedFormula[T, *Ts]:
    setattr(fun, _TS_METADATA, _TS_TRANSITION)
    return fun


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


_TS_METADATA = "__ts_metadata__"
_TS_INIT = object()
_TS_AXIOM = object()
_TS_TRANSITION = object()
_TS_SPECIALS = {
    "init",
    "inits",
    "axiom",
    "axioms",
    "transition",
    "transitions",
}


def _get_methods(
    ts: BaseTransitionSystem, marker: object
) -> Iterable[tuple[str, TSFormula]]:
    for name in dir(ts.__class__):
        if name in _TS_SPECIALS:
            continue
        attr: TypedFormula[Any] = getattr(ts.__class__, name)
        if (
            callable(attr)
            and hasattr(attr, _TS_METADATA)
            and getattr(attr, _TS_METADATA) is marker
        ):
            yield name, ts_term(attr)


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
