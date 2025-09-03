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
)

import z3
from helpers import quantify, sat_check, print_model_in_order

from typed_z3 import Fun, Expr, Sort, Bool


class BaseTransitionSystem(ABC):
    @property
    @abstractmethod
    def symbols(self) -> dict[str, z3.FuncDeclRef]: ...

    def __getitem__(self, item: str) -> z3.FuncDeclRef:
        return self.symbols[item]

    @property
    @abstractmethod
    def next(self) -> Self: ...

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
        print_smtlib: bool = False,
    ) -> bool:
        args += (self.axiom,)
        if with_next:
            args += (self.next.axiom,)
        result = sat_check(args, minimize_sorts=self.sorts, print_smtlib=print_smtlib)
        if result[0] == z3.unsat:
            print(f"Checking {name}: passed")
            return True
        else:
            symbols = {symbol: None for symbol in self.symbols.values()}
            if with_next:
                symbols |= {
                    symbol: None
                    for symbol in self.next.symbols.values()
                    if symbol not in symbols
                }
            print(f"Checking {name}: failed")
            print_model_in_order(result, symbols, name)
            return False


type TypedTerm[T: BaseTransitionSystem, *Ts, R: z3.ExprRef] = Callable[[T, *Ts], R]
type BoundTypedTerm[*Ts, R: z3.ExprRef] = Callable[[*Ts], R]
type TypedFormula[T: BaseTransitionSystem, *Ts] = TypedTerm[T, *Ts, z3.BoolRef]
type BoundTypedFormula[*Ts] = BoundTypedTerm[*Ts, z3.BoolRef]
type ErasedBoundTypedFormula = Callable[..., z3.BoolRef]
type Params = dict[str, Expr]
type RawTSTerm[T] = Callable[[BaseTransitionSystem, Params], T]
type Immutable[T] = Annotated[T, "immutable"]


class ParamSpec(dict[str, Sort]):
    def primed(self) -> Self:
        return self.__class__({f"{param}'": sort for param, sort in self.items()})

    def doubled(self) -> Self:
        return self.__class__(self | self.primed())

    def prime(self, params: Params) -> Params:
        primed = dict(params)
        for param in self:
            primed[param + "'"] = primed[param]
        return primed

    def unprime(self, params: Params) -> Params:
        unprimed = dict(params)
        for param in self:
            unprimed[param] = unprimed[param + "'"]
        return unprimed

    def params(self, suffix: str = "") -> Params:
        return {f"{param}{suffix}": sort(param) for param, sort in self.items()}


@dataclass(frozen=True)
class TSTerm[T: z3.ExprRef = z3.ExprRef]:
    spec: ParamSpec
    fun: RawTSTerm[T]
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

    def __call__(self, ts: BaseTransitionSystem, params: Params | None = None) -> T:
        return self.fun(ts, params or self.params)


@dataclass(frozen=True)
class TSFormula(TSTerm[z3.BoolRef]):
    def forall(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        return quantify(True, self.params.values(), self(ts), qid=self.name)

    def exists(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        return quantify(False, self.params.values(), self(ts), qid=self.name)


class TransitionSystem(BaseTransitionSystem, ABC):
    suffix: str

    def __init__(self, suffix: str = "") -> None:
        self.suffix = suffix
        _ = self.symbols  # init self.symbols

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
            inits[name] = method.forall(self)
        return inits

    @cached_property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return {
            name: method.forall(self) for name, method in _get_methods(self, _TS_AXIOM)
        }

    @cached_property
    def transitions(self) -> dict[str, z3.BoolRef]:
        transitions: dict[str, z3.BoolRef] = {}
        for name, method in _get_methods(self, _TS_TRANSITION):
            transitions[name] = method.exists(self)
        return transitions


@dataclass(frozen=True)
class IntersectionTransitionSystem[L: BaseTransitionSystem, R: BaseTransitionSystem](
    BaseTransitionSystem
):
    left: L
    right: R

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        return self.left.symbols | self.right.symbols

    @cached_property
    def next(self) -> Self:
        return self.__class__(self.left.next, self.right.next)

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


def ts_formula[T: BaseTransitionSystem, *Ts](
    formula: TypedFormula[T, *Ts],
) -> TSFormula:
    spec = _get_spec(formula, z3.BoolRef, Bool)
    raw_term = _compile_with_spec(formula, spec)
    return TSFormula(spec, raw_term, formula.__name__)


def ts_term[T: BaseTransitionSystem, *Ts, R: z3.ExprRef](
    term: TypedTerm[T, *Ts, R],
) -> TSTerm[R]:
    spec = _get_spec(term, z3.ExprRef)
    raw_term = _compile_with_spec(term, spec)
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


def _get_spec[T: BaseTransitionSystem, *Ts, R: z3.ExprRef](
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


def _compile_with_spec[T: BaseTransitionSystem, *Ts, R: z3.ExprRef](
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
            yield name, ts_formula(attr)


def _resolve_type(t: Any) -> type:
    if isinstance(t, TypeAliasType):
        return _resolve_type(t.__value__)
    elif isinstance(t, type):
        return t
    assert False, f"Unresolvable type {t}"
