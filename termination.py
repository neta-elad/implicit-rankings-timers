import time
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from functools import cached_property
from typing import ClassVar, cast, Any, Self, overload, Literal

import z3

from helpers import expr_size
from metadata import add_marker, get_methods, has_marker
from ranks import Rank, FiniteLemma, TimerRank
from temporal import Prop, nnf, contains_temporal
from timers import TimerTransitionSystem, create_timers, TimeFun, Time, timer_zero
from ts import (
    BaseTransitionSystem,
    IntersectionTransitionSystem,
    TSFormula,
    TransitionSystem,
    compile_with_spec,
    TSTerm,
    ParamSpec,
    UnionTransitionSystem,
    universal_closure,
    existential_closure,
    TermLike,
    ts_term,
)
from typed_z3 import Expr, Sort, true


class WitnessSystem(BaseTransitionSystem):
    witness_generator: Callable[[str], dict[str, z3.FuncDeclRef]]
    axiom_generator: Callable[[str], dict[str, z3.BoolRef]]

    def __init__(
        self,
        suffix: str,
        witness_generator: Callable[[str], dict[str, z3.FuncDeclRef]],
        axiom_generator: Callable[[str], dict[str, z3.BoolRef]],
    ) -> None:
        super().__init__(suffix)
        self.witness_generator = witness_generator
        self.axiom_generator = axiom_generator

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        return self.witness_generator(self.suffix)

    def clone(self, suffix: str) -> Self:
        return self.__class__(suffix, self.witness_generator, self.axiom_generator)

    @property
    def inits(self) -> dict[str, z3.BoolRef]:
        return {}

    @property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return self.axiom_generator(self.suffix)

    @property
    def transitions(self) -> dict[str, z3.BoolRef]:
        return {}


@dataclass(frozen=True)
class TemporalWitness:
    formula: TSFormula

    @cached_property
    def name(self) -> str:
        return self.formula.name

    @cached_property
    def sort(self) -> Sort:
        ((_param, sort),) = self.formula.spec.items()
        return sort

    @cached_property
    def param(self) -> str:
        ((param, _sort),) = self.formula.spec.items()
        return param

    @cached_property
    def symbol(self) -> Expr:
        return self.sort(self.name)

    def source(self, sys: BaseTransitionSystem) -> z3.BoolRef:
        return existential_closure(self.formula, sys)

    def instantiated(self, sys: BaseTransitionSystem) -> z3.BoolRef:
        return self.formula(sys, {self.param: self.symbol})

    def implication(self, sys: BaseTransitionSystem) -> z3.BoolRef:
        return z3.Implies(self.source(sys), self.instantiated(sys))


@dataclass(frozen=True)
class Invariant:
    source: TSFormula
    leaf: bool

    def formula[T: TransitionSystem](self, ts: "Proof[T]") -> z3.BoolRef:
        return universal_closure(self.source, ts)

    def count[T: TransitionSystem](self, ts: "Proof[T]") -> int:
        formula = self.source(ts)
        if z3.is_and(formula):
            return len(formula.children())
        return 1

    def size[T: TransitionSystem](self, ts: "Proof[T]") -> int:
        return expr_size(self.source(ts))


@dataclass(frozen=True)
class TemporalInvariant(Invariant):
    def formula[T: TransitionSystem](self, ts: "Proof[T]") -> z3.BoolRef:
        super_formula = super().formula(ts.reset)
        return timer_zero(ts.compile_timer(f"t_<{nnf(super_formula)}>")(ts))


def assert_no_temporal(inv_name: str, formula: z3.BoolRef) -> Literal[True]:
    assert not contains_temporal(
        formula
    ), f"Invariant {inv_name} must not contain temporal operators"
    return True


type PropProvider[T: TransitionSystem] = type[Prop[T]]


class Proof[T: TransitionSystem](BaseTransitionSystem, ABC):
    prop_type: PropProvider[T]
    ts: ClassVar[type[TransitionSystem]]
    _cache: ClassVar[dict[type[BaseTransitionSystem], type]] = {}

    def __init_subclass__(cls, prop: PropProvider[T], **kwargs: Any) -> None:
        super().__init_subclass__(**kwargs)
        cls.prop_type = prop

    def __init__(self, suffix: str = "") -> None:
        super().__init__(suffix)
        _ = self.witnesses  # initialize witnesses
        _ = self.temporal_witnesses  # initialize temporal witnesses

    @property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        return self.intersection.symbols

    def clone(self, suffix: str) -> Self:
        return self.__class__(suffix)

    @property
    def inits(self) -> dict[str, z3.BoolRef]:
        return self.intersection.inits

    @property
    def axioms(self) -> dict[str, z3.BoolRef]:
        return self.intersection.axioms

    @property
    def transitions(self) -> dict[str, z3.BoolRef]:
        return self.intersection.transitions

    @classmethod
    def __class_getitem__(cls, item: type[BaseTransitionSystem]) -> "type[Proof[T]]":
        if item not in cls._cache:
            cls._cache[item] = type(f"ProofOf{item}", (cls,), {"ts": item}, prop=None)

        return cls._cache[item]

    @abstractmethod
    def rank(self) -> Rank: ...

    @cached_property
    def sys(self) -> T:
        return cast(T, self.__class__.ts(self.suffix))

    @cached_property
    def witness_system(self) -> WitnessSystem:
        return WitnessSystem(
            self.suffix,
            lambda suffix: self.clone(suffix).witness_symbols
            | self.clone(suffix).temporal_witness_symbols,
            lambda suffix: self.clone(suffix).witness_axioms,
        )

    @cached_property
    def sys_with_witnesses(self) -> UnionTransitionSystem[T, WitnessSystem]:
        return UnionTransitionSystem(self.suffix, self.sys, self.witness_system)

    @cached_property
    def prop(self) -> z3.BoolRef:
        return self.prop_type(self.sys).prop()

    @cached_property
    def timers(self) -> TimerTransitionSystem:
        return create_timers(
            self.reset.sys_with_witnesses,
            self.reset.negated_prop,
            *self.reset.tracked_temporal_formulas.values(),
        ).clone(self.suffix)

    @cached_property
    def negated_prop(self) -> z3.BoolRef:
        return nnf(
            z3.And(
                z3.Not(self.prop),
                *(w.implication(self) for w in self.temporal_witnesses.values()),
            )
        )

    @cached_property
    def tracked_temporal_formulas(self) -> dict[str, z3.BoolRef]:
        return {
            name: universal_closure(method, self.reset)
            for name, method in _get_methods(self, _PROOF_TRACK_TEMPORAL)
        }

    @cached_property
    def intersection(
        self,
    ) -> IntersectionTransitionSystem[
        UnionTransitionSystem[T, WitnessSystem], TimerTransitionSystem
    ]:
        return IntersectionTransitionSystem(
            self.suffix, self.sys_with_witnesses, self.timers
        )

    def t(self, temporal_formula: z3.BoolRef) -> TimeFun:
        """
        :return: matching timer function for `temporal_formula`.
        """
        temporal_formula = nnf(temporal_formula)
        return self.timers.t(f"t_<{str(temporal_formula).replace("'", "")}>")

    @cached_property
    def system_invariants(self) -> dict[str, Invariant]:
        return {
            name: Invariant(
                method,
                has_marker(getattr(self.__class__, name), _PROOF_LEAF_INVARIANT),
            )
            for name, method in _get_methods(self, _PROOF_SYSTEM_INVARIANT)
            if assert_no_temporal(name, method(self))
        }

    @cached_property
    def invariants(self) -> dict[str, Invariant]:
        return {
            name: Invariant(
                method,
                has_marker(getattr(self.__class__, name), _PROOF_LEAF_INVARIANT),
            )
            for name, method in _get_methods(self, _PROOF_INVARIANT)
            if assert_no_temporal(name, method(self))
        }

    @cached_property
    def temporal_invariants(self) -> dict[str, Invariant]:
        return {
            name: TemporalInvariant(
                method,
                has_marker(getattr(self.__class__, name), _PROOF_LEAF_INVARIANT),
            )
            for name, method in _get_methods(self, _PROOF_TEMPORAL_INVARIANT)
        }

    @cached_property
    def all_invariants(self) -> dict[str, Invariant]:
        return self.system_invariants | self.invariants | self.temporal_invariants

    @cached_property
    def invariant(self) -> z3.BoolRef:
        return z3.And(*(inv.formula(self) for inv in self.all_invariants.values()))

    @cached_property
    def invariant_count(self) -> int:
        return sum(inv.count(self) for inv in self.all_invariants.values())

    @cached_property
    def invariant_size(self) -> int:
        return sum(1 + inv.size(self) for inv in self.all_invariants.values())

    @cached_property
    def size(self) -> int:
        return self.invariant_size + self.rank().expr_size(self)

    @cached_property
    def no_leaf_invariant(self) -> z3.BoolRef:
        return z3.And(
            *(inv.formula(self) for inv in self.all_invariants.values() if not inv.leaf)
        )

    @cached_property
    def no_leaf_system_invariant(self) -> z3.BoolRef:
        return z3.And(
            *(
                inv.formula(self)
                for inv in self.system_invariants.values()
                if not inv.leaf
            )
        )

    @cached_property
    def witnesses(self) -> dict[str, tuple[Expr, z3.BoolRef]]:
        witnesses = {}
        for method_name, method in _get_methods(self, _PROOF_WITNESS):
            witness_name = method_name
            assert (
                len(method.spec) == 1
            ), f"Witness method {method_name} must except exactly one argument"
            ((param, sort),) = method.spec.items()
            symbol = sort(witness_name + self.suffix, True)
            axiom = z3.Implies(
                existential_closure(method, self), method(self, {param: symbol})
            )
            witnesses[witness_name] = (symbol, axiom)
            setattr(self, witness_name, symbol)
        return witnesses

    @cached_property
    def witness_symbols(self) -> dict[str, z3.FuncDeclRef]:
        return {
            name: symbol.fun_ref for name, (symbol, _axiom) in self.witnesses.items()
        }

    @cached_property
    def witness_axioms(self) -> dict[str, z3.BoolRef]:
        return {name: axiom for name, (_symbol, axiom) in self.witnesses.items()}

    @cached_property
    def temporal_witnesses(self) -> dict[str, TemporalWitness]:
        witnesses = {}
        for method_name, method in _get_methods(self, _PROOF_TEMPORAL_WITNESS):
            witness_name = method_name
            assert (
                len(method.spec) == 1
            ), f"Witness method {method_name} must except exactly one argument"
            w = TemporalWitness(method)
            witnesses[witness_name] = w
            setattr(self, witness_name, w.symbol)
        return witnesses

    @cached_property
    def temporal_witness_symbols(self) -> dict[str, z3.FuncDeclRef]:
        return {name: w.symbol.fun_ref for name, w in self.temporal_witnesses.items()}

    def timer_rank(
        self,
        phi: TermLike[z3.BoolRef],
        alpha: TermLike[z3.BoolRef] | None,
        finite_lemma: FiniteLemma | None,
    ) -> Rank:
        ts_phi = ts_term(phi)
        timer_name = f"t_<{nnf(ts_phi(self))}>"
        spec = ts_phi.spec

        phi_size = expr_size(ts_phi(self))
        phi_term = self.compile_timer(timer_name, spec)

        return TimerRank(phi_term, phi_size, alpha, finite_lemma)

    @staticmethod
    def compile_timer(timer_name: str, spec: ParamSpec | None = None) -> TSTerm[Time]:
        if spec is None:
            spec = ParamSpec()

        def timer_term(ts: Self, *args: z3.ExprRef) -> Time:
            return ts.timers.t(timer_name)(*args)

        raw = compile_with_spec(timer_term, spec)

        phi_term = TSTerm(spec, raw, timer_name)
        return phi_term

    def check(self, *, check_conserved: bool = False) -> bool:
        start_time = time.monotonic()
        if not self.sys.sanity_check():
            print("fail: sanity")
            return False

        if not self._check_inv():
            print("fail: inv")
            return False

        if check_conserved and not self._check_conserved():
            print("fail: conserved")
            return False

        if not self._check_decreases():
            print("fail: decreases")
            return False

        if not self._check_soundness():
            print(f"fail: soundness")
            return False

        end_time = time.monotonic()
        print(f"All passed!")
        print(f"Time: {end_time - start_time:.3f} seconds")
        self.print_stats()
        return True

    def print_stats(self) -> None:
        print(f"Rank: {self.rank()}")
        print(f"Rank size: {self.rank().size}")
        print(f"Invariant count: {self.invariant_count}")
        print(f"Proof size: {self.size}")

    def _check_inv(self) -> bool:
        results = []

        # System invariants
        for name, inv in self.system_invariants.items():
            results.append(
                self.check_inductiveness(
                    lambda this: inv.formula(this),
                    name + "*",
                    self.sys_with_witnesses,
                    lambda this: z3.And(
                        inv.formula(this), this.no_leaf_system_invariant
                    ),
                )
            )

        # Regular invariants
        for name, inv in self.invariants.items():
            results.append(
                self.check_inductiveness(
                    lambda this: inv.formula(this),
                    name,
                    self,
                    lambda this: z3.And(inv.formula(this), this.no_leaf_invariant),
                )
            )

        # Temporal invariants
        for name, inv in self.temporal_invariants.items():
            results.append(
                self.check_inductiveness(
                    lambda this: inv.formula(this),
                    name,
                    self,
                    lambda this: z3.And(inv.formula(this), this.no_leaf_invariant),
                )
            )

        return all(results)

    def check_inductiveness(
        self,
        inv: Callable[[Self], z3.BoolRef],
        inv_name: str = "?",
        ts: BaseTransitionSystem | None = None,
        assumption: Callable[[Self], z3.BoolRef] | None = None,
    ) -> bool:
        if ts is None:
            ts = self

        if assumption is None:
            assumption = inv

        results = []
        results.append(
            self.check_and_print(
                f"{inv_name} in init",
                ts.axiom,
                ts.init,
                z3.Not(inv(self)),
                with_axioms=False,
            )
        )

        for name, trans in ts.transitions.items():
            results.append(
                self.check_and_print(
                    f"{inv_name} in {name}",
                    ts.axiom,
                    ts.next.axiom,
                    assumption(self),
                    trans,
                    z3.Not(inv(self.next)),
                    with_axioms=False,
                    with_next=True,
                )
            )

        return all(results)

    def _check_conserved(self, assumption: z3.BoolRef = true) -> bool:
        results = []
        for name, trans in self.transitions.items():
            results.append(
                self.check_and_print(
                    f"conserved in {name}",
                    self.invariant,
                    assumption,
                    trans,
                    z3.Not(self.rank().conserved(self)),
                    with_next=True,
                )
            )
        return all(results)

    def _check_decreases(self, assumption: z3.BoolRef = true) -> bool:
        results = []
        for name, trans in self.transitions.items():
            results.append(
                self.check_and_print(
                    f"decreases in {name}",
                    self.invariant,
                    assumption,
                    trans,
                    z3.Not(self.rank().decreases(self)),
                    with_next=True,
                )
            )
        return all(results)

    def _check_soundness(self) -> bool:
        if self.rank().condition.check(self, self.invariant):
            print("Checking soundness: passed")
            return True
        else:
            print("Checking soundness: failed")
            return False


type TypedProofFormula[T: Proof[Any], *Ts] = Callable[[T, *Ts], z3.BoolRef]


@overload
def system_invariant[T: Proof[Any], *Ts](
    *, leaf: bool = False
) -> Callable[[TypedProofFormula[T, *Ts]], TypedProofFormula[T, *Ts]]: ...


@overload
def system_invariant[T: Proof[Any], *Ts](
    fun: TypedProofFormula[T, *Ts], /
) -> TypedProofFormula[T, *Ts]: ...


def system_invariant[T: Proof[Any], *Ts](
    fun: Any | None = None, /, *, leaf: bool = False
) -> Any:
    def wrapper(actual_fun: TypedProofFormula[T, *Ts]) -> TypedProofFormula[T, *Ts]:
        if leaf:
            add_marker(actual_fun, _PROOF_LEAF_INVARIANT)
        return add_marker(actual_fun, _PROOF_SYSTEM_INVARIANT)

    if fun is not None:
        return wrapper(fun)
    return wrapper


@overload
def invariant[T: Proof[Any], *Ts](
    *, leaf: bool = False
) -> Callable[[TypedProofFormula[T, *Ts]], TypedProofFormula[T, *Ts]]: ...


@overload
def invariant[T: Proof[Any], *Ts](
    fun: TypedProofFormula[T, *Ts], /
) -> TypedProofFormula[T, *Ts]: ...


def invariant[T: Proof[Any], *Ts](
    fun: Any | None = None, /, *, leaf: bool = False
) -> Any:
    def wrapper(actual_fun: TypedProofFormula[T, *Ts]) -> TypedProofFormula[T, *Ts]:
        if leaf:
            add_marker(actual_fun, _PROOF_LEAF_INVARIANT)
        return add_marker(actual_fun, _PROOF_INVARIANT)

    if fun is not None:
        return wrapper(fun)
    return wrapper


@overload
def temporal_invariant[T: Proof[Any], *Ts](
    *, leaf: bool = False
) -> Callable[[TypedProofFormula[T, *Ts]], TypedProofFormula[T, *Ts]]: ...


@overload
def temporal_invariant[T: Proof[Any], *Ts](
    fun: TypedProofFormula[T, *Ts], /
) -> TypedProofFormula[T, *Ts]: ...


def temporal_invariant[T: Proof[Any], *Ts](
    fun: Any | None = None, /, *, leaf: bool = False
) -> Any:
    def wrapper(actual_fun: TypedProofFormula[T, *Ts]) -> TypedProofFormula[T, *Ts]:
        if leaf:
            add_marker(actual_fun, _PROOF_LEAF_INVARIANT)

        return add_marker(actual_fun, _PROOF_TEMPORAL_INVARIANT)

    if fun is not None:
        return wrapper(fun)
    return wrapper


def track[T: Proof[Any], *Ts](
    fun: TypedProofFormula[T, *Ts],
) -> TypedProofFormula[T, *Ts]:
    return add_marker(fun, _PROOF_TRACK_TEMPORAL)


def witness[T: Proof[Any], W: Expr](fun: TypedProofFormula[T, W]) -> W:
    return add_marker(fun, _PROOF_WITNESS)  # type: ignore


def temporal_witness[T: Proof[Any], W: Expr](fun: TypedProofFormula[T, W]) -> W:
    return add_marker(fun, _PROOF_TEMPORAL_WITNESS)  # type: ignore


_PROOF_SYSTEM_INVARIANT = object()
_PROOF_INVARIANT = object()
_PROOF_LEAF_INVARIANT = object()
_PROOF_TEMPORAL_INVARIANT = object()
_PROOF_WITNESS = object()
_PROOF_TEMPORAL_WITNESS = object()
_PROOF_TRACK_TEMPORAL = object()


def _get_methods(ts: Proof[Any], marker: object) -> Iterable[tuple[str, TSFormula]]:
    for name, member in get_methods(ts, marker):
        yield name, ts_term(member)
