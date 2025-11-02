"""
This module provides constructors for implicit rankings.
"""

import operator
from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping, Sequence, Iterable
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import cast, Any, overload

import z3

from helpers import (
    strict_partial_immutable_order,
    minimal_in_order,
    quantify,
    instantiate,
    Predicate,
    strict_partial_immutable_order_axioms,
    expr_size,
)
from orders import Order, FormulaOrder, OrderLike
from timers import Time, timer_zero, timer_order
from ts import (
    BaseTransitionSystem,
    ParamSpec,
    TSFormula,
    TSTerm,
    Params,
    RawTSTerm,
    universal_closure,
    TermLike,
    ts_term,
    FormulaLike,
)
from typed_z3 import Expr, Rel, Sort

__all__ = [
    "Rank",
    "BinRank",
    "PosInOrderRank",
    "CondRank",
    "DomainPointwiseRank",
    "DomainLexRank",
    "LexRank",
    "PointwiseRank",
    "DomainPermutedRank",
    "TimerRank",
    "FiniteLemma",
]

type Hint = Mapping[str, TermLike[z3.ExprRef]]
type DomainPointwiseHints = Sequence[Hint]
type LeftHint = Sequence[Hint]
type RightHint = Sequence[Hint]
type DomainLexConservedHints = Sequence[Hint]
type DomainLexDecreasesHints = tuple[DomainLexConservedHints, Sequence[Hint]]
type DomainPermutedConservedHint = tuple[LeftHint, RightHint]
type DomainPermutedConservedHints = Sequence[DomainPermutedConservedHint]
type DomainPermutedDecreasesHint = tuple[LeftHint, RightHint, Hint]
type DomainPermutedDecreasesHints = Sequence[DomainPermutedDecreasesHint]
type FiniteSCHint = Sequence[Hint]
type FiniteSCHints = Sequence[FiniteSCHint]

type _RawTSRel[*Ts] = Callable[[BaseTransitionSystem], Rel[*Ts]]


def hint_size(ts: BaseTransitionSystem, hint: Iterable[Any] | None) -> int:
    if hint is None:
        return 0
    if hasattr(hint, "values") and callable(hint.values):
        return sum(expr_size(ts_term(term)(ts)) for term in hint.values())
    return sum(hint_size(ts, sub_hint) for sub_hint in hint)


@dataclass(frozen=True)
class TSRel[*Ts]:
    fun: _RawTSRel[*Ts]
    name: str

    def __call__(self, ts: BaseTransitionSystem) -> Rel[*Ts]:
        return self.fun(ts)

    def __str__(self) -> str:
        return self.name


@overload
def ts_rel[*Ts](rel: TSRel[*Ts]) -> TSRel[*Ts]: ...


@overload
def ts_rel[*Ts](rel: Rel[*Ts]) -> TSRel[*Ts]: ...


@overload
def ts_rel[TR: BaseTransitionSystem, *Ts](
    rel: Callable[[TR], Rel[*Ts]],
) -> TSRel[*Ts]: ...


def ts_rel(rel: Any) -> Any:
    if isinstance(rel, TSRel):
        return rel
    elif isinstance(rel, Rel):
        return _ts_rel_from_rel(rel)
    else:
        return _ts_rel_from_callable(rel)


def _ts_rel_from_rel[*Ts](rel: Rel[*Ts]) -> TSRel[*Ts]:
    name = str(rel.fun)

    def fun(ts: BaseTransitionSystem) -> Rel[*Ts]:
        if name in ts.symbols:
            return rel.__class__(name, mutable=rel.mutable, fun=ts.symbols[name])
        return rel

    return TSRel(fun, name)


def _ts_rel_from_callable[*Ts](
    rel: Callable[[BaseTransitionSystem], Rel[*Ts]],
) -> TSRel[*Ts]:
    return TSRel(rel, rel.__name__)


type RelLike[*Ts] = TSRel[*Ts] | Rel[*Ts] | _RawTSRel[*Ts] | Callable[
    [BaseTransitionSystem], Rel[*Ts]
]


class SoundnessCondition(ABC):
    @abstractmethod
    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool: ...


class TrueSC(SoundnessCondition):
    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        return True


@dataclass(frozen=True)
class WellFoundedSC[T: Expr](SoundnessCondition):
    order: TSRel[T, T]

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        rel = self.order(ts)
        sort, *_ = rel.signature
        print(f"Checking {rel.fun} well-founded: ", end="", flush=True)
        if sort.finite():
            print(f"{sort.ref()} finite")
            return True
        if rel.well_founded():
            print(f"{rel.fun} well-founded")
            return True
        print(f"{sort.ref()} not finite and {rel.fun} not well-founded")
        return False


@dataclass(frozen=True)
class WellFoundedOrderSC(SoundnessCondition):
    order: Order

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        return self.order.check_well_founded()


@dataclass(frozen=True)
class ConjunctionSC(SoundnessCondition):
    conditions: tuple[SoundnessCondition, ...]

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        return all(sc.check(ts, invariant) for sc in self.conditions)


@dataclass(frozen=True)
class FiniteSCBySort(SoundnessCondition):
    spec: ParamSpec

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        for sort in self.spec.values():
            if not sort.finite():
                print(f"{sort.ref()} is not finite")
                return False
        return True


@dataclass(frozen=True)
class FiniteLemma:
    """
    Helper lemma for proving finiteness of sets.

    Provides a formula `beta` that over-approximates elements that can be
    added to a set, and bounds the number of elements that can be added
    initially and in each transition.

    Example:
    ```python
    class Thread(Finite): ...
    class System(TransitionSystem):
        queue: Rel[Thread]

    class SysProof(Proof[System], prop=...):
        def in_queue(self, t: Thread) -> BoolRef:
            return self.sys.queue(t)

        def finite_lemma(self) -> FiniteLemma:
            return FiniteLemma(
                beta=self.in_queue,
                m=2,  # at most 2 threads added initially and per transition
                init_hints=[...],  # optional hints
                tr_hints=[...]  # optional hints
            )
    ```
    """

    beta: FormulaLike
    """Formula over-approximating added elements."""

    m: int = 1
    """Number of elements added initially and in each transition."""

    init_hints: FiniteSCHints | None = None
    """Hints for initial state finiteness check."""

    tr_hints: FiniteSCHints | None = None
    """Hints for transition finiteness check."""

    @cached_property
    def ts_beta(self) -> TSFormula:
        return ts_term(self.beta)


def lemma_size(ts: BaseTransitionSystem, lemma: FiniteLemma | None) -> int:
    if lemma is None:
        return 0
    return expr_size(lemma.ts_beta(ts))


@dataclass(frozen=True)
class FiniteSCByBeta(SoundnessCondition):
    spec: ParamSpec
    minimal: TSFormula
    lemma: FiniteLemma

    def __post_init__(self) -> None:
        assert self.beta.spec == self.alpha.spec

    @cached_property
    def alpha(self) -> TSFormula:
        theta_min = self.minimal
        return TSTerm(
            theta_min.spec,
            lambda ts, params: z3.Not(theta_min(ts, params)),
            f"alpha_<{theta_min.name}>",
        )

    @cached_property
    def beta(self) -> TSFormula:
        return self.lemma.ts_beta

    @cached_property
    def alpha_implies_beta(self) -> TSFormula:
        return TSTerm(
            self.beta.spec,
            lambda ts, params: z3.Implies(
                self.alpha(ts, params), self.beta(ts, params)
            ),
            f"alpha->beta_<{self.minimal.name}>",
        )

    def exists_ys_with_hints(
        self, ts: BaseTransitionSystem, body: z3.BoolRef, hints: FiniteSCHints | None
    ) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        formula = z3.Exists([y for y_tuple in ys for y in y_tuple], body)

        if hints is None:
            return formula

        def one_instantiation(hint_set: FiniteSCHint) -> z3.BoolRef:
            instantiation = reduce(
                operator.or_,
                (
                    _hint_to_params(ts, cast(Params, {}), hint, f"_{i}")
                    for i, hint in enumerate(hint_set)
                ),
            )
            return instantiate(formula, instantiation)

        return z3.Or(*(one_instantiation(hint_set) for hint_set in hints))

    def at_most_m_beta_at_init(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        params = self.spec.consts()

        body = z3.ForAll(
            params,
            z3.Implies(
                self.beta(ts),
                z3.Or(
                    *(
                        z3.And(*(param == y for param, y in zip(params, y_tuple)))
                        for y_tuple in ys
                    )
                ),
            ),
        )

        return self.exists_ys_with_hints(ts, body, self.lemma.init_hints)

    def at_most_m_beta_added(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        params = self.spec.consts()

        body = z3.ForAll(
            params,
            z3.Implies(
                self.beta(ts.next),
                z3.Or(
                    self.beta(ts),
                    *(
                        z3.And(*(param == y for param, y in zip(params, y_tuple)))
                        for y_tuple in ys
                    ),
                ),
            ),
        )

        return self.exists_ys_with_hints(ts, body, self.lemma.tr_hints)

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        ts_formula = self.alpha_implies_beta
        if not ts.check_and_print(
            self.alpha_implies_beta.name,
            invariant,
            z3.Not(universal_closure(ts_formula, ts)),
        ):
            return False
        self.at_most_m_beta_at_init(ts)
        z = ParamSpec(
            {
                param: sort
                for param, sort in self.minimal.spec.items()
                if param not in self.spec
            }
        )

        if not ts.check_and_print(
            f"init->at most {self.lemma.m} beta_<{self.minimal.name}>",
            ts.init,
            z3.Not(
                quantify(
                    True,
                    z.consts(),  # todo: maybe flip to exists ys forall z
                    self.at_most_m_beta_at_init(ts),
                )
            ),
        ):
            return False

        for name, trans in ts.transitions.items():
            if not ts.check_and_print(
                f"{name}->at most {self.lemma.m} beta added_<{self.minimal.name}>",
                invariant,
                trans,
                z3.Not(
                    quantify(
                        True,
                        z.consts(),  # todo: maybe flip to exists ys forall z
                        self.at_most_m_beta_added(ts),
                    ),
                ),
                with_next=True,
            ):
                return False

        return True


class Rank(ABC):
    """
    Abstract base class for all ranking constructors.

    A ranking constructor defines how to rank states in a transition system,
    typically used for proving termination or other liveness properties.
    Each rank has:
    - A `spec` defining free parameters
    - A `conserved` formula describing when the rank doesn't increase
    - A `decreases` formula describing when the rank decreases
    - A `minimal` formula describing minimal states
    - A `condition` for soundness checking

    Example:
    ```python
    class Ticket(Expr): ...

    class System(TransitionSystem):
        zero: Immutable[Ticket]
        service: Ticket

    class SysProof(Proof[System], prop=...):
        def is_zero(self, t: Ticket) -> BoolRef:
            return t == self.sys.zero

        def my_rank(self) -> Rank:
            return BinRank(self.is_zero)
    ```
    """

    @property
    @abstractmethod
    def condition(self) -> SoundnessCondition: ...

    @property
    @abstractmethod
    def decreases(self) -> TSFormula: ...

    @property
    @abstractmethod
    def size(self) -> int: ...

    @abstractmethod
    def expr_size(self, ts: BaseTransitionSystem) -> int: ...

    @property
    @abstractmethod
    def spec(self) -> ParamSpec: ...

    @property
    @abstractmethod
    def conserved(self) -> TSFormula: ...

    @property
    @abstractmethod
    def minimal(self) -> TSFormula: ...

    @property
    def closed(self) -> bool:
        return not self.spec


@dataclass(frozen=True)
class BinRank(Rank):
    """
    Binary implicit ranking constructor.
    Corresponds to a rank function
    that maps states where the formula `alpha` holds to 1
    and states where it does not to 0.

    Example:
    ```python
    class Ticket(Expr): ...
    class System(TransitionSystem):
        zero: Immutable[Ticket]

    class SysProof(Proof[System], prop=...):
        def my_formula(self, a: Ticket) -> BoolRef:
            return a == self.sys.zero

        def my_bin_rank(self) -> Rank:
            return BinRank(self.my_formula)  # rank with free variable "a"
    ```
    """

    alpha: FormulaLike
    """Formula that determines when rank is 1 (True) vs 0 (False)."""

    @cached_property
    def ts_alpha(self) -> TSFormula:
        return ts_term(self.alpha)

    @property
    def spec(self) -> ParamSpec:
        return self.ts_alpha.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Implies(
                z3.Not(self.ts_alpha(ts, params)),
                z3.Not(self.ts_alpha.next(ts, params)),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.Not(self.ts_alpha(ts, params)),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return TrueSC()

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.ts_alpha(ts, params),
                z3.Not(self.ts_alpha.next(ts, params)),
                self.conserved(ts, params),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + alpha
        return 1 + expr_size(self.ts_alpha(ts))

    def __str__(self) -> str:
        return f"Bin({self.ts_alpha.name})"


@dataclass(frozen=True)
class PosInOrderRank[T: Expr](Rank):
    """
    Position-in-order implicit ranking constructor.

    Example:
    ```python
    class Index(Finite): ...

    class System(TransitionSystem):
        lt: Immutable[Rel[Index, Index]]
        ptr: Index

    class SysProof(Proof[System], prop=...):
        def my_pos_rank(self) -> Rank:
            return PosInOrderRank(self.sys.ptr, self.sys.lt)
    ```
    """

    term: TermLike[T]
    """Term representing the element whose position in the order is ranked."""

    order: RelLike[T, T]
    """Binary relation defining the order over elements."""

    @cached_property
    def ts_term(self) -> TSTerm[T]:
        return ts_term(self.term)

    @cached_property
    def ts_order(self) -> TSRel[T, T]:
        return ts_rel(self.order)

    @property
    def spec(self) -> ParamSpec:
        return self.ts_term.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                strict_partial_immutable_order(self.ts_order(ts)),
                z3.Or(
                    self.ts_order(ts)(
                        self.ts_term.next(ts, params),
                        self.ts_term(ts, params),
                    ),
                    self.ts_term.next(ts, params) == self.ts_term(ts, params),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: minimal_in_order(
                self.ts_term(ts, params), self.ts_order(ts)
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return WellFoundedSC(self.ts_order)

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                strict_partial_immutable_order(self.ts_order(ts)),
                self.ts_order(ts)(
                    self.ts_term.next(ts, params), self.ts_term(ts, params)
                ),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + order + term
        return 1 + 1 + expr_size(self.ts_term(ts))

    def __str__(self) -> str:
        return f"Pos({self.ts_term.name})"


@dataclass(frozen=True)
class LexRank(Rank):
    """
    Lexicographic combination of multiple ranks.

    The rank decreases when the first rank decreases, or when the first rank
    is conserved and the second decreases, and so on.
    All ranks must use the same parameter specification.

    Example:
    ```python
    class Index(Finite): ...

    class System(TransitionSystem):
        lt: Immutable[Rel[Index, Index]]
        ptr1: Index
        ptr2: Index

    class SysProof(Proof[System], prop=...):
        def my_lex_rank(self) -> Rank:
            rank1 = PosInOrderRank(self.sys.ptr1, self.sys.lt)
            rank2 = PosInOrderRank(self.sys.ptr2, self.sys.lt)
            return LexRank(rank1, rank2)
    ```
    """

    ranks: tuple[Rank, ...]
    """The component ranks combined lexicographically."""

    @property
    def spec(self) -> ParamSpec:
        return self.ranks[0].spec

    def __init__(self, *ranks: Rank) -> None:
        assert ranks, "LexRank must receives at least one rank"
        spec = ranks[0].spec
        assert all(
            rank.spec == spec for rank in ranks
        ), "All ranks must use the same parameters"
        object.__setattr__(self, "ranks", ranks)

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                self.decreases(ts, params),
                z3.And(*(rank.conserved(ts, params) for rank in self.ranks)),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.And(
                *(rank.minimal(ts, params) for rank in self.ranks)
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return ConjunctionSC(tuple(rank.condition for rank in self.ranks))

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                *(
                    z3.And(
                        rank.decreases(ts, params),
                        *(
                            rank_.conserved(ts, params)
                            for j, rank_ in enumerate(self.ranks)
                            if j < i
                        ),
                    )
                    for i, rank in enumerate(self.ranks)
                )
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1 + sum(rank.size for rank in self.ranks)

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + sub-ranks
        return 1 + sum(rank.expr_size(ts) for rank in self.ranks)

    def __str__(self) -> str:
        return f"Lex({", ".join(map(str, self.ranks))})"


@dataclass(frozen=True)
class PointwiseRank(Rank):
    """
    Pointwise combination of multiple ranks.

    The rank decreases when any component rank decreases (and all are conserved).
    All ranks must use the same parameter specification.

    Example:
    ```python
    class Thread(Finite): ...
    class System(TransitionSystem):
        on: Rel[Thread]

    class SysProof(Proof[System], prop=...):
        def is_on(self, t: Thread) -> BoolRef:
            return self.sys.on(t)

        def my_pw_rank(self) -> Rank:
            rank1 = BinRank(lambda t: self.is_on(t))
            rank2 = BinRank(lambda t: Not(self.is_on(t)))
            return PointwiseRank(rank1, rank2)
    ```
    """

    ranks: tuple[Rank, ...]
    """The component ranks combined pointwise."""

    @property
    def spec(self) -> ParamSpec:
        return self.ranks[0].spec

    def __init__(self, *ranks: Rank) -> None:
        assert ranks, "PointwiseRank must receives at least one rank"
        spec = ranks[0].spec
        assert all(
            rank.spec == spec for rank in ranks
        ), "All ranks must use the same parameters"
        object.__setattr__(self, "ranks", ranks)

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                *(rank.conserved(ts, params) for rank in self.ranks)
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.And(
                *(rank.minimal(ts, params) for rank in self.ranks)
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return ConjunctionSC(tuple(rank.condition for rank in self.ranks))

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                z3.Or(*(rank.decreases(ts, params) for rank in self.ranks)),
                z3.And(*(rank.conserved(ts, params) for rank in self.ranks)),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1 + sum(rank.size for rank in self.ranks)

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + sub-ranks
        return 1 + sum(rank.expr_size(ts) for rank in self.ranks)

    def __str__(self) -> str:
        return f"PW({", ".join(map(str, self.ranks))})"


@dataclass(frozen=True)
class CondRank(Rank):
    """
    Conditional rank.
    Uses `rank` when `alpha` is true,
    otherwise maps to minimum.

    Example:
    ```python
    class Index(Finite): ...

    class System(TransitionSystem):
        lt: Immutable[Rel[Index, Index]]
        ptr: Index

        waiting: Bool

    class SysProof(Proof[System], prop=...):
        def my_cond_rank(self) -> Rank:
            return CondRank(PosInOrderRank(self.sys.ptr, self.sys.lt), self.sys.waiting)
    ```
    """

    rank: Rank
    """The inner rank used when condition is true."""

    alpha: FormulaLike
    """Conditional formula: when true, use `rank`; when false, rank is minimal."""

    @cached_property
    def ts_alpha(self) -> TSFormula:
        return ts_term(self.alpha)

    def __post_init__(self) -> None:
        assert (
            self.rank.spec == self.ts_alpha.spec
        ), "Rank and condition must use the same params"

    @property
    def spec(self) -> ParamSpec:
        return self.rank.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                z3.Not(self.ts_alpha.next(ts, params)),
                z3.And(
                    self.ts_alpha(ts, params),
                    self.ts_alpha.next(ts, params),
                    self.rank.conserved(ts, params),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.Not(self.ts_alpha(ts, params)),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return self.rank.condition

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                z3.And(
                    self.ts_alpha(ts, params), z3.Not(self.ts_alpha.next(ts, params))
                ),
                z3.And(
                    self.ts_alpha(ts, params),
                    self.ts_alpha.next(ts, params),
                    self.rank.decreases(ts, params),
                ),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1 + self.rank.size

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + sub-rank + alpha
        return 1 + self.rank.expr_size(ts) + expr_size(self.ts_alpha(ts))

    def __str__(self) -> str:
        return f"Cond({self.rank}, {self.ts_alpha.name})"


@dataclass(frozen=True)
class DomainPointwiseRank(Rank):
    """
    Domain-pointwise rank,
    decreases whenever the inner rank decreases for any tuple of elements
    (that we quantify over, see `quant_spec`).

    Example:
    ```python
    class Thread(Finite): ...
    class System(TransitionSystem):
        on: Rel[Thread]

    class SysProof(Proof[System], prop=...):
        def is_on(self, t: Thread) -> BoolRef:
            return self.sys.on(t)

        def dom_pw_rank(self) -> Rank:
            return DomainPointwiseRank(BinRank(self.is_on), ParamSpec(t=Thread))
    ```
    """

    rank: Rank
    """The inner rank applied to each element in the quantified domain."""

    quant_spec: ParamSpec
    """Parameters to quantify over (domain elements), removed from free parameters."""

    finite_lemma: FiniteLemma | None
    """
    Lemma for proving finiteness of the domain.
    Should be provided unless all sorts in `quant_spec` are declared finite.
    """

    decreases_hints: DomainPointwiseHints | None = None
    """
    Hints for instantiating the existential quantification over `quant_spec`.
    """

    @classmethod
    def close(
        cls,
        rank: Rank,
        finite_lemma: FiniteLemma | None,
        decreases_hints: DomainPointwiseHints | None = None,
    ) -> Rank:
        """
        Shorthand for creating a `DomainPointwiseRank` that closes over all free variables in `rank`.


        Example:
        ```python
        class Thread(Finite): ...
        class System(TransitionSystem):
            on: Rel[Thread]

        class SysProof(Proof[System], prop=...):
            def is_on(self, t: Thread) -> BoolRef:
                return self.sys.on(t)

            def dom_pw_rank(self) -> Rank:
                return DomainPointwiseRank.close(BinRank(self.is_on))
        ```
        """
        if not rank.spec:
            return rank
        return cls(rank, rank.spec, finite_lemma, decreases_hints)

    def __post_init__(self) -> None:
        assert self.quant_spec, "Must quantify over some parameters"
        assert (
            self.quant_spec.keys() <= self.rank.spec.keys()
        ), f"{self} has unknown quantified params"

    @property
    def spec(self) -> ParamSpec:
        return ParamSpec(
            {
                param: sort
                for param, sort in self.rank.spec.items()
                if param not in self.quant_spec
            }
        )

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.ForAll(
                self.quant_spec.consts(),
                self.rank.conserved(
                    ts,
                    params | self.quant_spec.params() | self.quant_spec.params("'"),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.ForAll(
                self.quant_spec.consts(),
                self.rank.minimal(ts, params | self.quant_spec.params()),
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return ConjunctionSC((self.rank.condition, self.finite_condition))

    @property
    def finite_condition(self) -> SoundnessCondition:
        if self.finite_lemma is None:
            return FiniteSCBySort(self.quant_spec)
        else:
            return FiniteSCByBeta(self.quant_spec, self.rank.minimal, self.finite_lemma)

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.conserved(ts, params),
                self.exists_with_hints(ts, params),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1 + self.rank.size

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + sub-rank + quant-spec + lemma + hints
        return (
            1
            + self.rank.expr_size(ts)
            + len(self.quant_spec)
            + lemma_size(ts, self.finite_lemma)
            + hint_size(ts, self.decreases_hints)
        )

    def exists_with_hints(self, ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
        formula = z3.Exists(
            self.quant_spec.consts(),
            self.rank.decreases(
                ts,
                params | self.quant_spec.params() | self.quant_spec.params("'"),
            ),
        )
        if self.decreases_hints is None:
            return formula

        return z3.Or(
            *(
                instantiate(formula, _hint_to_params(ts, params, hint))
                for hint in self.decreases_hints
            )
        )

    def __str__(self) -> str:
        return f"DomPW({self.rank}, [{", ".join(self.quant_spec.keys())}])"


@dataclass(frozen=True)
class DomainLexRank(Rank):
    """
    Domain lexicographic ranking constructor.

    Quantifies over a domain ordered by `order`, and uses lexicographic
    ordering based on the order relation. The inner rank is evaluated
    at all domain elements, ordered lexicographically.

    Example:
    ```python
    class Thread(Finite): ...
    class Ticket(Expr): ...

    class System(TransitionSystem):
        ticket: Rel[Thread, Ticket]
        lt: Immutable[WFRel[Ticket]]

    class SysProof(Proof[System], prop=...):
        def has_ticket(self, t: Thread, tick: Ticket) -> BoolRef:
            return self.sys.ticket(t, tick)

        def my_dom_lex_rank(self) -> Rank:
            return DomainLexRank(BinRank(self.has_ticket), self.sys.lt)
    ```
    """

    rank: Rank
    """The inner rank to apply at each domain element."""

    order: OrderLike
    """The order relation over the domain elements."""

    finite_lemma: FiniteLemma | None = None
    """Lemma for proving finiteness if domain sorts are not declared finite."""

    conserved_hints: DomainLexConservedHints | None = None
    """Hints for instantiating conserved formulas."""

    decreases_hints: DomainLexDecreasesHints | None = None
    """Hints for instantiating decreases formulas."""

    def __post_init__(self) -> None:
        assert (
            self.order_single_spec <= self.rank.spec
        ), f"{self} has unknown order params"

    @cached_property
    def compiled_order(self) -> Order:
        if isinstance(self.order, Order):
            return self.order
        return FormulaOrder(ts_term(self.order))

    @cached_property
    def order_formula(self) -> TSFormula:
        return self.compiled_order.ts_formula

    def order_pred(self, ts: BaseTransitionSystem) -> Predicate:
        formula = self.order_formula

        def predicate(*args: z3.ExprRef) -> z3.BoolRef:
            params = {name: arg for name, arg in zip(self.double_names, args)}
            return formula(ts, params)

        return predicate

    @cached_property
    def order_name(self) -> str:
        return self.order_formula.name

    @cached_property
    def order_single_spec(self) -> ParamSpec:
        name = self.order_formula.name
        spec = self.order_formula.spec
        spec_keys = list(spec.keys())
        assert len(spec_keys) % 2 == 0, f"Non-even order formula {name}"

        single_spec: dict[str, Sort] = {}
        for name, sort in spec.items():
            assert name.endswith("1") or name.endswith(
                "2"
            ), f"Bad param {name} to order formula"
            trunc_name = name[:-1]
            if name.endswith("1"):
                paired_name = trunc_name + "2"
                assert (
                    paired_name
                ) in spec, f"Missing paired param {paired_name} for {name}"
                paired_sort = spec[paired_name]
                assert (
                    paired_sort is sort
                ), f"Bad paired sort for {paired_name}: expected {sort.ref()} (like {name}), but got {paired_sort.ref()}"
                single_spec[trunc_name] = sort
            if name.endswith("2"):
                paired_name = trunc_name + "1"
                assert (
                    paired_name
                ) in spec, f"Missing paired param {paired_name} to {name}"
                paired_sort = spec[paired_name]
                assert (
                    paired_sort is sort
                ), f"Bad paired sort for {paired_name}: expected {sort.ref()} (like {name}), but got {paired_sort.ref()}"

        return ParamSpec(single_spec)

    @cached_property
    def sorts(self) -> list[Sort]:
        return list(self.order_single_spec.values())

    @cached_property
    def sort_refs(self) -> list[z3.SortRef]:
        return [sort.ref() for sort in self.sorts]

    @cached_property
    def double_names(self) -> list[str]:
        return [name + "1" for name in self.names] + [name + "2" for name in self.names]

    @cached_property
    def names(self) -> list[str]:
        return list(self.order_single_spec.keys())

    @cached_property
    def primed_names(self) -> list[str]:
        return [name + "'" for name in self.names]

    @property
    def quant_spec(self) -> ParamSpec:
        return ParamSpec({name: sort for name, sort in zip(self.names, self.sorts)})

    @property
    def spec(self) -> ParamSpec:
        return ParamSpec(
            {
                param: sort
                for param, sort in self.rank.spec.items()
                if param not in self.quant_spec
            }
        )

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: self.conserved_formula(ts, params, self.conserved_hints),
            f"{self}_<conserved>",
        )

    def conserved_formula(
        self,
        ts: BaseTransitionSystem,
        params: Params,
        y0s_hints: DomainLexConservedHints | None,
    ) -> z3.BoolRef:
        y0s = [z3.Const(f"_y0_{i}", sort.ref()) for i, sort in enumerate(self.sorts)]
        ys = [z3.Const(f"_y_{i}", sort.ref()) for i, sort in enumerate(self.sorts)]

        exists: z3.BoolRef = z3.Exists(
            y0s,
            z3.And(
                self.order_pred(ts)(*ys, *y0s),
                self.rank.decreases(
                    ts,
                    params
                    | dict(zip(self.names, y0s))
                    | dict(zip(self.primed_names, y0s)),
                ),
            ),
        )

        if y0s_hints is not None:
            exists = z3.Or(
                *(
                    instantiate(
                        exists,
                        {
                            f"_y0_{i}": expr
                            for i, (_name, expr) in enumerate(
                                _hint_to_params(ts, params, hint).items()
                            )
                        },
                    )
                    for hint in y0s_hints
                )
            )

        return z3.And(
            strict_partial_immutable_order_axioms(
                self.order_pred(ts), self.order_pred(ts.next), self.sort_refs
            ),
            z3.ForAll(
                ys,
                z3.Or(
                    self.rank.conserved(
                        ts,
                        params
                        | dict(zip(self.names, ys))
                        | dict(zip(self.primed_names, ys)),
                    ),
                    exists,
                ),
            ),
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.ForAll(
                self.quant_spec.consts(),
                self.rank.minimal(ts, params | self.quant_spec.params()),
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return ConjunctionSC((self.rank.condition, self.finite_condition))

    @property
    def finite_condition(self) -> SoundnessCondition:
        order_condition = WellFoundedOrderSC(self.compiled_order)
        if self.finite_lemma is None:
            return ConjunctionSC((order_condition, FiniteSCBySort(self.quant_spec)))
        else:
            return ConjunctionSC(
                (
                    order_condition,
                    FiniteSCByBeta(
                        self.quant_spec, self.rank.minimal, self.finite_lemma
                    ),
                )
            )

    @cached_property
    def decreases_conserved_hints(self) -> DomainLexConservedHints | None:
        if self.decreases_hints is None:
            return None
        return self.decreases_hints[0]

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.conserved_formula(ts, params, self.decreases_conserved_hints),
                self.decreases_formula(ts, params),
            ),
            f"{self}_<decreases>",
        )

    def decreases_formula(self, ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
        formula: z3.BoolRef = z3.Exists(
            self.quant_spec.consts(),
            self.rank.decreases(
                ts,
                params | self.quant_spec.params() | self.quant_spec.params("'"),
            ),
        )
        if self.decreases_hints is not None:
            formula = z3.Or(
                *(
                    instantiate(formula, _hint_to_params(ts, params, hint))
                    for hint in self.decreases_hints[1]
                )
            )
        return formula

    @property
    def size(self) -> int:
        return 1 + self.rank.size

    def order_expr_size(self, ts: BaseTransitionSystem) -> int:
        xs = [z3.Const(f"_x_{i}", sort.ref()) for i, sort in enumerate(self.sorts)]
        ys = [z3.Const(f"_y_{i}", sort.ref()) for i, sort in enumerate(self.sorts)]

        return expr_size(self.order_pred(ts)(*xs, *ys))

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + order + lemma + hints
        return (
            1
            + self.order_expr_size(ts)
            + lemma_size(ts, self.finite_lemma)
            + hint_size(ts, self.conserved_hints)
            + hint_size(ts, self.decreases_hints)
        )

    def __str__(self) -> str:
        return f"DomLex({self.rank}, {self.order_name}, [{", ".join(self.names)}])"


@dataclass(frozen=True)
class DomainPermutedRank(Rank):
    """
    Domain permuted ranking constructor.

    Quantifies over domain elements and allows permutation of `k` pairs
    of elements. The rank decreases if there exists a permutation where
    the inner rank decreases.

    Example:
    ```python
    class Thread(Finite): ...
    class System(TransitionSystem):
        on: Rel[Thread]

    class SysProof(Proof[System], prop=...):
        def is_on(self, t: Thread) -> BoolRef:
            return self.sys.on(t)

        def my_perm_rank(self) -> Rank:
            inner_rank = BinRank(self.is_on)
            return DomainPermutedRank(
                inner_rank,
                ParamSpec(t=Thread),
                k=2,  # allow permuting 2 pairs
                finite_lemma=None
            )
    ```
    """

    rank: Rank
    """The inner rank to apply."""

    quant_spec: ParamSpec
    """The parameters to quantify over (domain elements)."""

    k: int
    """Number of pairs of elements that can be permuted."""

    finite_lemma: FiniteLemma | None
    """Lemma for proving finiteness if domain sorts are not declared finite."""

    conserved_hints: DomainPermutedConservedHints | None = None
    """Hints for instantiating conserved formulas."""

    decreases_hints: DomainPermutedDecreasesHints | None = None
    """Hints for instantiating decreases formulas."""

    def __post_init__(self) -> None:
        assert self.quant_spec, "Must quantify over some parameters"
        assert (
            self.quant_spec.keys() <= self.rank.spec.keys()
        ), f"{self} has unknown quantified params"

    @cached_property
    def ys_left_right(self) -> list[tuple[dict[str, Expr], dict[str, Expr]]]:
        return [
            (
                self.quant_spec.params("", f"-left-{i}"),
                self.quant_spec.params("", f"-right-{i}"),
            )
            for i in range(1, self.k + 1)
        ]

    @cached_property
    def ys_sigma(self) -> Params:
        ys_left_right = self.ys_left_right
        ys = self.quant_spec.params()
        ys_sigma = self.quant_spec.params()
        for left, right in ys_left_right:
            ys_sigma = {
                name: z3.If(
                    ys[name] == right[name],
                    left[name],
                    z3.If(ys[name] == left[name], right[name], param),
                )
                for name, param in ys_sigma.items()
            }
        return ys_sigma

    @property
    def spec(self) -> ParamSpec:
        return ParamSpec(
            {
                param: sort
                for param, sort in self.rank.spec.items()
                if param not in self.quant_spec
            }
        )

    def exists_permutation(self, alpha: RawTSTerm[z3.BoolRef]) -> RawTSTerm[z3.BoolRef]:
        all_ys_left_right = [
            var
            for (left, right) in self.ys_left_right
            for name in left
            for var in (left[name], right[name])
        ]
        return lambda ts, params: z3.Exists(
            all_ys_left_right,
            z3.And(
                *(
                    z3.And(
                        *(right_i[name] != right_j[name] for name in right_i),
                        *(left_i[name] != left_j[name] for name in left_i),
                        *(right_i[name] != left_j[name] for name in right_i),
                    )
                    for i, (left_i, right_i) in enumerate(self.ys_left_right)
                    for j, (left_j, right_j) in enumerate(self.ys_left_right)
                    if i < j
                ),
                alpha(ts, (params) | self.quant_spec.prime(self.ys_sigma)),
            ),
        )

    def exists_permutation_conserved(self) -> RawTSTerm[z3.BoolRef]:
        alpha = lambda ts, params: z3.ForAll(
            self.quant_spec.consts(),
            self.rank.conserved(ts, params | self.quant_spec.params()),
        )

        def formula(ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
            result = self.exists_permutation(alpha)(ts, params)
            if self.conserved_hints is None:
                return result

            def hinted_exists_permutation(
                ts: BaseTransitionSystem,
                params: Params,
                hint: DomainPermutedConservedHint,
            ) -> z3.BoolRef:
                left_hint, right_hint = hint
                left_instantiation = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-left-{i + 1}")
                        for i, hint in enumerate(left_hint)
                    ),
                )
                right_instantiation = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-right-{i + 1}")
                        for i, hint in enumerate(right_hint)
                    ),
                )
                return instantiate(result, left_instantiation | right_instantiation)

            return z3.Or(
                *(
                    hinted_exists_permutation(ts, params, hint)
                    for hint in self.conserved_hints
                )
            )

        return formula

    def exists_permutation_decreases(self) -> RawTSTerm[z3.BoolRef]:
        alpha = lambda ts, params: z3.And(
            z3.ForAll(
                self.quant_spec.consts(),
                self.rank.conserved(
                    ts,
                    params
                    | self.quant_spec.params()
                    | self.quant_spec.prime(self.ys_sigma),
                ),
            ),
            z3.Exists(
                self.quant_spec.consts(),
                self.rank.decreases(
                    ts,
                    params
                    | self.quant_spec.params()
                    | self.quant_spec.prime(self.ys_sigma),
                ),
            ),
        )

        def formula(ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
            result = self.exists_permutation(alpha)(ts, params)
            if self.decreases_hints is None:
                return result

            def hinted_exists_permutation(
                hint: DomainPermutedDecreasesHint,
            ) -> z3.BoolRef:
                left_hint, right_hint, ys_hint = hint
                left_instantiation = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-left-{i + 1}")
                        for i, hint in enumerate(left_hint)
                    ),
                )
                right_instantiation = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-right-{i + 1}")
                        for i, hint in enumerate(right_hint)
                    ),
                )
                ys_instantiation = _hint_to_params(ts, params, ys_hint)
                return instantiate(
                    result, left_instantiation | right_instantiation | ys_instantiation
                )

            return z3.Or(
                *(hinted_exists_permutation(hint) for hint in self.decreases_hints)
            )

        return formula

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec,
            self.exists_permutation_conserved(),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.ForAll(
                self.quant_spec.consts(),
                self.rank.minimal(ts, params | self.quant_spec.params()),
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return ConjunctionSC((self.rank.condition, self.finite_condition))

    @property
    def finite_condition(self) -> SoundnessCondition:
        if self.finite_lemma is None:
            return FiniteSCBySort(self.quant_spec)
        else:
            return FiniteSCByBeta(self.quant_spec, self.rank.minimal, self.finite_lemma)

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec,
            self.exists_permutation_decreases(),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1 + self.rank.size

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + ys + k + lemma + hints
        return (
            1
            + len(self.quant_spec)
            + 1
            + lemma_size(ts, self.finite_lemma)
            + hint_size(ts, self.conserved_hints)
            + hint_size(ts, self.decreases_hints)
        )

    def __str__(self) -> str:
        return f"DomPerm({self.rank}, {self.quant_spec}, {self.k})"


@dataclass(frozen=True)
class TimerPosInOrderRank(Rank):
    term: TermLike[Time]

    @cached_property
    def ts_term(self) -> TSTerm[Time]:
        return ts_term(self.term)

    @property
    def spec(self) -> ParamSpec:
        return self.ts_term.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                timer_order(
                    self.ts_term.next(ts, params),
                    self.ts_term(ts, params),
                ),
                self.ts_term.next(ts, params) == self.ts_term(ts, params),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: timer_zero(self.ts_term(ts, params)),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return TrueSC()

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: timer_order(
                self.ts_term.next(ts, params), self.ts_term(ts, params)
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + term
        return 1 + expr_size(self.ts_term(ts))

    def __str__(self) -> str:
        return f"TimerPos({self.ts_term.name})"


@dataclass(frozen=True)
class TimerRank(Rank):
    """
    Ranking constructor based on timer values.

    Creates a rank from a timer term (of sort `timers.Time`). The rank decreases
    when the timer decreases, and is minimal when the timer is zero.
    If `alpha` is provided, the rank is conditional: it only applies when
    `alpha` is true, otherwise it's minimal.

    This rank is typically used through `proofs.Proof.timer_rank`, which
    automatically creates timers from temporal formulas.

    Example (using `proofs.Proof.timer_rank` method, recommended):
    ```python
    class Thread(Finite): ...
    class System(TransitionSystem):
        waiting: Rel[Thread]

    class SysProof(Proof[System], prop=...):
        def my_timer_rank(self, t: Thread) -> Rank:
            # Creates a timer rank from the formula
            return self.timer_rank(self.sys.waiting(t), None, None)
    ```
    """

    term: TermLike[Time]
    """The timer term to rank by."""

    term_size: int

    alpha: FormulaLike | None = None
    """Optional condition: when provided, rank is conditional on this formula."""

    finite_lemma: FiniteLemma | None = None
    """Lemma for proving finiteness if needed."""

    @cached_property
    def ts_term(self) -> TSTerm[Time]:
        return ts_term(self.term)

    @cached_property
    def ts_alpha(self) -> TSFormula | None:
        if self.alpha is None:
            return None
        return ts_term(self.alpha)

    def __post_init__(self) -> None:
        assert (
            self.ts_alpha is None or self.ts_term.spec == self.ts_alpha.spec
        ), f"Mismatch in params"

    @cached_property
    def rank(self) -> Rank:
        if self.ts_alpha is None:
            return DomainPointwiseRank.close(
                TimerPosInOrderRank(self.ts_term), self.finite_lemma
            )
        return DomainPointwiseRank.close(
            CondRank(TimerPosInOrderRank(self.ts_term), self.ts_alpha),
            self.finite_lemma,
        )

    @property
    def spec(self) -> ParamSpec:
        return self.rank.spec

    @property
    def conserved(self) -> TSFormula:
        return self.rank.conserved

    @property
    def minimal(self) -> TSFormula:
        return self.rank.minimal

    @property
    def condition(self) -> SoundnessCondition:
        return self.rank.condition

    @property
    def decreases(self) -> TSFormula:
        return self.rank.decreases

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + term + alpha + lemma
        alpha_size = 0
        if self.ts_alpha is not None:
            alpha_size = expr_size(self.ts_alpha(ts))
        return 1 + self.term_size + alpha_size + lemma_size(ts, self.finite_lemma)

    def __str__(self) -> str:
        if self.ts_alpha is None:
            return f"TimerRank({self.ts_term.name})"
        return f"TimerRank({self.ts_term.name}, {self.ts_alpha.name})"


def _hint_to_params(
    ts: BaseTransitionSystem, params: Params, hint: Hint, suffix: str = ""
) -> Params:
    return {f"{key}{suffix}": ts_term(term)(ts, params) for key, term in hint.items()}
