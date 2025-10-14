import operator
from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping, Sequence, Iterable
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import cast, Any, overload, Self

import z3

from helpers import (
    strict_partial_immutable_order,
    minimal_in_order,
    quantify,
    instantiate,
    Predicate,
    strict_partial_immutable_order_axioms,
    Instances,
    expr_size,
)
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
)
from typed_z3 import Expr, Rel, Sort

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


#
# def hints_size(ts: BaseTransitionSystem, hints: Iterable[Hint] | None) -> int:
#     if hints is None:
#         return 0
#     return sum(hint_size(ts, hint) for hint in hints)
#
#
# def m_hints_size(
#     ts: BaseTransitionSystem, multi_hints: Iterable[Iterable[Hint]] | None
# ) -> int:
#     if multi_hints is None:
#         return 0
#     return sum(hints_size(ts, hints) for hints in multi_hints)
#
#
# def mm_hints_size(
#     ts: BaseTransitionSystem, multi_hints: Iterable[Iterable[Iterable[Hint]]] | None
# ) -> int:
#     if multi_hints is None:
#         return 0
#     return sum(m_hints_size(ts, hints) for hints in multi_hints)
#
# def mmm_hints_size(
#     ts: BaseTransitionSystem, multi_hints: Iterable[Iterable[Iterable[Iterable[Hint]]]] | None
# ) -> int:
#     if multi_hints is None:
#         return 0
#     return sum(mm_hints_size(ts, hints) for hints in multi_hints)


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
            return rel.__class__(name, rel.mutable, ts.symbols[name])
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
    beta_src: TermLike[z3.BoolRef]
    m: int = 1  # number of elements added initially and in each transition
    init_hints: FiniteSCHints | None = None
    tr_hints: FiniteSCHints | None = None

    @cached_property
    def beta(self) -> TSFormula:
        return ts_term(self.beta_src)


def lemma_size(ts: BaseTransitionSystem, lemma: FiniteLemma | None) -> int:
    if lemma is None:
        return 0
    return expr_size(lemma.beta(ts))


@dataclass(frozen=True)
class FiniteSCByBeta(SoundnessCondition):
    spec: ParamSpec
    rank: "Rank"  # todo: differently?
    lemma: FiniteLemma

    def __post_init__(self) -> None:
        assert self.beta.spec == self.alpha.spec

    @cached_property
    def alpha(self) -> TSFormula:
        theta_min = self.rank.minimal
        return TSTerm(
            theta_min.spec,
            lambda ts, params: z3.Not(theta_min(ts, params)),
            f"alpha_<{theta_min.name}>",
        )

    @cached_property
    def beta(self) -> TSFormula:
        return self.lemma.beta

    @cached_property
    def alpha_implies_beta(self) -> TSFormula:
        return TSTerm(
            self.beta.spec,
            lambda ts, params: z3.Implies(
                self.alpha(ts, params), self.beta(ts, params)
            ),
            f"alpha->beta_<{self.rank}>",
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
                for param, sort in self.rank.spec.items()
                if param not in self.spec
            }
        )

        if not ts.check_and_print(
            f"init->at most {self.lemma.m} beta_<{self.rank}>",
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
                f"{name}->at most {self.lemma.m} beta added_<{self.rank}>",
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


class ClosedRank(ABC):
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


class Rank(ClosedRank, ABC):
    @property
    @abstractmethod
    def spec(self) -> ParamSpec: ...

    @property
    @abstractmethod
    def conserved(self) -> TSFormula: ...

    @property
    @abstractmethod
    def minimal(self) -> TSFormula: ...


@dataclass(frozen=True)
class BinRank(Rank):
    alpha_src: TermLike[z3.BoolRef]

    @cached_property
    def alpha(self) -> TSFormula:
        return ts_term(self.alpha_src)

    @property
    def spec(self) -> ParamSpec:
        return self.alpha.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Implies(
                z3.Not(self.alpha(ts, params)), z3.Not(self.alpha.next(ts, params))
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.Not(self.alpha(ts, params)),
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
                self.alpha(ts, params),
                z3.Not(self.alpha.next(ts, params)),
                self.conserved(ts, params),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + alpha
        return 1 + expr_size(self.alpha(ts))

    def __str__(self) -> str:
        return f"Bin({self.alpha.name})"


@dataclass(frozen=True)
class PosInOrderRank[T: Expr](Rank):
    term_src: TermLike[T]
    order_like: RelLike[T, T]

    @cached_property
    def term(self) -> TSTerm[T]:
        return ts_term(self.term_src)

    @cached_property
    def order(self) -> TSRel[T, T]:
        return ts_rel(self.order_like)

    @property
    def spec(self) -> ParamSpec:
        return self.term.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                strict_partial_immutable_order(self.order(ts)),
                z3.Or(
                    self.order(ts)(
                        self.term.next(ts, params),
                        self.term(ts, params),
                    ),
                    self.term.next(ts, params) == self.term(ts, params),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: minimal_in_order(self.term(ts, params), self.order(ts)),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return WellFoundedSC(self.order)

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                strict_partial_immutable_order(self.order(ts)),
                self.order(ts)(self.term.next(ts, params), self.term(ts, params)),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + order + term
        return 1 + 1 + expr_size(self.term(ts))

    def __str__(self) -> str:
        return f"Pos({self.term.name})"


@dataclass(frozen=True)
class LexRank(Rank):
    ranks: tuple[Rank, ...]

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
    ranks: tuple[Rank, ...]

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
    rank: Rank
    alpha_src: TermLike[z3.BoolRef]

    @cached_property
    def alpha(self) -> TSFormula:
        return ts_term(self.alpha_src)

    def __post_init__(self) -> None:
        assert (
            self.rank.spec == self.alpha.spec
        ), "Rank and condition must use the same params"

    @property
    def spec(self) -> ParamSpec:
        return self.rank.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                z3.Not(self.alpha.next(ts, params)),
                z3.And(
                    self.alpha(ts, params),
                    self.alpha.next(ts, params),
                    self.rank.conserved(ts, params),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: z3.Not(self.alpha(ts, params)),
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
                z3.And(self.alpha(ts, params), z3.Not(self.alpha.next(ts, params))),
                z3.And(
                    self.alpha(ts, params),
                    self.alpha.next(ts, params),
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
        return 1 + self.rank.expr_size(ts) + expr_size(self.alpha(ts))

    def __str__(self) -> str:
        return f"Cond({self.rank}, {self.alpha.name})"


@dataclass(frozen=True)
class DomainPointwiseRank(Rank):
    rank: Rank
    quant_spec: ParamSpec
    finite_lemma: FiniteLemma | None
    decreases_hints: DomainPointwiseHints | None = None

    @classmethod
    def close(cls, rank: Rank, finite_lemma: FiniteLemma | None) -> Rank:
        if not rank.spec:
            return rank
        return cls(rank, rank.spec, finite_lemma)

    def __post_init__(self) -> None:
        assert self.quant_spec, "Must quantify over some parameters"

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
            return FiniteSCByBeta(self.quant_spec, self.rank, self.finite_lemma)

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


type BinaryDomLexOrder[T: Expr] = tuple[RelLike[T, T], T]
type QuaternaryDomLexOrder[T1: Expr, T2: Expr] = tuple[RelLike[T1, T2, T1, T2], T1, T2]
type SenaryDomLexOrder[T1: Expr, T2: Expr, T3: Expr] = tuple[
    RelLike[T1, T2, T3, T1, T2, T3], T1, T2, T3
]
type OctonaryDomLexOrder[T1: Expr, T2: Expr, T3: Expr, T4: Expr] = tuple[
    RelLike[T1, T2, T3, T4, T1, T2, T3, T4], T1, T2, T3, T4
]

type DomLexOrder[T1: Expr, T2: Expr, T3: Expr, T4: Expr] = (
    BinaryDomLexOrder[T1]
    | QuaternaryDomLexOrder[T1, T2]
    | SenaryDomLexOrder[T1, T2, T3]
    | OctonaryDomLexOrder[T1, T2, T3, T4]
)


@dataclass(frozen=True)
class DomainLexRank[T1: Expr, T2: Expr, T3: Expr, T4: Expr](Rank):
    rank: Rank
    order_like: DomLexOrder[T1, T2, T3, T4] | TermLike[z3.BoolRef]
    finite_lemma: FiniteLemma | None = None
    conserved_hints: DomainLexConservedHints | None = None
    decreases_hints: DomainLexDecreasesHints | None = None

    @cached_property
    def order_as_ts_rel(
        self,
    ) -> (
        None
        | TSRel[T1, T1]
        | TSRel[T1, T2, T1, T2]
        | TSRel[T1, T2, T3, T1, T2, T3]
        | TSRel[T1, T2, T3, T4, T1, T2, T3, T4]
    ):
        if isinstance(self.order_like, tuple):
            return ts_rel(self.order_like[0])  # type ignore
        return None

    @cached_property
    def order_as_ts_formula(self) -> TSFormula | None:
        if isinstance(self.order_like, tuple):
            return None
        return ts_term(self.order_like)

    def order_pred(self, ts: BaseTransitionSystem) -> Predicate:
        if self.order_as_ts_rel is not None:
            return cast(Predicate, self.order_as_ts_rel(ts))

        formula = self.order_as_ts_formula
        assert formula is not None, f"Unsupported order like {self.order_like}"

        def predicate(*args: z3.ExprRef) -> z3.BoolRef:
            params = {name: arg for name, arg in zip(formula.spec.keys(), args)}
            return formula(ts, params)

        return predicate

    @cached_property
    def order_name(self) -> str:
        if self.order_as_ts_rel is not None:
            return self.order_as_ts_rel.name

        assert (
            self.order_as_ts_formula is not None
        ), f"Unsupported order like {self.order_like}"
        return self.order_as_ts_formula.name

    @cached_property
    def sorts(self) -> list[Sort]:
        if isinstance(self.order_like, tuple):
            return [
                cast(Sort, self.order_like[i].__class__)
                for i in range(1, len(self.order_like))
            ]

        assert (
            self.order_as_ts_formula is not None
        ), f"Unsupported order like {self.order_like}"
        name = self.order_as_ts_formula.name
        spec = self.order_as_ts_formula.spec
        spec_values = list(spec.values())
        assert len(spec_values) % 2 == 0, f"Non-even order formula {name}"
        half_len = len(spec_values) // 2

        sorts = []
        for i in range(half_len):
            sort1 = spec_values[i]
            sort2 = spec_values[i + half_len]
            assert sort1 is sort2, (
                f"Mismatched sorts in order formula {name}, "
                f"{sort1.ref()} at {i} but {sort2.ref()} at {i + half_len}"
            )

            sorts.append(sort1)

        return sorts

    @cached_property
    def sort_refs(self) -> list[z3.SortRef]:
        return [sort.ref() for sort in self.sorts]

    @cached_property
    def names(self) -> list[str]:
        if isinstance(self.order_like, tuple):
            return [str(self.order_like[i]) for i in range(1, len(self.order_like))]

        assert (
            self.order_as_ts_formula is not None
        ), f"Unsupported order like {self.order_like}"
        name = self.order_as_ts_formula.name
        spec = self.order_as_ts_formula.spec
        spec_keys = list(spec.keys())
        assert len(spec_keys) % 2 == 0, f"Non-even order formula {name}"
        half_len = len(spec_keys) // 2

        names = []
        for i in range(half_len):
            name1 = spec_keys[i]
            name2 = spec_keys[i + half_len]
            assert (
                name1.endswith("1") and name2.endswith("2") and name1[:-1] == name2[:-1]
            ), (
                f"Mismatched names in order formula {name}, "
                f"{name1} at {i} but {name2} at {i + half_len}"
            )

            names.append(name1[:-1])
        return names

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
        if self.finite_lemma is None:
            return FiniteSCBySort(self.quant_spec)
        else:
            # todo: add soundness condition of WF of order as well
            return FiniteSCByBeta(self.quant_spec, self.rank, self.finite_lemma)

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
    rank: Rank
    ys: ParamSpec
    k: int
    finite_lemma: FiniteLemma | None
    conserved_hints: DomainPermutedConservedHints | None = None
    decreases_hints: DomainPermutedDecreasesHints | None = None

    @cached_property
    def ys_left_right(self) -> list[tuple[dict[str, Expr], dict[str, Expr]]]:
        return [
            (self.ys.params("", f"-left-{i}"), self.ys.params("", f"-right-{i}"))
            for i in range(1, self.k + 1)
        ]

    @cached_property
    def ys_sigma(self) -> Params:
        ys_left_right = self.ys_left_right
        ys = self.ys.params()
        ys_sigma = self.ys.params()
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
                if param not in self.ys
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
                alpha(ts, (params) | self.ys.prime(self.ys_sigma)),
            ),
        )

    def exists_permutation_conserved(self) -> RawTSTerm[z3.BoolRef]:
        alpha = lambda ts, params: z3.ForAll(
            self.ys.consts(),
            self.rank.conserved(ts, params | self.ys.params()),
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
                self.ys.consts(),
                self.rank.conserved(
                    ts, params | self.ys.params() | self.ys.prime(self.ys_sigma)
                ),
            ),
            z3.Exists(
                self.ys.consts(),
                self.rank.decreases(
                    ts, params | self.ys.params() | self.ys.prime(self.ys_sigma)
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
                self.ys.consts(),
                self.rank.minimal(ts, params | self.ys.params()),
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return ConjunctionSC((self.rank.condition, self.finite_condition))

    @property
    def finite_condition(self) -> SoundnessCondition:
        if self.finite_lemma is None:
            return FiniteSCBySort(self.ys)
        else:
            return FiniteSCByBeta(self.ys, self.rank, self.finite_lemma)

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
            + len(self.ys)
            + 1
            + lemma_size(ts, self.finite_lemma)
            + hint_size(ts, self.conserved_hints)
            + hint_size(ts, self.decreases_hints)
        )

    def __str__(self) -> str:
        return f"DomPerm({self.rank}, {self.ys}, {self.k})"


@dataclass(frozen=True)
class TimerPosInOrderRank(Rank):
    term_like: TermLike[Time]

    @cached_property
    def term(self) -> TSTerm[Time]:
        return ts_term(self.term_like)

    @property
    def spec(self) -> ParamSpec:
        return self.term.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                timer_order(
                    self.term.next(ts, params),
                    self.term(ts, params),
                ),
                self.term.next(ts, params) == self.term(ts, params),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSTerm(
            self.spec,
            lambda ts, params: timer_zero(self.term(ts, params)),
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
                self.term.next(ts, params), self.term(ts, params)
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

    def expr_size(self, ts: BaseTransitionSystem) -> int:
        # rank + term
        return 1 + expr_size(self.term(ts))

    def __str__(self) -> str:
        return f"TimerPos({self.term.name})"


@dataclass(frozen=True)
class TimerRank(Rank):
    term_like: TermLike[Time]
    term_size: int
    alpha_like: TermLike[z3.BoolRef] | None = None
    finite_lemma: FiniteLemma | None = None

    @cached_property
    def term(self) -> TSTerm[Time]:
        return ts_term(self.term_like)

    @cached_property
    def alpha(self) -> TSFormula | None:
        if self.alpha_like is None:
            return None
        return ts_term(self.alpha_like)

    def __post_init__(self) -> None:
        assert (
            self.alpha is None or self.term.spec == self.alpha.spec
        ), f"Mismatch in params"

    @cached_property
    def rank(self) -> Rank:
        if self.alpha is None:
            return DomainPointwiseRank.close(
                TimerPosInOrderRank(self.term), self.finite_lemma
            )
        return DomainPointwiseRank.close(
            CondRank(TimerPosInOrderRank(self.term), self.alpha),
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
        if self.alpha is not None:
            alpha_size = expr_size(self.alpha(ts))
        return (
            1
            + self.term_size
            + alpha_size
            + lemma_size(ts, self.finite_lemma)
        )

    def __str__(self) -> str:
        if self.alpha is None:
            return f"TimerRank({self.term.name})"
        return f"TimerRank({self.term.name}, {self.alpha.name})"


def _hint_to_params(
    ts: BaseTransitionSystem, params: Params, hint: Hint, suffix: str = ""
) -> Params:
    return {f"{key}{suffix}": ts_term(term)(ts, params) for key, term in hint.items()}
