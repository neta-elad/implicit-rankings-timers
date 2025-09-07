from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from functools import cached_property
from typing import cast, Any

import z3

from helpers import order_lt, minimal_in_order_lt, quantify
from timers import timer_order, Time
from ts import (
    BaseTransitionSystem,
    ParamSpec,
    TSFormula,
    TSTerm,
    BoundTypedFormula,
    unbind,
    ts_formula,
    BoundTypedTerm,
    ts_term,
    ErasedBoundTypedFormula,
)
from typed_z3 import Expr, Rel, Sort

type _RawTSRel[T: Expr] = Callable[[BaseTransitionSystem], Rel[T, T]]


@dataclass(frozen=True)
class TSRel[T: Expr]:
    fun: _RawTSRel[T]

    def __call__(self, ts: BaseTransitionSystem) -> Rel[T, T]:
        return self.fun(ts)


class SoundnessCondition(ABC):
    @abstractmethod
    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool: ...


class TrueSC(SoundnessCondition):
    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        return True


@dataclass(frozen=True)
class WellFoundedSC(SoundnessCondition):
    order: TSRel[Any]

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        rel = self.order(ts)
        return rel.well_founded()


@dataclass(frozen=True)
class ConjunctionSC(SoundnessCondition):
    conditions: tuple[SoundnessCondition, ...]

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        return all(sc.check(ts, invariant) for sc in self.conditions)


@dataclass(frozen=True)
class FiniteSCBySort(SoundnessCondition):
    spec: ParamSpec

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        return all(sort.finite() for sort in self.spec.values())


@dataclass(frozen=True)
class FiniteLemma:
    alpha_src: ErasedBoundTypedFormula
    m: int = 1  # number of elements added initially and in each transition

    @cached_property
    def alpha(self) -> TSFormula:
        return ts_formula(unbind(self.alpha_src))


@dataclass(frozen=True)
class FiniteSCByAlpha(SoundnessCondition):
    spec: ParamSpec
    rank: "Rank"  # todo: differently?
    lemma: FiniteLemma

    def __post_init__(self) -> None:
        assert self.alpha.spec == self.beta.spec

    @cached_property
    def beta(self) -> TSFormula:
        theta_min = self.rank.minimal
        return TSFormula(
            theta_min.spec,
            lambda ts, params: z3.Not(theta_min(ts, params)),
            f"beta_<{theta_min.name}>",
        )

    @cached_property
    def alpha(self) -> TSFormula:
        return self.lemma.alpha

    @cached_property
    def beta_implies_alpha(self) -> TSFormula:
        return TSFormula(
            self.alpha.spec,
            lambda ts, params: z3.Implies(
                self.beta(ts, params), self.alpha(ts, params)
            ),
            f"beta->alpha_<{self.rank}>",
        )

    def at_most_m_alpha_at_init(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        params = self.spec.params()

        return z3.Exists(
            [y for y_tuple in ys for y in y_tuple],
            z3.ForAll(
                list(params.values()),
                z3.Implies(
                    self.alpha(ts),
                    z3.Or(
                        *(
                            z3.And(
                                *(
                                    param == y
                                    for param, y in zip(params.values(), y_tuple)
                                )
                            )
                            for y_tuple in ys
                        )
                    ),
                ),
            ),
        )

    def at_most_m_alpha_added(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        params = self.spec.params()

        return z3.Exists(
            [y for y_tuple in ys for y in y_tuple],
            z3.ForAll(
                list(params.values()),
                z3.Implies(
                    self.alpha(ts.next),
                    z3.Or(
                        self.alpha(ts),
                        *(
                            z3.And(
                                *(
                                    param == y
                                    for param, y in zip(params.values(), y_tuple)
                                )
                            )
                            for y_tuple in ys
                        ),
                    ),
                ),
            ),
        )

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        if not ts.check_and_print(
            self.beta_implies_alpha.name,
            invariant,
            z3.Not(self.beta_implies_alpha.forall(ts)),
        ):
            return False
        self.at_most_m_alpha_at_init(ts)
        z = ParamSpec(
            {
                param: sort
                for param, sort in self.rank.spec.items()
                if param not in self.spec
            }
        )

        if not ts.check_and_print(
            f"init->at most m alpha_<{self.rank}>",
            ts.init,
            z3.Not(
                quantify(
                    True,
                    z.params().values(),  # todo: maybe flip to exists ys forall z
                    self.at_most_m_alpha_at_init(ts),
                )
            ),
        ):
            return False

        for name, trans in ts.transitions.items():
            if not ts.check_and_print(
                f"{name}->at most m alpha added_<{self.rank}>",
                invariant,
                trans,
                z3.Not(
                    quantify(
                        True,
                        z.params().values(),  # todo: maybe flip to exists ys forall z
                        self.at_most_m_alpha_added(ts),
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
    def decreased(self) -> TSFormula: ...


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
    alpha_src: ErasedBoundTypedFormula

    @cached_property
    def alpha(self) -> TSFormula:
        return ts_formula(unbind(self.alpha_src))

    @property
    def spec(self) -> ParamSpec:
        return self.alpha.spec

    @property
    def conserved(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.Implies(
                z3.Not(self.alpha(ts, params)), z3.Not(self.alpha.next(ts, params))
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSFormula(
            self.spec,
            lambda ts, params: z3.Not(self.alpha(ts, params)),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return TrueSC()

    @property
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.alpha(ts, params),
                z3.Not(self.alpha.next(ts, params)),
                self.conserved(ts, params),
            ),
            f"{self}_<decreased>",
        )

    def __str__(self) -> str:
        return f"Bin({self.alpha.name})"


@dataclass(frozen=True)
class PosInOrderRank[T: Expr](Rank):
    order: TSRel[T]
    term_src: BoundTypedTerm[Any, T] | TSTerm[T]

    @cached_property
    def term(self) -> TSTerm[T]:
        if isinstance(self.term_src, TSTerm):
            return self.term_src
        return ts_term(unbind(self.term_src))

    @property
    def spec(self) -> ParamSpec:
        return self.term.spec

    @property
    def conserved(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                order_lt(self.order(ts)),
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
        return TSFormula(
            self.spec,
            lambda ts, params: minimal_in_order_lt(
                self.term(ts, params), self.order(ts)
            ),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return WellFoundedSC(self.order)

    @property
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                order_lt(self.order(ts)),
                self.order(ts)(self.term.next(ts, params), self.term(ts, params)),
            ),
            f"{self}_<decreased>",
        )

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
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                self.decreased(ts, params),
                z3.And(*(rank.conserved(ts, params) for rank in self.ranks)),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSFormula(
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
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                *(
                    z3.And(
                        rank.decreased(ts, params),
                        *(
                            rank_.conserved(ts, params)
                            for j, rank_ in enumerate(self.ranks)
                            if j < i
                        ),
                    )
                    for i, rank in enumerate(self.ranks)
                )
            ),
            f"{self}_<decreased>",
        )

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
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                *(rank.conserved(ts, params) for rank in self.ranks)
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSFormula(
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
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                z3.Or(*(rank.decreased(ts, params) for rank in self.ranks)),
                z3.And(*(rank.conserved(ts, params) for rank in self.ranks)),
            ),
            f"{self}_<decreased>",
        )

    def __str__(self) -> str:
        return f"PW({", ".join(map(str, self.ranks))})"


@dataclass(frozen=True)
class CondRank(Rank):
    rank: Rank
    alpha_src: ErasedBoundTypedFormula

    @cached_property
    def alpha(self) -> TSFormula:
        return ts_formula(unbind(self.alpha_src))

    def __post_init__(self) -> None:
        assert (
            self.rank.spec == self.alpha.spec
        ), "Rank and condition must use the same params"

    @property
    def spec(self) -> ParamSpec:
        return self.rank.spec

    @property
    def conserved(self) -> TSFormula:
        return TSFormula(
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
        return TSFormula(
            self.spec,
            lambda ts, params: z3.Not(self.alpha(ts, params)),
            f"{self}_<minimal>",
        )

    @property
    def condition(self) -> SoundnessCondition:
        return self.rank.condition

    @property
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.Or(
                z3.And(self.alpha(ts, params), z3.Not(self.alpha.next(ts, params))),
                z3.And(
                    self.alpha(ts, params),
                    self.alpha.next(ts, params),
                    self.rank.decreased(ts, params),
                ),
            ),
            f"{self}_<decreased>",
        )

    def __str__(self) -> str:
        return f"Cond({self.rank}, {self.alpha.name})"


@dataclass(frozen=True)
class DomainPointwiseRank(Rank):
    rank: Rank
    quant_spec: ParamSpec
    finite_lemma: FiniteLemma | None

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
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.ForAll(
                list(self.quant_spec.params().values()),
                self.rank.conserved(
                    ts,
                    params | self.quant_spec.params() | self.quant_spec.params("'"),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSFormula(
            self.spec,
            lambda ts, params: z3.ForAll(
                list(self.quant_spec.params().values()),
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
            return FiniteSCByAlpha(self.quant_spec, self.rank, self.finite_lemma)

    @property
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.conserved(ts, params),
                z3.Exists(
                    list(self.quant_spec.params().values()),
                    self.rank.decreased(
                        ts,
                        params | self.quant_spec.params() | self.quant_spec.params("'"),
                    ),
                ),
            ),
            f"{self}_<decreased>",
        )

    def __str__(self) -> str:
        return f"DomPW({self.rank}, [{", ".join(self.spec.keys())}])"


@dataclass(frozen=True)
class DomainLexRank(Rank):
    rank: Rank
    order: TSRel[Any]
    param: tuple[str, Sort]
    finite_lemma: FiniteLemma | None = None

    @property
    def quant_spec(self) -> ParamSpec:
        return ParamSpec({self.param[0]: self.param[1]})

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
        y0 = self.param[1]("y0")
        y = self.param[1]("y")
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                order_lt(self.order(ts)),
                z3.ForAll(
                    y,
                    z3.Or(
                        self.rank.conserved(
                            ts,
                            params | {self.param[0]: y} | {self.param[0] + "'": y},
                        ),
                        z3.Exists(
                            y0,
                            z3.And(
                                self.order(ts)(y0, y),
                                self.rank.decreased(
                                    ts,
                                    params
                                    | {self.param[0]: y0}
                                    | {self.param[0] + "'": y0},
                                ),
                            ),
                        ),
                    ),
                ),
            ),
            f"{self}_<conserved>",
        )

    @property
    def minimal(self) -> TSFormula:
        return TSFormula(
            self.spec,
            lambda ts, params: z3.ForAll(
                list(self.quant_spec.params().values()),
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
            return FiniteSCByAlpha(self.quant_spec, self.rank, self.finite_lemma)

    @property
    def decreased(self) -> TSFormula:
        return TSFormula(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.conserved(ts, params),
                z3.Exists(
                    list(self.quant_spec.params().values()),
                    self.rank.decreased(
                        ts,
                        params | self.quant_spec.params() | self.quant_spec.params("'"),
                    ),
                ),
            ),
            f"{self}_<decreased>",
        )

    def __str__(self) -> str:
        return f"DomLex({self.rank}, {self.param[0]})"


def ts_rel[T: BaseTransitionSystem, R: Expr](rel: Callable[[T], Rel[R, R]]) -> TSRel[R]:
    return TSRel[R](cast(_RawTSRel[R], rel))


def timer_rank[*Ts](
    finite_lemma: FiniteLemma | None,
    term: BoundTypedTerm[*Ts, Time] | TSTerm[Time],
    alpha: BoundTypedFormula[*Ts] | None = None,
) -> Rank:
    if alpha is None:
        return DomainPointwiseRank.close(
            PosInOrderRank(ts_rel(lambda ts: timer_order()), term), finite_lemma
        )
    # assert term.spec == alpha.spec, f"Mismatch in params"
    return DomainPointwiseRank.close(
        CondRank(PosInOrderRank(ts_rel(lambda ts: timer_order()), term), alpha),
        finite_lemma,
    )
