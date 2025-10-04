import operator
from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import cast, Any, overload

import z3

from helpers import order_lt, minimal_in_order_lt, quantify, instantiate
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
type DomainPermutedConservedHint = tuple[LeftHint, RightHint]
type DomainPermutedConservedHints = Sequence[DomainPermutedConservedHint]
type DomainPermutedDecreasesHint = tuple[LeftHint, RightHint, Hint]
type DomainPermutedDecreasesHints = Sequence[DomainPermutedDecreasesHint]
type FiniteSCHint = Sequence[Hint]
type FiniteSCHints = Sequence[FiniteSCHint]

type _RawTSRel[T: Expr] = Callable[[BaseTransitionSystem], Rel[T, T]]


@dataclass(frozen=True)
class TSRel[T: Expr]:
    fun: _RawTSRel[T]

    def __call__(self, ts: BaseTransitionSystem) -> Rel[T, T]:
        return self.fun(ts)


@overload
def ts_rel[T: Expr](rel: TSRel[T]) -> TSRel[T]: ...


@overload
def ts_rel[T: Expr](rel: Rel[T, T]) -> TSRel[T]: ...


@overload
def ts_rel[TR: BaseTransitionSystem, T: Expr](
    rel: Callable[[TR], Rel[T, T]],
) -> TSRel[T]: ...


def ts_rel(rel: Any) -> TSRel[Any]:
    if isinstance(rel, TSRel):
        return rel
    elif isinstance(rel, Rel):
        return _ts_rel_from_rel(rel)
    else:
        return _ts_rel_from_callable(rel)


def _ts_rel_from_rel[T: Expr](rel: Rel[T, T]) -> TSRel[T]:
    name = str(rel)

    def fun(ts: BaseTransitionSystem) -> Rel[T, T]:
        if name in ts.symbols:
            return Rel(name, rel.mutable, ts.symbols[name])
        return rel

    return TSRel(fun)


def _ts_rel_from_callable[T: Expr](
    rel: Callable[[BaseTransitionSystem], Rel[T, T]],
) -> TSRel[T]:
    return TSRel(rel)


type RelLike[T: Expr] = TSRel[T] | Rel[T, T] | _RawTSRel[T] | Callable[
    [BaseTransitionSystem], Rel[T, T]
]


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
        return all(sort.finite() for sort in self.spec.values())


@dataclass(frozen=True)
class FiniteLemma:
    alpha_src: TermLike[z3.BoolRef]
    m: int = 1  # number of elements added initially and in each transition
    init_hints: FiniteSCHints | None = None
    tr_hints: FiniteSCHints | None = None

    @cached_property
    def alpha(self) -> TSFormula:
        return ts_term(self.alpha_src)


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
        return TSTerm(
            theta_min.spec,
            lambda ts, params: z3.Not(theta_min(ts, params)),
            f"beta_<{theta_min.name}>",
        )

    @cached_property
    def alpha(self) -> TSFormula:
        return self.lemma.alpha

    @cached_property
    def beta_implies_alpha(self) -> TSFormula:
        return TSTerm(
            self.alpha.spec,
            lambda ts, params: z3.Implies(
                self.beta(ts, params), self.alpha(ts, params)
            ),
            f"beta->alpha_<{self.rank}>",
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
            instantiation_params = reduce(
                operator.or_,
                (
                    _hint_to_params(ts, cast(Params, {}), hint, f"_{i}")
                    for i, hint in enumerate(hint_set)
                ),
            )
            instantiations = {name: var for name, var in instantiation_params.items()}
            return instantiate(formula, instantiations)

        return z3.Or(*(one_instantiation(hint_set) for hint_set in hints))

    def at_most_m_alpha_at_init(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        params = self.spec.consts()

        body = z3.ForAll(
            params,
            z3.Implies(
                self.alpha(ts),
                z3.Or(
                    *(
                        z3.And(*(param == y for param, y in zip(params, y_tuple)))
                        for y_tuple in ys
                    )
                ),
            ),
        )

        return self.exists_ys_with_hints(ts, body, self.lemma.init_hints)

    def at_most_m_alpha_added(self, ts: BaseTransitionSystem) -> z3.BoolRef:
        ys = [
            [sort(f"{param}_{i}") for param, sort in self.spec.items()]
            for i in range(self.lemma.m)
        ]

        params = self.spec.consts()

        body = z3.ForAll(
            params,
            z3.Implies(
                self.alpha(ts.next),
                z3.Or(
                    self.alpha(ts),
                    *(
                        z3.And(*(param == y for param, y in zip(params, y_tuple)))
                        for y_tuple in ys
                    ),
                ),
            ),
        )

        return self.exists_ys_with_hints(ts, body, self.lemma.tr_hints)

    def check(self, ts: BaseTransitionSystem, invariant: z3.BoolRef) -> bool:
        ts_formula = self.beta_implies_alpha
        if not ts.check_and_print(
            self.beta_implies_alpha.name,
            invariant,
            z3.Not(universal_closure(ts_formula, ts)),
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
            f"init->at most {self.lemma.m} alpha_<{self.rank}>",
            ts.init,
            z3.Not(
                quantify(
                    True,
                    z.consts(),  # todo: maybe flip to exists ys forall z
                    self.at_most_m_alpha_at_init(ts),
                )
            ),
        ):
            return False

        for name, trans in ts.transitions.items():
            if not ts.check_and_print(
                f"{name}->at most {self.lemma.m} alpha added_<{self.rank}>",
                invariant,
                trans,
                z3.Not(
                    quantify(
                        True,
                        z.consts(),  # todo: maybe flip to exists ys forall z
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
    def decreases(self) -> TSFormula: ...

    @property
    @abstractmethod
    def size(self) -> int: ...


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

    def __str__(self) -> str:
        return f"Bin({self.alpha.name})"


@dataclass(frozen=True)
class PosInOrderRank[T: Expr](Rank):
    term_src: TermLike[T]
    order_like: RelLike[T]

    @cached_property
    def term(self) -> TSTerm[T]:
        return ts_term(self.term_src)

    @cached_property
    def order(self) -> TSRel[T]:
        return ts_rel(self.order_like)

    @property
    def spec(self) -> ParamSpec:
        return self.term.spec

    @property
    def conserved(self) -> TSFormula:
        return TSTerm(
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
        return TSTerm(
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
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                order_lt(self.order(ts)),
                self.order(ts)(self.term.next(ts, params), self.term(ts, params)),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1

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
            return FiniteSCByAlpha(self.quant_spec, self.rank, self.finite_lemma)

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

        def hinted_exists(hint: Hint) -> z3.BoolRef:
            instantiation_params = _hint_to_params(ts, params, hint)
            instantiations = {name: var for name, var in instantiation_params.items()}
            return instantiate(formula, instantiations)

        return z3.Or(*(hinted_exists(hint) for hint in self.decreases_hints))

    def __str__(self) -> str:
        return f"DomPW({self.rank}, [{", ".join(self.spec.keys())}])"


@dataclass(frozen=True)
class DomainLexRank(Rank):
    rank: Rank
    order_like: RelLike[Any]
    param: tuple[str, Sort]
    finite_lemma: FiniteLemma | None = None

    @cached_property
    def order(self) -> TSRel[Any]:
        return ts_rel(self.order_like)

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
        return TSTerm(
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
                                self.rank.decreases(
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
            return FiniteSCByAlpha(self.quant_spec, self.rank, self.finite_lemma)

    @property
    def decreases(self) -> TSFormula:
        return TSTerm(
            self.spec.doubled(),
            lambda ts, params: z3.And(
                self.conserved(ts, params),
                z3.Exists(
                    self.quant_spec.consts(),
                    self.rank.decreases(
                        ts,
                        params | self.quant_spec.params() | self.quant_spec.params("'"),
                    ),
                ),
            ),
            f"{self}_<decreases>",
        )

    @property
    def size(self) -> int:
        return 1 + self.rank.size

    def __str__(self) -> str:
        return f"DomLex({self.rank}, {self.param[0]})"


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
                alpha(ts, params | self.ys.prime(self.ys_sigma)),
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
                left_params = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-left-{i + 1}")
                        for i, hint in enumerate(left_hint)
                    ),
                )
                right_params = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-right-{i + 1}")
                        for i, hint in enumerate(right_hint)
                    ),
                )
                instantiations = {
                    name: var for name, var in (left_params | right_params).items()
                }
                return instantiate(result, instantiations)

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
                left_params = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-left-{i + 1}")
                        for i, hint in enumerate(left_hint)
                    ),
                )
                right_params = reduce(
                    operator.or_,
                    (
                        _hint_to_params(ts, params, hint, f"-right-{i + 1}")
                        for i, hint in enumerate(right_hint)
                    ),
                )
                ys_params = _hint_to_params(ts, params, ys_hint)
                instantiations = {
                    name: var
                    for name, var in (left_params | right_params | ys_params).items()
                }
                return instantiate(result, instantiations)

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
            return FiniteSCByAlpha(self.ys, self.rank, self.finite_lemma)

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

    def __str__(self) -> str:
        return f"TimerPos({self.term.name})"


@dataclass(frozen=True)
class TimerRank(Rank):
    term_like: TermLike[Time]
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


def _hint_to_params(
    ts: BaseTransitionSystem, params: Params, hint: Hint, suffix: str = ""
) -> Params:
    return {f"{key}{suffix}": ts_term(term)(ts, params) for key, term in hint.items()}
