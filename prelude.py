"""
The `prelude` module re-exports all necessary symbols
so one can simple write `from prelude import *`
and starting working with the library.
"""

from z3 import (
    BoolRef,
    ExprRef,
    And,
    Implies,
    Or,
    Not,
    ForAll,
    If,
    Exists,
)

from orders import (
    Order,
    RelOrder,
    FormulaOrder,
    LexOrder,
    PointwiseOrder,
)
from ranks import (
    Rank,
    BinRank,
    PosInOrderRank,
    CondRank,
    DomainPointwiseRank,
    DomainLexRank,
    LexRank,
    PointwiseRank,
    DomainPermutedRank,
    FiniteLemma,
    TSRel,
    SoundnessCondition,
)
from temporal import G, F, Prop
from proofs import (
    Proof,
    system_invariant,
    invariant,
    temporal_invariant,
    witness,
    temporal_witness,
    track,
)
from timers import (
    Time,
    TimeFun,
    timer_zero,
    timer_finite,
    timer_infinite,
    timer_nonzero,
    timer_decreasable,
)
from ts import (
    TransitionSystem,
    Immutable,
    axiom,
    init,
    transition,
    ParamSpec,
    TSTerm,
    TSFormula,
    TermLike,
    FormulaLike,
    BaseTransitionSystem,
)
from typed_z3 import (
    Expr,
    Rel,
    BiRel,
    Fun,
    Finite,
    WFRel,
    Bool,
    Int,
    Enum,
    false,
    true,
)

__all__ = [
    # typed Z3
    "Expr",
    "Rel",
    "BiRel",
    "Fun",
    "Finite",
    "WFRel",
    "Bool",
    "Int",
    "Enum",
    "false",
    "true",
    # Transition systems
    "BaseTransitionSystem",
    "TransitionSystem",
    "Immutable",
    "axiom",
    "init",
    "transition",
    "ParamSpec",
    "TSTerm",
    "TSFormula",
    "TermLike",
    "FormulaLike",
    # Temporal
    "G",
    "F",
    "Prop",
    # Timers
    "Time",
    "TimeFun",
    "timer_zero",
    "timer_finite",
    "timer_infinite",
    "timer_nonzero",
    "timer_decreasable",
    # Termination proof
    "Proof",
    "system_invariant",
    "temporal_invariant",
    "invariant",
    "witness",
    "temporal_witness",
    "track",
    # Order constructors
    "Order",
    "RelOrder",
    "FormulaOrder",
    "LexOrder",
    "PointwiseOrder",
    # Ranks
    "Rank",
    "BinRank",
    "PosInOrderRank",
    "CondRank",
    "DomainPointwiseRank",
    "DomainLexRank",
    "LexRank",
    "PointwiseRank",
    "DomainPermutedRank",
    "FiniteLemma",
    "TSRel",
    "SoundnessCondition",
    # re-exported Z3
    "BoolRef",
    "ExprRef",
    "And",
    "Implies",
    "Or",
    "Not",
    "ForAll",
    "If",
    "Exists",
    # ***
]
