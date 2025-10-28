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
    RelOrder,
    FormulaOrder,
    LexOrder,
    PointwiseOrder,
)
from ranks import (
    ClosedRank,
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
from termination import (
    Proof,
    system_invariant,
    invariant,
    temporal_invariant,
    witness,
    temporal_witness,
    track,
)
from timers import (
    timer_zero,
    timer_finite,
    Time,
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
    ts_term,
    TSFormula,
    BaseTransitionSystem,
)
from typed_z3 import (
    Expr,
    Rel,
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
    "ts_term",
    "TSFormula",
    # Temporal
    "G",
    "F",
    "Prop",
    # Timers
    "timer_zero",
    "timer_finite",
    "Time",
    "timer_infinite",
    "timer_nonzero",
    "timer_decreasable",
    # Termination proof
    "Proof",
    "system_invariant",
    "invariant",
    "temporal_invariant",
    "witness",
    "temporal_witness",
    "track",
    # Order constructors
    "RelOrder",
    "FormulaOrder",
    "LexOrder",
    "PointwiseOrder",
    # Ranks
    "ClosedRank",
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
