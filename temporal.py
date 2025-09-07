from abc import ABC, abstractmethod
from typing import ClassVar

import z3

from ts import TransitionSystem, BaseTransitionSystem

_G = z3.Function("G", z3.BoolSort(), z3.BoolSort())
_F = z3.Function("F", z3.BoolSort(), z3.BoolSort())


def G(formula: z3.BoolRef) -> z3.BoolRef:
    return _G(formula)  # type: ignore


def F(formula: z3.BoolRef) -> z3.BoolRef:
    return _F(formula)  # type: ignore


def is_G(formula: z3.BoolRef) -> bool:
    return z3.is_app(formula) and formula.decl().eq(_G)


def is_F(formula: z3.BoolRef) -> bool:
    return z3.is_app(formula) and formula.decl().eq(_F)


class Prop[T: TransitionSystem](ABC):
    sys: T

    @abstractmethod
    def negated_prop(self) -> z3.BoolRef: ...

    def __init__(self, sys: T) -> None:
        self.sys = sys
