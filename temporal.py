"""
This module provides the basics for defining
temporal properties for transition systems.
"""

from abc import ABC, abstractmethod

import z3

from helpers import unpack_quantifier
from ts import TransitionSystem
from typed_z3 import true, false

_G = z3.Function("G", z3.BoolSort(), z3.BoolSort())
_F = z3.Function("F", z3.BoolSort(), z3.BoolSort())


def G(formula: z3.BoolRef) -> z3.BoolRef:
    """
    The globally (G, ☐) temporal operator.

    :param formula: The formula to apply the globally operator to.
    :return: A formula expressing that the formula holds globally (in all future states).
    """
    return _G(formula)  # type: ignore


def F(formula: z3.BoolRef) -> z3.BoolRef:
    """
    The eventually (F, ♢) temporal operator.

    :param formula: The formula to apply the eventually operator to.
    :return: A formula expressing that the formula holds eventually (in some future state).
    """
    return _F(formula)  # type: ignore


def is_G(formula: z3.ExprRef) -> bool:
    return z3.is_app(formula) and formula.decl().eq(_G)


def is_F(formula: z3.ExprRef) -> bool:
    return z3.is_app(formula) and formula.decl().eq(_F)


def contains_temporal(formula: z3.ExprRef) -> bool:
    if z3.is_quantifier(formula):
        variables, body = unpack_quantifier(formula)
        return contains_temporal(body)
    elif is_F(formula) or is_G(formula):
        return True
    else:
        return any(contains_temporal(child) for child in formula.children())


def nnf(formula: z3.ExprRef, negated: bool = False) -> z3.BoolRef:
    if z3.is_false(formula):
        if negated:
            return true
        else:
            return false
    elif z3.is_true(formula):
        if negated:
            return false
        else:
            return true
    elif z3.is_quantifier(formula):
        variables, body = unpack_quantifier(formula)
        nnf_body = nnf(body, negated)
        if (negated and formula.is_forall()) or (not negated and formula.is_exists()):
            return z3.Exists(variables, nnf_body)
        else:
            return z3.ForAll(variables, nnf_body)
    elif is_F(formula):
        (child,) = formula.children()
        nnf_body = nnf(child, negated)
        if negated:
            return G(nnf_body)
        else:
            return F(nnf_body)
    elif is_G(formula):
        (child,) = formula.children()
        nnf_body = nnf(child, negated)
        if negated:
            return F(nnf_body)
        else:
            return G(nnf_body)
    elif z3.is_bool(formula) and formula.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        if negated:
            return z3.Not(formula)
        else:
            return formula
    elif (z3.is_eq(formula) and not negated) or (z3.is_distinct(formula) and negated):
        left, right = formula.children()
        if z3.is_bool(left) and z3.is_bool(right):  # iff construction
            return nnf(
                z3.And(z3.Implies(left, right), z3.Implies(right, left)), negated
            )
        else:
            return left == right
    elif (z3.is_distinct(formula) and not negated) or (z3.is_eq(formula) and negated):
        left, right = formula.children()
        if z3.is_bool(left) and z3.is_bool(right):  # not-iff construction
            return nnf(
                z3.And(z3.Implies(left, right), z3.Implies(right, left)), not negated
            )
        else:
            return left != right
    elif z3.is_not(formula):
        (child,) = formula.children()
        return nnf(child, not negated)
    elif z3.is_and(formula) or z3.is_or(formula):
        children = [nnf(child, negated) for child in formula.children()]
        if (negated and z3.is_and(formula)) or (not negated and z3.is_or(formula)):
            return z3.Or(*children)
        else:
            return z3.And(*children)
    elif z3.is_implies(formula):
        antecedent, consequent = formula.children()
        assert z3.is_bool(antecedent) and z3.is_bool(
            consequent
        ), f"Bad implies {formula}"
        return nnf(z3.Or(z3.Not(antecedent), consequent), negated)

    assert False, f"Unexpected formula: {formula}"


class Prop[T: TransitionSystem](ABC):
    """
    Subclasses of this class represent a temporal property we wish to prove.
    They must implement the abstract method `prop`:
    ```python
    class Terminating(Prop[TerminationSystem]):
        def prop(self) -> BoolRef:
            T = Thread("T")
            return F(ForAll(T, Not(self.sys.on(T))))
    ```
    """

    sys: T
    """
    Field holding a reference to the transition system,
    so that the temporal property can have access to symbols from the signature.
    """

    @abstractmethod
    def prop(self) -> z3.BoolRef:
        """
        Return the temporal property to prove (non-negated).

        :return: Temporal property formula we wish to prove.
        """

    def __init__(self, sys: T) -> None:
        self.sys = sys
