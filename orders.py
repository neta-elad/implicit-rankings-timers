"""
This module provides constructors to build verifiably
well-founded orders,
used in `ranks.DomainLexRank`.
"""

import operator
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import cast

import z3

from ts import (
    TSFormula,
    BaseTransitionSystem,
    TSTerm,
    ParamSpec,
    Params,
    ts_term,
    FormulaLike,
)
from typed_z3 import Expr, Sort, BiRel

__all__ = [
    "Order",
    "OrderLike",
    "RelOrder",
    "FormulaOrder",
    "LexOrder",
    "PointwiseOrder",
]


class Order(ABC):
    """Abstract base class for order constructors."""

    @property
    @abstractmethod
    def ts_formula(self) -> TSFormula: ...

    @abstractmethod
    def check_well_founded(self) -> bool: ...


type OrderLike = Order | FormulaLike
"""
Any value that can be converted to `Order`:
an already constructed `Order` or a formula-like
that would be converted to a `FormulaOrder`.
"""


@dataclass(frozen=True)
class RelOrder[T: Expr](Order):
    """
    Order constructed from a binary relation.
    Considered well-founded
    when it is declared so (see `typed_z3.WFRel`)
    or when its input sort is declared finite (see `typed_z3.Finite`).

    Constructed by giving a binary relation and a parameter name:
    ```python
    class Thread(Expr): ...
    lt: WFRel[Thread]

    rel_order = RelOrder(lt, "a")
    ```
    """

    rel: BiRel[T]
    """The binary relation."""

    param: str
    """Name of parameter."""

    @cached_property
    def sort(self) -> Sort:
        return self.rel.signature[0]

    @property
    def ts_formula(self) -> TSFormula:
        name = self.param
        name1 = name + "1"
        name2 = name + "2"
        return TSTerm(
            ParamSpec({name1: self.sort, name2: self.sort}),
            lambda ts, params: cast(
                z3.BoolRef, ts[self.rel.name](params[name1], params[name2])
            ),
            self.rel.name,
        )

    def check_well_founded(self) -> bool:
        print(f"Checking {self} well-founded: ", end="", flush=True)
        if self.sort.finite():
            print(f"{self.sort.ref()} finite")
            return True
        if self.rel.well_founded():
            print(f"{self} declared well-founded")
            return True
        print(f"{self.sort.ref()} not finite and {self} not well-founded")
        return False

    def __str__(self) -> str:
        return self.rel.name


@dataclass(frozen=True)
class FormulaOrder(Order):
    """
    Order constructed from a `ts.TSFormula`.
    Considered well-founded
    when all its input sorts are declared finite (see `typed_z3.Finite`).

    Constructed from any formula-like value:
    ```python
    class Thread(Finite): ...
    class System(TransitionSystem):
        gt: BiRel[Thread]

    def lt_formula(ts: System, a1: Thread, a2: Thread, b1: Thread, b2: Thread) -> BoolRef:
        return Or(ts.gt(a2, a1), And(a1 == a2, ts.gt(b2, b1))

    formula_order = FormulaOrder(lt_formula)
    ```

    Note that the parameter names for the formula must be of the form
    `<name>1 <name>2 <other_name>1 <other_name>2`.
    Order does not matter, but every parameter must end in `1` or `2`,
    and must have a matching parameter ending in `2` or `1` (respectively).
    """

    formula: FormulaLike
    """Source formula that can be converted to a `ts.TSFormula`."""

    @cached_property
    def ts_formula(self) -> TSFormula:
        return ts_term(self.formula)

    def check_well_founded(self) -> bool:
        print(f"Checking {self} well-founded: ", end="", flush=True)
        for sort in self.ts_formula.spec.values():
            if not sort.finite():
                print(f"{sort.ref()} not finite")
                return False
        print(f"all sorts finite")
        return True

    def __str__(self) -> str:
        return self.ts_formula.name


@dataclass(frozen=True)
class LexOrder(Order):
    """
    Order constructed from a lexicographic order over multiple binary relations.
    Considered well-founded
    when all of its underlying orders are well-founded.

    Constructed by mapping parameters to binary relations:
    ```python
    class Thread(Finite): ...
    class Ticket(Expr): ...

    thread_order: BiRel[Thread]
    ticket_order: WFRel[Ticket]
    lex_order = LexOrder(a=thread_order, b=ticket_order)
    ```
    """

    orders: dict[str, Order]

    def __init__(self, **kwargs: BiRel[Expr]) -> None:
        object.__setattr__(
            self, "orders", {name: RelOrder(rel, name) for name, rel in kwargs.items()}
        )

    @property
    def ts_formula(self) -> TSFormula:
        spec = reduce(
            operator.or_, [order.ts_formula.spec for order in self.orders.values()]
        )

        def actual_formula(ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
            clauses = []
            guard = z3.BoolVal(True)
            for name, order in self.orders.items():
                clauses.append(z3.And(guard, order.ts_formula(ts, params)))
                guard = z3.And(guard, params[name + "1"] == params[name + "2"])

            return z3.Or(*clauses)

        return TSTerm(spec, actual_formula, str(self))

    def check_well_founded(self) -> bool:
        return all(order.check_well_founded() for order in self.orders.values())

    def __str__(self) -> str:
        return f"LexOrder({", ".join(f"{name}={order}" for name, order in self.orders.items())})"


@dataclass(frozen=True)
class PointwiseOrder(Order):
    """
    Order constructed from a pointwise order over multiple binary relations.
    Considered well-founded
    when all of its underlying orders are well-founded.

    Constructed by mapping parameters to binary relations:
    ```python
    class Thread(Finite): ...
    class Ticket(Expr): ...

    thread_order: BiRel[Thread]
    ticket_order: WFRel[Ticket]
    pw_order = PointwiseOrder(a=thread_order, b=ticket_order)
    ```
    """

    orders: dict[str, Order]

    def __init__(self, **kwargs: BiRel[Expr]) -> None:
        object.__setattr__(
            self, "orders", {name: RelOrder(rel, name) for name, rel in kwargs.items()}
        )

    @property
    def ts_formula(self) -> TSFormula:
        spec = reduce(
            operator.or_, [order.ts_formula.spec for order in self.orders.values()]
        )

        def actual_formula(ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
            clauses = []
            guards = []
            for name, order in self.orders.items():
                clauses.append(order.ts_formula(ts, params))
                guards.append(
                    z3.Or(
                        order.ts_formula(ts, params),
                        params[name + "1"] == params[name + "2"],
                    )
                )

            return z3.And(*guards, z3.Or(*clauses))

        return TSTerm(spec, actual_formula, str(self))

    def check_well_founded(self) -> bool:
        return all(order.check_well_founded() for order in self.orders.values())

    def __str__(self) -> str:
        return f"PointwiseOrder({", ".join(f"{name}={order}" for name, order in self.orders.items())})"
