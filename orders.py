import operator
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import cast

import z3

from ts import TSFormula, BaseTransitionSystem, TSTerm, ParamSpec, Params
from typed_z3 import Expr, Rel, Sort


class Order(ABC):
    @property
    @abstractmethod
    def formula(self) -> TSFormula: ...

    @abstractmethod
    def check_well_founded(self, ts: BaseTransitionSystem) -> bool: ...


type BinaryRel[T] = Rel[T, T]


@dataclass(frozen=True)
class RelOrder[T: Expr](Order):
    rel: BinaryRel[T]
    param: str

    @cached_property
    def sort(self) -> Sort:
        return self.rel.signature[0]

    @property
    def formula(self) -> TSFormula:
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

    def check_well_founded(self, ts: BaseTransitionSystem) -> bool:
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
    src_formula: TSFormula

    @cached_property
    def formula(self) -> TSFormula:
        return self.src_formula

    def check_well_founded(self, ts: BaseTransitionSystem) -> bool:
        print(f"Checking {self} well-founded: ", end="", flush=True)
        for sort in self.formula.spec.values():
            if not sort.finite():
                print(f"{sort.ref()} not finite")
                return False
        print(f"all sorts finite")
        return True

    def __str__(self) -> str:
        return self.formula.name


@dataclass(frozen=True)
class LexOrder(Order):
    orders: dict[str, Order]

    def __init__(self, **kwargs: BinaryRel[Expr]) -> None:
        object.__setattr__(
            self, "orders", {name: RelOrder(rel, name) for name, rel in kwargs.items()}
        )

    @property
    def formula(self) -> TSFormula:
        spec = reduce(
            operator.or_, [order.formula.spec for order in self.orders.values()]
        )

        def actual_formula(ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
            clauses = []
            guard = z3.BoolVal(True)
            for name, order in self.orders.items():
                clauses.append(z3.And(guard, order.formula(ts, params)))
                guard = z3.And(guard, params[name + "1"] == params[name + "2"])

            return z3.Or(*clauses)

        return TSTerm(spec, actual_formula, str(self))

    def check_well_founded(self, ts: BaseTransitionSystem) -> bool:
        return all(order.check_well_founded(ts) for order in self.orders.values())

    def __str__(self) -> str:
        return f"LexOrder({", ".join(f"{name}={order}" for name, order in self.orders.items())})"


@dataclass(frozen=True)
class PointwiseOrder(Order):
    orders: dict[str, Order]

    def __init__(self, **kwargs: BinaryRel[Expr]) -> None:
        object.__setattr__(
            self, "orders", {name: RelOrder(rel, name) for name, rel in kwargs.items()}
        )

    @property
    def formula(self) -> TSFormula:
        spec = reduce(
            operator.or_, [order.formula.spec for order in self.orders.values()]
        )

        def actual_formula(ts: BaseTransitionSystem, params: Params) -> z3.BoolRef:
            clauses = []
            guards = []
            for name, order in self.orders.items():
                clauses.append(order.formula(ts, params))
                guards.append(
                    z3.Or(
                        order.formula(ts, params),
                        params[name + "1"] == params[name + "2"],
                    )
                )

            return z3.And(*guards, z3.Or(*clauses))

        return TSTerm(spec, actual_formula, str(self))

    def check_well_founded(self, ts: BaseTransitionSystem) -> bool:
        return all(order.check_well_founded(ts) for order in self.orders.values())

    def __str__(self) -> str:
        return f"PointwiseOrder({", ".join(f"{name}={order}" for name, order in self.orders.items())})"
