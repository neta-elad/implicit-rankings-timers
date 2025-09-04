from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable
from functools import cached_property
from typing import ClassVar, cast, Any

import z3

from ranks import Rank
from timers import TimerTransitionSystem, create_timers, TimeFun
from ts import (
    BaseTransitionSystem,
    IntersectionTransitionSystem,
    ts_formula,
    TSFormula,
    TransitionSystem,
)


class Proof[T: TransitionSystem](
    IntersectionTransitionSystem[T, TimerTransitionSystem], ABC
):
    ts: ClassVar[type[BaseTransitionSystem]]
    _cache: ClassVar[dict[type[BaseTransitionSystem], type]] = {}

    def __init__(
        self, left: T | None = None, right: TimerTransitionSystem | None = None
    ) -> None:
        if left is None:
            left = cast(T, self.__class__.ts())
        object.__setattr__(self, "left", left)

        if right is None:
            right = create_timers(left.negated_prop(), left)
        object.__setattr__(self, "right", right)

    @classmethod
    def __class_getitem__(cls, item: type[BaseTransitionSystem]) -> "type[Proof[T]]":
        if item not in cls._cache:
            cls._cache[item] = type("tmp", (cls,), {"ts": item})

        return cls._cache[item]

    @abstractmethod
    def rank(self) -> Rank: ...

    @cached_property
    def sys(self) -> T:
        return self.left

    @cached_property
    def timers(self) -> TimerTransitionSystem:
        return self.right

    def t(self, name: str) -> TimeFun:
        return self.right.t(name)

    @cached_property
    def invariants(self) -> dict[str, z3.BoolRef]:
        return {
            name: method.forall(self)
            for name, method in _get_methods(self, _PROOF_INVARIANT)
        }

    @cached_property
    def invariant(self) -> z3.BoolRef:
        return z3.And(*self.invariants.values())

    def check(self) -> bool:
        if not self._check_inv():
            print("fail: inv")
            return False

        if not self._check_conserved():
            print("fail: conserved")
            return False

        if not self._check_decrease():
            print("fail: decrease")
            return False

        if not self._check_soundness():
            print(f"fail: soundness")
            return False

        print(f"All passed!")
        return True

    def _check_inv(self) -> bool:
        return self.check_inductiveness(lambda this: this.invariant, "inv")

    def _check_conserved(self) -> bool:
        results = []
        for name, trans in self.transitions.items():
            results.append(
                self.check_and_print(
                    f"conserved in {name}",
                    self.invariant,
                    trans,
                    z3.Not(self.rank().conserved(self)),
                    with_next=True,
                )
            )
        return all(results)

    def _check_decrease(self) -> bool:
        results = []
        for name, trans in self.transitions.items():
            results.append(
                self.check_and_print(
                    f"decreases in {name}",
                    self.invariant,
                    trans,
                    z3.Not(self.rank().decreased(self)),
                    with_next=True,
                )
            )
        return all(results)

    def _check_soundness(self) -> bool:
        if self.rank().condition.check(self, self.invariant):
            print("Checking soundness: passed")
            return True
        else:
            print("Checking soundness: failed")
            return False


type TypedProofFormula[T: Proof[Any], *Ts] = Callable[[T, *Ts], z3.BoolRef]


def invariant[T: Proof[Any], *Ts](
    fun: TypedProofFormula[T, *Ts],
) -> TypedProofFormula[T, *Ts]:
    setattr(fun, _PROOF_METADATA, _PROOF_INVARIANT)
    return fun


_PROOF_METADATA = "__proof_metadata__"
_PROOF_INVARIANT = object()
_PROOF_SPECIALS = {"invariant", "invariants"}


def _get_methods(ts: Proof[Any], marker: object) -> Iterable[tuple[str, TSFormula]]:
    for name in dir(ts.__class__):
        if name in _PROOF_SPECIALS:
            continue
        attr: TypedProofFormula[Any] = getattr(ts.__class__, name)
        if (
            callable(attr)
            and hasattr(attr, _PROOF_METADATA)
            and getattr(attr, _PROOF_METADATA) is marker
        ):
            yield name, ts_formula(attr)
