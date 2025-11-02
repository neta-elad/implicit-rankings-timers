"""
This module provides the interface to talk about timers.
The **Implicit Ranking Timers** library supports two modes of timers:
- Uninterpreted (`unint`, `u`):
    `Time` is an uninterpreted sort with axioms that make it behave
    as expected.
- Interpreted (`int`, `i`):
    `Time` is expressed with interpreted integers, with infinity represented as -1.

Time expressions (of sort `Time`) are never created directly,
but through temporal formulas
(see `proofs.Proof.t`).

When running an example the mode can be configured
by setting the environment variable `TIMERS`:
```sh
make examples/ticket.py TIMERS=<mode>
```
where `<mode>` is either `unint` or `int`.
The default mode is `int` (interpreted integers).
"""

import difflib
import operator
import textwrap
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property, reduce
from os import getenv
from typing import Any, cast, Self, Protocol, TYPE_CHECKING

import z3

from helpers import unpack_quantifier, find_substitution, quantify
from temporal import is_G, is_F, nnf
from ts import BaseTransitionSystem, ParamSpec, Params
from typed_z3 import Rel, Fun, Sort, Expr, Int, Bool, Signature

__all__ = [
    "Time",
    "TimeFun",
    "timer_zero",
    "timer_finite",
    "timer_infinite",
    "timer_nonzero",
    "timer_decreasable",
]

__pdoc__ = {}

_DEFAULT_TIMERS_MODE = "int"
_UNINTERPRETED_TIMERS = "uninterpreted".startswith(
    getenv("TIMERS", _DEFAULT_TIMERS_MODE).lower()
)


class Time(Expr):
    """
    Time sort.
    Should not be instantiated directly.
    """


if not TYPE_CHECKING:
    if _UNINTERPRETED_TIMERS:  # uninterpreted time

        class _Time(Expr): ...

        _zero = _Time("zero")
        _inf = _Time("inf")
    else:  # integer time
        _Time = Int
        _zero = z3.IntVal(0)
        _inf = z3.IntVal(-1)
else:
    type _Time = Time
    _zero: Time
    _inf: Time

__pdoc__["Time"] = True


class TimeFun(Protocol):
    """
    Variadic callable returning a `Time` expression.
    A function with signature:
    ```python
    def time_fun(*args: z3.ExprRef) -> Time: ...
    ```

    The usual way of producing a `TimeFun` is by calling `proofs.Proof.t`.
    """

    def __call__(self, *args: z3.ExprRef) -> Time: ...


def timer_order_axioms() -> z3.BoolRef:
    if _UNINTERPRETED_TIMERS:
        x = _Time("x")  # type: ignore
        y = _Time("y")  # type: ignore
        z = _Time("z")  # type: ignore
        return z3.And(
            z3.ForAll(
                [x, y, z],
                z3.Implies(
                    z3.And(timer_order(x, y), timer_order(y, z)), timer_order(x, z)
                ),
            ),
            z3.ForAll(x, z3.Not(timer_order(x, x))),
            z3.ForAll(x, z3.Or(x == _zero, timer_order(_zero, x))),
            z3.ForAll(x, z3.Or(x == _inf, timer_order(x, _inf))),
            _zero != _inf,
        )

    return z3.BoolVal(True)


_timer_order = Rel[_Time, _Time]("timer_order")


def timer_order(t1: Time, t2: Time) -> z3.BoolRef:
    if _UNINTERPRETED_TIMERS:
        return _timer_order(t1, t2)

    return z3.Or(
        z3.And(timer_finite(t1), timer_infinite(t2)),
        z3.And(timer_finite(t1), timer_finite(t2), t1 < t2),  # type: ignore
    )


def timer_valid(timer_expr: Time) -> z3.BoolRef:
    if _UNINTERPRETED_TIMERS:
        return z3.BoolVal(True)
    return timer_expr >= _inf  # type: ignore


def timer_zero(timer_expr: Time) -> z3.BoolRef:
    """
    Return a formula expressing that the timer expression is zero.

    :param timer_expr: The timer expression to check.
    :return: Formula expressing that the timer is zero.
    """
    return timer_expr == _zero


def timer_nonzero(timer_expr: Time) -> z3.BoolRef:
    """
    Return a formula expressing that the timer expression is non-zero.

    :param timer_expr: The timer expression to check.
    :return: Formula expressing that the timer is non-zero.
    """
    return timer_expr != _zero


def timer_finite(timer_expr: Time) -> z3.BoolRef:
    """
    Return a formula expressing that the timer expression is finite.

    :param timer_expr: The timer expression to check.
    :return: Formula expressing that the timer is finite.
    """
    if _UNINTERPRETED_TIMERS:
        return timer_expr != _inf

    return timer_expr >= 0  # type: ignore


def timer_infinite(timer_expr: Time) -> z3.BoolRef:
    """
    Return a formula expressing that the timer expression is infinite.

    :param timer_expr: The timer expression to check.
    :return: Formula expressing that the timer is infinite.
    """
    return timer_expr == _inf


def timer_decreasable(timer_expr: Time) -> z3.BoolRef:
    """
    Return a formula expressing that the timer expression is decreasable (finite and non-zero).

    :param timer_expr: The timer expression to check.
    :return: Formula expressing that the timer is decreasable.
    """
    if _UNINTERPRETED_TIMERS:
        return z3.And(timer_expr != _zero, timer_expr != _inf)

    return timer_expr > 0  # type: ignore


def timer_decrease(pre_timer_expr: Time, post_timer_expr: Time) -> z3.BoolRef:
    if _UNINTERPRETED_TIMERS:
        return timer_order(post_timer_expr, pre_timer_expr)

    return post_timer_expr == pre_timer_expr - 1  # type: ignore


@dataclass(frozen=True)
class TimerId:
    formula: z3.BoolRef

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, TimerId):
            return False
        return self.formula.eq(other.formula)

    def __hash__(self) -> int:
        return hash(self.formula)

    def __str__(self) -> str:
        return str(self.formula)

    def __repr__(self) -> str:
        return str(self.formula)


@dataclass(frozen=True)
class Timer(ABC):
    formula: z3.BoolRef
    params: ParamSpec

    @cached_property
    def id(self) -> TimerId:
        return TimerId(self.formula)

    @cached_property
    def name(self) -> str:
        return f"t_<{self.formula}>"

    @cached_property
    def signature(self) -> tuple[Sort, ...]:
        return tuple(v for v in self.params.values())

    @cached_property
    def args(self) -> tuple[str, ...]:
        return tuple(self.params.keys())

    def to_fun(self, suffix: str) -> z3.FuncDeclRef:
        signature: Signature = self.signature + (cast(Sort, _Time),)
        return cast(
            z3.FuncDeclRef,
            Fun.declare(signature)(self.name + suffix).fun,
        )

    def term(self, sym: "TimerTransitionSystem", params: Params) -> Time:
        return cast(Time, sym[self.name](*(params[arg] for arg in self.args)))

    @abstractmethod
    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef: ...

    def base_transition(
        self,
        pre_sym: "TimerTransitionSystem",
        post_sym: "TimerTransitionSystem",
        params: Params,
    ) -> z3.BoolRef:
        pre_timer = self.term(pre_sym, params)
        post_timer = self.term(post_sym, params)
        return z3.And(
            z3.Implies(
                timer_decreasable(pre_timer), timer_decrease(pre_timer, post_timer)
            ),
            z3.Implies(timer_infinite(pre_timer), timer_infinite(post_timer)),
        )

    def transition(
        self,
        pre_sym: "TimerTransitionSystem",
        post_sym: "TimerTransitionSystem",
        params: Params,
    ) -> None | z3.BoolRef:
        return None

    def complete_transition(
        self,
        pre_sym: "TimerTransitionSystem",
        post_sym: "TimerTransitionSystem",
        params: Params,
    ) -> z3.BoolRef:
        base_trans = self.base_transition(pre_sym, post_sym, params)
        trans = self.transition(pre_sym, post_sym, params)
        if trans is None:
            return base_trans
        else:
            return z3.And(base_trans, trans)


@dataclass(frozen=True)
class AtomicTimer(Timer):
    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return _replace_symbols_in_formula(self.formula, sym, params)


@dataclass(frozen=True)
class EventuallyTimer(Timer):
    child: Timer

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return timer_finite(self.child.term(sym, params))

    def transition(
        self,
        pre_sym: "TimerTransitionSystem",
        post_sym: "TimerTransitionSystem",
        params: Params,
    ) -> None | z3.BoolRef:
        return timer_zero(self.term(pre_sym, params)) == z3.Or(
            timer_zero(self.child.term(pre_sym, params)),
            timer_zero(self.term(post_sym, params)),
        )


@dataclass(frozen=True)
class GloballyTimer(Timer):
    child: Timer
    negated_child: Timer

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return timer_infinite(self.negated_child.term(sym, params))

    def transition(
        self,
        pre_sym: "TimerTransitionSystem",
        post_sym: "TimerTransitionSystem",
        params: Params,
    ) -> None | z3.BoolRef:
        return timer_zero(self.term(pre_sym, params)) == z3.And(
            timer_zero(self.child.term(pre_sym, params)),
            timer_zero(self.term(post_sym, params)),
        )


@dataclass(frozen=True)
class NegationTimer(Timer):
    child: Timer

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return timer_nonzero(self.child.term(sym, params))


@dataclass(frozen=True)
class ConjunctionTimer(Timer):
    children: tuple[Timer, ...]

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return z3.And(*(timer_zero(child.term(sym, params)) for child in self.children))


@dataclass(frozen=True)
class DisjunctionTimer(Timer):
    children: tuple[Timer, ...]

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return z3.Or(*(timer_zero(child.term(sym, params)) for child in self.children))


@dataclass(frozen=True)
class ImplicationTimer(Timer):
    antecedent: Timer
    consequent: Timer

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        return z3.Implies(
            timer_zero(self.antecedent.term(sym, params)),
            timer_zero(self.consequent.term(sym, params)),
        )


@dataclass(frozen=True)
class ForallTimer(Timer):
    body: Timer
    vars: ParamSpec

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        vars_params = {var: sort(var) for var, sort in self.vars.items()}
        all_params = params | vars_params
        return z3.ForAll(
            list(vars_params.values()), timer_zero(self.body.term(sym, all_params))
        )


@dataclass(frozen=True)
class ExistsTimer(Timer):
    body: Timer
    vars: ParamSpec

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        vars_params = {var: sort(var) for var, sort in self.vars.items()}
        all_params = params | vars_params
        return z3.Exists(
            list(vars_params.values()), timer_zero(self.body.term(sym, all_params))
        )


@dataclass(frozen=True)
class TimerTransitionSystem(BaseTransitionSystem):
    """
    Transition system for a set of timers.
    """

    ts: BaseTransitionSystem
    timers: dict[TimerId, Timer]
    root: Timer
    suffix: str = ""

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        if _UNINTERPRETED_TIMERS:
            added_symbols = {
                "zero": _zero.decl(),
                "inf": _inf.decl(),
                "timer_order": _timer_order.fun,
            }
        else:
            added_symbols = {}
        return (
            self.ts.symbols
            | {timer.name: timer.to_fun(self.suffix) for timer in self.timers.values()}
            | added_symbols
        )

    def clone(self, suffix: str) -> Self:
        return self.__class__(self.ts.clone(suffix), self.timers, self.root, suffix)

    def t(self, name: str) -> TimeFun:
        if name not in self.symbols:
            timer_names = [timer.name for timer in self.timers.values()]
            (closest_match,) = difflib.get_close_matches(name, timer_names, 1)
            assert False, (
                f"No timer for {name}; "
                f"closest match: {closest_match}. "
                f"All timers:\n"
                + "\n".join(
                    textwrap.indent(timer_name, " " * 4) for timer_name in timer_names
                )
            )
        return cast(TimeFun, self.symbols[name])

    @property
    def axioms(self) -> dict[str, z3.BoolRef]:
        axioms = {"order_axioms": timer_order_axioms()}

        for timer in self.timers.values():
            params = {param: sort(param) for param, sort in timer.params.items()}
            body = z3.And(
                timer_zero(timer.term(self, params)) == timer.axiom(self, params),
                timer_valid(timer.term(self, params)),
            )
            if params:
                body = z3.ForAll(list(params.values()), body)
            axioms[timer.name] = body

        return axioms | self.refinement_axioms

    @property
    def refinement_axioms(self) -> dict[str, z3.BoolRef]:
        not_free_variables = set(self.ts.symbols.keys())

        axioms = {}

        for phi1, t1 in self.timers.items():
            for phi2, t2 in self.timers.items():
                if phi1 == phi2:
                    continue
                sub = find_substitution(phi1.formula, phi2.formula, not_free_variables)
                if sub is not None:
                    spec = get_params(phi2.formula, not_free_variables)
                    params = spec.params() | sub
                    axiom = quantify(
                        True,
                        spec.consts(),
                        t1.term(self, params) == t2.term(self, spec.params()),
                    )
                    axioms[f"{phi1} => {phi2}"] = axiom

        return axioms

    @property
    def transitions(self) -> dict[str, z3.BoolRef]:
        transitions: list[z3.BoolRef] = []

        for timer in self.timers.values():
            params = {param: sort(param) for param, sort in timer.params.items()}
            trans = timer.complete_transition(self, self.next, params)
            if params:
                trans = z3.ForAll(list(params.values()), trans)
            transitions.append(trans)

        return {"timers": z3.And(*transitions)}

    @property
    def inits(self) -> dict[str, z3.BoolRef]:
        params: Params = {
            param: sort(param) for param, sort in self.root.params.items()
        }
        assert not params, "root timer should have no free variables"
        return {"timers": timer_zero(self.root.term(self, params))}


def create_timers[T: BaseTransitionSystem](
    ts: T,
    root_formula: z3.BoolRef,
    *formulas: z3.BoolRef,
) -> TimerTransitionSystem:
    timers: dict[TimerId, Timer] = {}

    # normalization
    root_formula = nnf(root_formula)
    formulas = tuple(nnf(formula) for formula in formulas)

    # symbols that are not free variables
    def add(timer: Timer) -> Timer:
        timers[timer.id] = timer
        return timer

    def create_timer(formula: z3.ExprRef) -> Timer:
        assert isinstance(formula, z3.BoolRef) or isinstance(formula, Bool)
        if z3.is_quantifier(formula) and formula.is_exists():
            variables, body = unpack_quantifier(formula)
            body_timer = create_timer(body)
            quant_vars = {
                str(var): Expr.declare(var.sort().name()) for var in variables
            }
            return add(
                ExistsTimer(
                    formula,
                    ParamSpec(
                        {
                            param: sort
                            for param, sort in body_timer.params.items()
                            if param not in quant_vars
                        }
                    ),
                    body_timer,
                    ParamSpec(quant_vars),
                )
            )
        elif z3.is_quantifier(formula) and formula.is_forall():
            variables, body = unpack_quantifier(formula)
            body_timer = create_timer(body)
            quant_vars = {
                str(var): Expr.declare(var.sort().name()) for var in variables
            }
            return add(
                ForallTimer(
                    formula,
                    ParamSpec(
                        {
                            param: sort
                            for param, sort in body_timer.params.items()
                            if param not in quant_vars
                        }
                    ),
                    body_timer,
                    ParamSpec(quant_vars),
                )
            )
        elif z3.is_implies(formula):
            ante, consq = formula.children()
            ante_timer = create_timer(ante)
            consq_timer = create_timer(consq)
            return add(
                ImplicationTimer(
                    formula,
                    ParamSpec(ante_timer.params | consq_timer.params),
                    ante_timer,
                    consq_timer,
                )
            )
        elif z3.is_or(formula):
            children = tuple(create_timer(child) for child in formula.children())
            return add(
                DisjunctionTimer(
                    formula,
                    ParamSpec(
                        reduce(operator.or_, (child.params for child in children))
                    ),
                    children,
                )
            )
        elif z3.is_and(formula):
            children = tuple(create_timer(child) for child in formula.children())
            return add(
                ConjunctionTimer(
                    formula,
                    ParamSpec(
                        reduce(operator.or_, (child.params for child in children))
                    ),
                    children,
                )
            )
        elif z3.is_not(formula):
            (child,) = formula.children()
            child_timer = create_timer(child)
            return add(NegationTimer(formula, child_timer.params, child_timer))
        elif is_G(formula):
            (child,) = formula.children()
            negated_child = nnf(z3.Not(cast(z3.BoolRef, child)))

            child_timer = create_timer(child)
            negated_child_timer = create_timer(negated_child)

            return add(
                GloballyTimer(
                    formula,
                    child_timer.params,
                    child_timer,
                    negated_child_timer,
                )
            )
        elif is_F(formula):
            (child,) = formula.children()
            child_timer = create_timer(child)
            return add(EventuallyTimer(formula, child_timer.params, child_timer))
        else:  # if nothing else then atomic
            atomic_params = get_params(formula, set(ts.symbols.keys()))
            return add(AtomicTimer(formula, atomic_params))

    root_timer = create_timer(root_formula)

    for formula in formulas:
        create_timer(formula)

    return TimerTransitionSystem(ts, timers, root_timer)


def get_params(root_expr: z3.ExprRef, excluded: set[str]) -> ParamSpec:
    params = {}

    def find_params(expr: z3.ExprRef) -> None:
        if (
            z3.is_const(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and expr.decl().name() not in excluded
        ):
            params[expr.decl().name()] = Expr.declare(expr.sort().name())
        else:
            for child in expr.children():
                find_params(child)

    find_params(root_expr)
    return ParamSpec(params)


def _replace_symbols_in_formula(
    formula: z3.BoolRef, sym: "TimerTransitionSystem", params: Params
) -> z3.BoolRef:
    if formula.decl().kind() != z3.Z3_OP_UNINTERPRETED:
        return formula
    terms = [
        _replace_symbols_in_term(child, sym, params) for child in formula.children()
    ]
    pred = formula.decl().name()
    assert pred in sym.symbols, f"Missing {pred} in symbols"
    return cast(z3.BoolRef, sym[pred](*terms))


def _replace_symbols_in_term(
    term: z3.ExprRef, sym: "TimerTransitionSystem", params: Params
) -> z3.ExprRef:
    if term.decl().kind() != z3.Z3_OP_UNINTERPRETED:
        return term

    name = term.decl().name()
    if name in params:
        return params[name]

    terms = [_replace_symbols_in_term(child, sym, params) for child in term.children()]
    assert name in sym.symbols, f"Missing {name} in symbols"
    return sym[name](*terms)
