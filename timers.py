import operator
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import Any, cast, Self, Protocol

import z3

from temporal import is_G, is_F
from ts import BaseTransitionSystem, ParamSpec, Params
from typed_z3 import Rel, Fun, Sort, Expr, Int, Bool

type Time = Int


class TimeFun(Protocol):
    def __call__(self, *args: z3.ExprRef) -> Time: ...


def timer_order() -> Rel[Time, Time]:
    return Int.lt()


def timer_valid(timer_expr: Time) -> z3.BoolRef:
    return timer_expr >= -1


def timer_zero(timer_expr: Time) -> z3.BoolRef:
    # todo: configurable lia/uninterpreted
    return timer_expr == 0


def timer_nonzero(timer_expr: Time) -> z3.BoolRef:
    return timer_expr != 0


def timer_finite(timer_expr: Time) -> z3.BoolRef:
    # todo configurable
    return timer_expr >= 0


def timer_infinite(timer_expr: Time) -> z3.BoolRef:
    # todo configurable
    return timer_expr == -1


def timer_decreasable(timer_expr: Time) -> z3.BoolRef:
    return timer_expr > 0


def timer_decrease(pre_timer_expr: Time, post_timer_expr: Time) -> z3.BoolRef:
    return post_timer_expr == pre_timer_expr - 1


@dataclass(frozen=True)
class TimerId:
    formula: z3.BoolRef

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, TimerId):
            return False
        return self.formula.eq(other.formula)

    def __hash__(self) -> int:
        return hash(self.formula)


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
        return cast(
            z3.FuncDeclRef, Fun.declare(self.signature + (Int,))(self.name + suffix).fun
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
        return z3.Implies(
            timer_decreasable(pre_timer), timer_decrease(pre_timer, post_timer)
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
        vars_params = {var: sort.const(var) for var, sort in self.vars.items()}
        all_params = params | vars_params
        return z3.ForAll(
            list(vars_params.values()), timer_zero(self.body.term(sym, all_params))
        )


@dataclass(frozen=True)
class ExistsTimer(Timer):
    body: Timer
    vars: ParamSpec

    def axiom(self, sym: "TimerTransitionSystem", params: Params) -> z3.BoolRef:
        vars_params = {var: sort.const(var) for var, sort in self.vars.items()}
        all_params = params | vars_params
        return z3.Exists(
            list(vars_params.values()), timer_zero(self.body.term(sym, all_params))
        )


class TimerTransitionSystem(BaseTransitionSystem):
    ts: BaseTransitionSystem
    timers: dict[TimerId, Timer]
    root: Timer
    suffix: str

    def __init__(
        self,
        ts: BaseTransitionSystem,
        timers: dict[TimerId, Timer],
        root: Timer,
        suffix: str = "",
    ) -> None:
        self.ts = ts
        self.timers = timers
        self.root = root
        self.suffix = suffix

    @cached_property
    def symbols(self) -> dict[str, z3.FuncDeclRef]:
        return self.ts.symbols | {
            timer.name: timer.to_fun(self.suffix) for timer in self.timers.values()
        }

    @cached_property
    def next(self) -> Self:
        return self.__class__(self.ts.next, self.timers, self.root, self.suffix + "'")

    def t(self, name: str) -> TimeFun:
        assert name in self.symbols, f"No timer for formula {name}"
        return cast(TimeFun, self.symbols[name])

    @property
    def axioms(self) -> dict[str, z3.BoolRef]:
        axioms = {}

        for timer in self.timers.values():
            params = {param: sort.const(param) for param, sort in timer.params.items()}
            body = z3.And(
                timer_zero(timer.term(self, params)) == timer.axiom(self, params),
                timer_valid(timer.term(self, params)),
            )
            if params:
                body = z3.ForAll(list(params.values()), body)
            axioms[timer.name] = body

        return axioms

    @property
    def transitions(self) -> dict[str, z3.BoolRef]:
        transitions: list[z3.BoolRef] = []

        for timer in self.timers.values():
            params = {param: sort.const(param) for param, sort in timer.params.items()}
            trans = timer.complete_transition(self, self.next, params)
            if params:
                trans = z3.ForAll(list(params.values()), trans)
            transitions.append(trans)

        return {"timers": z3.And(*transitions)}

    @property
    def inits(self) -> dict[str, z3.BoolRef]:
        params = {param: sort.const(param) for param, sort in self.root.params.items()}
        assert not params, "root timer should have no free variables"
        return {"timers": timer_zero(self.root.term(self, params))}


def create_timers[T: BaseTransitionSystem](
    root_formula: z3.BoolRef, ts: T
) -> TimerTransitionSystem:
    timers: dict[TimerId, Timer] = {}

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
            negated_child = normalized_not(child)

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


def normalized_not(formula: z3.ExprRef) -> z3.BoolRef:
    assert isinstance(formula, z3.BoolRef)
    if z3.is_not(formula):
        (child,) = formula.children()
        return cast(z3.BoolRef, child)
    else:
        return z3.Not(formula)


def clone_vars(quantifier: z3.QuantifierRef) -> list[z3.ExprRef]:
    return [
        z3.Const(quantifier.var_name(i), quantifier.var_sort(i))
        for i in range(quantifier.num_vars())
    ]


def unpack_quantifier(
    quantifier: z3.QuantifierRef,
) -> tuple[list[z3.ExprRef], z3.BoolRef]:
    bounding_vars = clone_vars(quantifier)

    body = z3.substitute_vars(
        quantifier.body(), *reversed(bounding_vars)
    )  # Z3 uses vars in reverse order

    return bounding_vars, body


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
