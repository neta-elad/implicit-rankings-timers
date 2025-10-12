import io
from collections.abc import Iterable, Container
from dataclasses import dataclass
from functools import cached_property
from os import getenv
from pathlib import Path
from typing import cast, Literal, Protocol, Iterator

import z3

from typed_z3 import Rel, Expr


@dataclass(frozen=True)
class UnsatResult:
    result: z3.CheckSatResult
    model: z3.ModelRef | None = None
    size: int | None = None

    @cached_property
    def unsat(self) -> bool:
        return self.result == z3.unsat

    @cached_property
    def timeout(self) -> bool:
        return self.result == z3.unknown


def unsat_check(
    constraints: Iterable[z3.BoolRef],
    *,
    find_model: bool = True,
    print_calls: bool = False,
    minimize_sorts: Iterable[z3.SortRef] = (),
) -> UnsatResult:
    solver = default_solver()
    for c in constraints:
        if print_calls:
            print(c)
        solver.add(c)

    result = solver.check()
    if result == z3.unsat:
        return UnsatResult(z3.unsat)

    if result == z3.unknown:
        return UnsatResult(z3.unknown)

    model = None
    model_size = None
    if not find_model:
        return UnsatResult(z3.sat)
    try:
        model = solver.model()
    except z3.Z3Exception as e:
        print(f"sat but no model: {e}")

    if minimize_sorts:
        for size in range(1, 8):
            solver.push()
            for sort in minimize_sorts:
                if sort.kind() != z3.Z3_UNINTERPRETED_SORT:
                    continue
                solver.add(size_constraint(sort, size))
            if solver.check() == z3.sat:
                model_size = size
                model = solver.model()
                break
            else:
                solver.pop()

    return UnsatResult(z3.sat, model, model_size)


@dataclass(frozen=True)
class SatResult:
    result: z3.CheckSatResult
    core: list[z3.BoolRef]

    @cached_property
    def sat(self) -> bool:
        return self.result == z3.sat


def sat_check(
    constraints: Iterable[z3.BoolRef],
    *,
    unsat_core: bool = True,
    print_calls: bool = False,
) -> SatResult:
    solver = default_solver()
    named_constraints = {str(i): c for i, c in enumerate(constraints)}
    # Enable unsat core tracking
    if unsat_core:
        solver.set(unsat_core=True)
        for name, c in named_constraints.items():
            solver.assert_and_track(c, name)
    else:
        for c in constraints:
            if print_calls:
                print(c)
            solver.add(c)

    result = solver.check()
    core: list[z3.BoolRef] = []
    if result == z3.unsat and unsat_core:
        core = list()
        for clause in solver.unsat_core():
            core.append(named_constraints[str(clause)])
    return SatResult(result, core)


_DEFAULT_TIMEOUT = int(getenv("TIMEOUT_MS", "300_000"))  # 5 minute timeout


def default_solver() -> z3.Solver:
    z3.set_param("timeout", _DEFAULT_TIMEOUT)
    solver = z3.Solver()
    solver.set(mbqi=True)
    return solver


_model_counter = 0


def print_model_in_order(
    result: UnsatResult,
    symbols: Iterable[z3.FuncDeclRef],
    print_model_to_file: str | bool = True,
) -> None:
    if result.model is None:
        return

    model = result.model
    sorts = model.sorts()
    buffer = io.StringIO()

    if result.size is None:
        print("Small model failed", file=buffer)
    else:
        print(f"Small model of size {result.size}", file=buffer)

    for s in sorts:
        print(model.get_universe(s), file=buffer)

    for symbol in symbols:
        if symbol in model:  # type: ignore
            print(symbol, ":", model[symbol], file=buffer)
        else:
            print(f"Missing {symbol} in model", file=buffer)

    if isinstance(print_model_to_file, str) or print_model_to_file is True:
        if not isinstance(print_model_to_file, str):
            print_model_to_file = ""
        else:
            print_model_to_file = print_model_to_file.replace(" ", "-")
        global _model_counter
        _model_counter += 1
        path = Path(f"models/{_model_counter}-{print_model_to_file}.txt")
        path.parent.mkdir(exist_ok=True)
        path.write_text(buffer.getvalue())
        print(f"Model written to {path.absolute()}")
    else:
        print(buffer.getvalue())


_core_counter = 0


def print_unsat_core(
    result: SatResult,
    print_core_to_file: str | bool = True,
) -> None:
    if not result.core:
        return

    buffer = io.StringIO()

    for clause in result.core:
        print(clause, file=buffer)

    if isinstance(print_core_to_file, str) or print_core_to_file is True:
        if not isinstance(print_core_to_file, str):
            print_core_to_file = ""
        else:
            print_core_to_file = print_core_to_file.replace(" ", "-")
        global _core_counter
        _core_counter += 1
        path = Path(f"cores/{_core_counter}-{print_core_to_file}.txt")
        path.parent.mkdir(exist_ok=True)
        path.write_text(buffer.getvalue())
        print(f"Unsat core written to {path.absolute()}")
    else:
        print(buffer.getvalue())


def size_constraint(sort: z3.SortRef, size: int) -> z3.BoolRef:
    each = z3.Const(f"{sort}_each", sort)
    return z3.ForAll(
        each,
        z3.Or(*((each == z3.Const(f"{sort}_size_{i}", sort)) for i in range(size))),
    )


def quantify(
    is_forall: bool, variables: Iterable[z3.Const], body: z3.BoolRef, *, qid: str = ""
) -> z3.BoolRef:
    if not variables:
        return body
    quant_vars = list(variables)
    if is_forall:
        return z3.ForAll(quant_vars, body, qid=qid)
    else:
        return z3.Exists(quant_vars, body, qid=qid)


def order_leq[T: Expr](order: Rel[T, T]) -> z3.BoolRef:
    sort = order.fun.domain(0)
    X = cast(T, z3.Const("X", sort))
    Y = cast(T, z3.Const("Y", sort))
    Z = cast(T, z3.Const("Z", sort))
    return z3.And(
        # transitive, antisymmetric z3.and total
        z3.ForAll(
            [X, Y, Z],
            z3.Implies(z3.And(order(X, Y), order(Y, Z)), order(X, Z)),
        ),
        z3.ForAll([X, Y], z3.Implies(z3.And(order(X, Y), order(Y, X)), X == Y)),
        z3.ForAll([X, Y], z3.Or(order(X, Y), order(Y, X))),
    )


def strict_partial_order[T: Expr](order_rel: Rel[T, T]) -> z3.BoolRef:
    order_fun = order_rel.fun

    def order(*args: z3.ExprRef) -> z3.BoolRef:
        return cast(z3.BoolRef, order_fun(*args))

    half_arity = order_fun.arity() // 2
    sorts = [order_fun.domain(i) for i in range(half_arity)]

    return strict_partial_order_axioms(order, sorts)


class Predicate(Protocol):
    def __call__(self, *args: z3.ExprRef) -> z3.BoolRef: ...


def strict_partial_order_axioms(
    order: Predicate, sorts: list[z3.SortRef]
) -> z3.BoolRef:
    X = [z3.Const(f"X{i}", sort) for i, sort in enumerate(sorts)]
    Y = [z3.Const(f"Y{i}", sort) for i, sort in enumerate(sorts)]
    Z = [z3.Const(f"Z{i}", sort) for i, sort in enumerate(sorts)]
    # todo: require immutable
    return z3.And(
        # transitive, antisymmetric and total
        z3.ForAll(
            X + Y + Z,
            z3.Implies(z3.And(order(*X, *Y), order(*Y, *Z)), order(*X, *Z)),
        ),
        z3.ForAll(X, z3.Not(order(*X, *X))),
    )


def minimal_in_order[T: Expr](term: T, order: Rel[T, T]) -> z3.BoolRef:
    sort = order.fun.domain(0)
    Y = cast(T, z3.Const("Y", sort))
    return z3.ForAll(Y, z3.Not(order(Y, term)))


def clone_vars(quantifier: z3.QuantifierRef) -> list[z3.Const]:
    return [
        z3.Const(quantifier.var_name(i), quantifier.var_sort(i))
        for i in range(quantifier.num_vars())
    ]


def unpack_quantifier(
    quantifier: z3.QuantifierRef,
) -> tuple[list[z3.Const], z3.BoolRef]:
    bounding_vars = clone_vars(quantifier)

    body = z3.substitute_vars(
        quantifier.body(), *reversed(bounding_vars)
    )  # Z3 uses vars in reverse order

    return bounding_vars, body


type InstantiationMode = Literal["exists", "forall", "both"]


class Instances(Protocol):
    def items(self) -> Iterable[tuple[str, z3.ExprRef]]: ...


def instantiate[T: z3.ExprRef](
    expr: T,
    instantiation: Instances,
    mode: InstantiationMode = "exists",
) -> T:
    def do_instantiate(
        expr_: z3.ExprRef, instances: dict[str, z3.ExprRef]
    ) -> z3.ExprRef:
        if z3.is_quantifier(expr_):
            variables, body = unpack_quantifier(expr_)
            names = {str(var): var for var in variables}
            instants_left = {
                name: value for name, value in instances.items() if name not in names
            }
            if mode == "both" or (expr_.is_exists() == (mode == "exists")):
                subs = [
                    (names[name], value)
                    for name, value in instances.items()
                    if name in names
                ]
                body = z3.substitute(body, *subs)
                variables_left = [
                    var for name, var in names.items() if name not in instances
                ]
                body = cast(z3.BoolRef, do_instantiate(body, instants_left))
                return quantify(expr_.is_forall(), variables_left, body)
            else:  # remove bound variables
                body = cast(z3.BoolRef, do_instantiate(body, instants_left))
                return quantify(expr_.is_forall(), variables, body)
        decl = expr_.decl()
        children = [do_instantiate(child, instances) for child in expr_.children()]
        return decl(*children)

    return cast(T, do_instantiate(expr, dict(instantiation.items())))


type Substitution = dict[str, z3.ExprRef]


def find_substitution(
    phi: z3.ExprRef, subbed_phi: z3.ExprRef, excluded: Container[str] = frozenset()
) -> Substitution | None:
    if z3.is_quantifier(phi) != z3.is_quantifier(subbed_phi):
        return None
    if z3.is_quantifier(phi):
        variables, body = unpack_quantifier(phi)
        assert z3.is_quantifier(subbed_phi)
        subbed_variables, subbed_body = unpack_quantifier(subbed_phi)
        if any(
            not var.eq(subbed_var)
            for var, subbed_var in zip(variables, subbed_variables)
        ):
            return None
        return find_substitution(body, subbed_body, excluded)

    decl = phi.decl()
    subbed_decl = subbed_phi.decl()
    if (
        decl.kind() != subbed_decl.kind()
        or decl.arity() != subbed_decl.arity()
        or decl.range() != subbed_decl.range()
        or any(decl.domain(i) != subbed_decl.domain(i) for i in range(decl.arity()))
    ):
        return None

    if z3.is_const(phi) and decl.kind() == z3.Z3_OP_UNINTERPRETED:
        if str(phi) == str(subbed_phi):
            return {}
        if str(phi) in excluded:
            return None
        return {str(phi): subbed_phi}

    if decl != subbed_decl:
        return None

    return _merge_subs(
        [
            find_substitution(child, subbed_child, excluded)
            for child, subbed_child in zip(phi.children(), subbed_phi.children())
        ]
    )


def _merge_subs(subs: list[Substitution | None]) -> Substitution | None:
    merged: Substitution = {}
    for sub in subs:
        if sub is None:
            return None
        if any(
            key in merged and not merged[key].eq(value) for key, value in sub.items()
        ):
            return None
        merged |= sub
    return merged
