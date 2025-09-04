import io
from collections.abc import Iterable
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import cast, Literal

import z3

from typed_z3 import Rel, Expr


@dataclass(frozen=True)
class SatResult:
    result: z3.CheckSatResult
    model: z3.ModelRef | None = None
    size: int | None = None

    @cached_property
    def unsat(self) -> bool:
        return self.result == z3.unsat


def unsat_check(
    constraints: Iterable[z3.BoolRef],
    *,
    find_model: bool = True,
    minimize_model: bool = True,
    unsat_core: bool = False,
    print_calls: bool = False,
    print_smtlib: bool = False,
    minimize_sorts: Iterable[z3.SortRef] = (),
) -> SatResult:
    z3.set_param("timeout", 5 * 60 * 1000)  # 5 minute timeout
    solver = z3.Solver()
    solver.set(mbqi=True)
    # Enable unsat core tracking
    if unsat_core:
        solver.set(unsat_core=True)
        for i, c in enumerate(constraints):
            if print_calls:
                print("constraint number", i)
                print(c)
            solver.assert_and_track(c, str(i))
    else:
        for c in constraints:
            if print_calls:
                print(c)
            solver.add(c)

    if print_smtlib:
        print(solver.sexpr())

    result = solver.check()
    if result == z3.unsat:
        if unsat_core:
            core = solver.unsat_core()
            print("Unsat core:", core)
        return SatResult(z3.unsat)

    if result == z3.sat:
        model = None
        model_size = None
        if find_model:
            try:
                full_model = solver.model()
            except z3.Z3Exception as e:
                print(f"sat but no model: {e}")
            if minimize_model and minimize_sorts:
                for size in range(1, 8):
                    solver.push()
                    for sort in minimize_sorts:
                        if sort.eq(z3.IntSort()):
                            continue
                        solver.add(size_constraint(sort, size))
                    new_result = solver.check()
                    if new_result == z3.sat:
                        model_size = size
                        model = solver.model()
                        break
                    else:
                        solver.pop()

                if model is None:
                    print("small model failed")
                    model = full_model
            else:
                model = full_model

        return SatResult(z3.sat, model, model_size)
    else:
        return SatResult(z3.unknown)


_model_counter = 0


def print_model_in_order(
    result: SatResult,
    symbols: Iterable[z3.FuncDeclRef],
    print_model_to_file: str | bool = True,
) -> None:
    if result.model is None:
        return

    model = result.model
    sorts = model.sorts()
    buffer = io.StringIO()

    if result.size is not None:
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
        path = Path(f"model-{_model_counter}-{print_model_to_file}.txt")
        print(f"Model written to {path.absolute()}")
        path.write_text(buffer.getvalue())
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


def order_lt[T: Expr](order: Rel[T, T]) -> z3.BoolRef:
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
        z3.ForAll([X], z3.Not(order(X, X))),
        z3.ForAll([X, Y], z3.Or(X == Y, order(X, Y), order(Y, X))),
    )


def minimal_in_order_lt[T: Expr](term: T, order: Rel[T, T]) -> z3.BoolRef:
    sort = order.fun.domain(0)
    Y = cast(T, z3.Const("Y", sort))
    return z3.ForAll(Y, z3.Not(order(Y, term)))
