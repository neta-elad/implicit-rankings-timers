from prelude import *


class Variable(Finite): ...


class Clause(Finite): ...


class SatBacktracking(TransitionSystem):
    curr_var: Variable
    dummy_leaf: Immutable[Variable]
    dummy_root: Immutable[Variable]
    sat: Bool
    unsat: Bool

    var_order: Immutable[Rel[Variable, Variable]]
    curr_assignment: Rel[Variable, Bool]
    appears: Immutable[Rel[Clause, Variable, Bool]]

    def succ(self, x: Variable, y: Variable) -> BoolRef:
        Z = Variable("Z")
        return And(
            x != y,
            self.var_order(x, y),
            ForAll(Z, Implies(self.var_order(x, Z), Or(x == Z, self.var_order(y, Z)))),
        )

    @axiom
    def order(self, X: Variable, Y: Variable, Z: Variable) -> BoolRef:
        return And(
            Implies(And(self.var_order(X, Y), self.var_order(Y, X)), X == Y),
            Implies(
                And(self.var_order(X, Y), self.var_order(Y, Z)), self.var_order(X, Z)
            ),
            Or(self.var_order(X, Y), self.var_order(Y, X)),
            self.var_order(X, self.dummy_leaf),
            self.var_order(self.dummy_root, X),
        )

    @axiom
    def dummies(self, C: Clause, b: Bool) -> BoolRef:
        return And(
            Not(self.appears(C, self.dummy_leaf, b)),
            Not(self.appears(C, self.dummy_root, b)),
        )

    @init
    def initial(self, X: Variable, b: Bool) -> BoolRef:
        return And(
            self.succ(self.dummy_root, self.curr_var),
            self.curr_assignment(X, b) == False,
            Not(self.sat),
            Not(self.unsat),
        )

    def increase_curr_var(self) -> BoolRef:
        return self.succ(self.curr_var, self.next.curr_var)

    def decrease_curr_var(self) -> BoolRef:
        return self.succ(self.next.curr_var, self.curr_var)

    def update_curr_assignment(self, var: Variable, value: Bool) -> BoolRef:
        return self.curr_assignment.update(
            {(var, value): true, (var, value.neg()): false}
        )

    def remove_assignment_var(self, var: Variable) -> BoolRef:
        return self.curr_assignment.update({(var, true): false, (var, false): false})

    def result_unchanged(self) -> BoolRef:
        return And(self.sat.unchanged(), self.unsat.unchanged())

    def curr_var_not_dummy(self) -> BoolRef:
        return And(
            self.curr_var != self.dummy_leaf,
            self.curr_var != self.dummy_root,
        )

    @transition
    def assign_true(self) -> BoolRef:
        return And(
            self.curr_var_not_dummy(),
            Not(self.curr_assignment(self.curr_var, true)),
            Not(self.curr_assignment(self.curr_var, false)),
            self.update_curr_assignment(self.curr_var, true),
            self.increase_curr_var(),
            self.result_unchanged(),
        )

    @transition
    def assign_false(self) -> BoolRef:
        return And(
            self.curr_var_not_dummy(),
            self.curr_assignment(self.curr_var, true),
            self.update_curr_assignment(self.curr_var, false),
            self.increase_curr_var(),
            self.result_unchanged(),
        )

    @transition
    def backprop_from_unsat_clause(self, c: Clause) -> BoolRef:
        X = Variable("X")
        b = Bool("b")
        return And(
            ForAll(
                [X, b],
                Implies(self.appears(c, X, b), self.curr_assignment(X, b.neg())),
            ),
            self.decrease_curr_var(),
            self.remove_assignment_var(self.curr_var),
            self.result_unchanged(),
        )

    @transition
    def backprop_from_false_var(self) -> BoolRef:
        return And(
            self.curr_assignment(self.curr_var, false),
            self.decrease_curr_var(),
            self.remove_assignment_var(self.curr_var),
            self.result_unchanged(),
        )

    @transition
    def reached_sat(self) -> BoolRef:
        C = Clause("C")
        X = Variable("X")
        b = Bool("b")
        return And(
            ForAll(
                C,
                Exists([X, b], And(self.appears(C, X, b), self.curr_assignment(X, b))),
            ),
            self.curr_var.unchanged(),
            self.curr_assignment.unchanged(),
            self.next.sat,
            self.unsat.unchanged(),
        )

    @transition
    def reached_unsat(self) -> BoolRef:
        return And(
            self.curr_var == self.dummy_root,
            self.curr_var.unchanged(),
            self.curr_assignment.unchanged(),
            self.next.unsat,
            self.sat.unchanged(),
        )


class SatBacktrackingProp(Prop[SatBacktracking]):
    def prop(self) -> BoolRef:
        return F(Or(self.sys.sat, self.sys.unsat))


class SatBacktrackingProof(Proof[SatBacktracking], prop=SatBacktrackingProp):
    def unassigned(self, var: Variable) -> BoolRef:
        return And(
            Not(self.sys.curr_assignment(var, true)),
            Not(self.sys.curr_assignment(var, false)),
        )

    @invariant
    def consistent_assignment(self, X: Variable) -> BoolRef:
        return Not(
            And(
                self.sys.curr_assignment(X, true),
                self.sys.curr_assignment(X, false),
            )
        )

    @invariant
    def sat_agrees_with_clauses(self, C: Clause) -> BoolRef:
        X = Variable("X")
        b = Bool("b")
        return Implies(
            self.sys.sat,
            Exists(
                [X, b], And(self.sys.appears(C, X, b), self.sys.curr_assignment(X, b))
            ),
        )

    @invariant
    def unassigned_dummies(self) -> BoolRef:
        return And(
            self.unassigned(self.sys.dummy_root),
            self.unassigned(self.sys.dummy_leaf),
        )

    @invariant
    def assignment_follows_order_unassigned(self, X: Variable) -> BoolRef:
        return Implies(
            And(self.sys.var_order(self.sys.curr_var, X), self.sys.curr_var != X),
            self.unassigned(X),
        )

    @invariant
    def assignment_follows_order_assigned(self, X: Variable) -> BoolRef:
        return Implies(
            And(
                self.sys.var_order(X, self.sys.curr_var),
                X != self.sys.curr_var,
                X != self.sys.dummy_root,
            ),
            Not(self.unassigned(X)),
        )

    @invariant
    def consistent_result(self) -> BoolRef:
        return Not(And(self.sys.sat, self.sys.unsat))

    @temporal_invariant
    def not_terminated(self) -> BoolRef:
        return G(Not(Or(self.sys.sat, self.sys.unsat)))

    def ghost_assignment(self, v: Variable) -> BoolRef:
        return And(
            v != self.sys.dummy_leaf,
            v != self.sys.dummy_root,
            Or(
                self.sys.curr_assignment(v, true),
                And(
                    self.unassigned(self.sys.curr_var),
                    self.sys.curr_var != self.sys.dummy_root,
                    self.unassigned(v),
                    self.sys.var_order(self.sys.curr_var, v),
                ),
            ),
        )

    def strict_order(self, v1: Variable, v2: Variable) -> BoolRef:
        return And(
            self.sys.var_order(v2, v1),
            v1 != v2,
        )

    def rank1(self) -> Rank:
        return DomainLexRank(BinRank(self.ghost_assignment), self.strict_order)

    def not_assigned_true(self, v: Variable) -> BoolRef:
        return Not(self.sys.curr_assignment(v, true))

    def num_not_true(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.not_assigned_true), None)

    def assigned_false(self, v: Variable) -> BoolRef:
        return self.sys.curr_assignment(v, false)

    def num_false(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.assigned_false), None)

    def rank2(self) -> Rank:
        return PointwiseRank(self.num_not_true(), self.num_false())

    def curr_is_leaf(self) -> BoolRef:
        return self.sys.curr_var == self.sys.dummy_leaf

    def rank3(self) -> Rank:
        return BinRank(self.curr_is_leaf)

    def rank(self) -> Rank:
        return LexRank(
            self.rank1(),
            self.rank2(),
            self.rank3(),
        )


SatBacktrackingProof().check()
