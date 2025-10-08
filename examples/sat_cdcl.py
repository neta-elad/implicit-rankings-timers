from prelude import *

# @status - problem with backjump transition

class Variable(Finite): ...


class Clause(Finite): ...


class Level(Finite): ...


class CDCL(TransitionSystem):
    min_level: Immutable[Level]
    lvl_order: Immutable[Rel[Level, Level]]
    appears: Immutable[Rel[Clause, Variable, Bool]]

    fail: Bool
    curr_lvl: Level

    m_seq: Rel[Level, Variable, Bool]
    decision_lvl: Rel[Level]
    assign_lvl: Rel[Level]
    in_F: Rel[Clause]

    def succ(self, x: Level, y: Level) -> BoolRef:
        k = Level("k")
        return And(
            x != y,
            self.lvl_order(x, y),
            ForAll(k, Implies(self.lvl_order(x, k), Or(k == x, self.lvl_order(y, k)))),
        )

    @axiom
    def order(self, i: Level, j: Level, k: Level) -> BoolRef:
        return And(
            Implies(And(self.lvl_order(i, j), self.lvl_order(j, i)), i == j),
            Implies(
                And(self.lvl_order(i, j), self.lvl_order(j, k)), self.lvl_order(i, k)
            ),
            Or(self.lvl_order(i, j), self.lvl_order(j, i)),
            self.lvl_order(self.min_level, i),
        )

    @axiom
    def second_order_behavior_of_clauses(self, i: Level) -> BoolRef:
        C = Clause("C")
        X = Variable("X")
        b = Bool("b")
        j = Level("j")
        return Exists(
            C,
            ForAll(
                [X, b],
                self.appears(C, X, b)
                == Exists(
                    j,
                    And(
                        self.lvl_order(j, i),
                        self.m_seq(i, X, b.neg()),
                        self.decision_lvl(i),
                    ),
                ),
            ),
        )

    def undefined(self, x: Variable) -> BoolRef:
        i = Level("i")
        b = Bool("b")
        return ForAll([i, b], Not(self.m_seq(i, x, b)))

    @init
    def initial(self, i: Level, X: Variable, b: Bool) -> BoolRef:
        return And(
            self.undefined(X),
            self.curr_lvl == self.min_level,
            Not(self.decision_lvl(i)),
            Not(self.assign_lvl(i)),
            Not(self.m_seq(i, X, b)),
        )

    def occurs_in_clause_of_F(self, x: Variable) -> BoolRef:
        D = Clause("D")
        return Exists(
            D,
            And(self.in_F(D), Or(self.appears(D, x, true), self.appears(D, x, false))),
        )

    @transition
    def unit_prop(self, c: Clause, x: Variable, val: Bool) -> BoolRef:
        X = Variable("X")
        b = Bool("b")
        i = Level("i")
        return And(
            self.in_F(c),
            self.appears(c, x, b),
            self.undefined(x),
            ForAll(
                [X, b],
                Implies(
                    And(self.appears(c, X, b), Not(And(X == x, b == val))),
                    Exists(i, self.m_seq(i, X, b.neg())),
                ),
            ),  # M models neg c \ l
            self.succ(self.curr_lvl, self.next.curr_lvl),
            ForAll(
                [i, X, b],
                self.next.m_seq(i, X, b)
                == Or(self.m_seq(i, X, b), And(i == self.curr_lvl, X == x, b == val)),
            ),
            self.decision_lvl.unchanged(),
            self.assign_lvl.update({(self.curr_lvl,): true}),
            self.fail.unchanged(),
            self.in_F.unchanged(),
        )

    @transition
    def decide(self, x: Variable, value: Bool) -> BoolRef:
        return And(
            self.occurs_in_clause_of_F(x),
            self.undefined(x),
            self.succ(self.curr_lvl, self.next.curr_lvl),
            self.m_seq.update({(self.curr_lvl, x, value): true}),
            self.decision_lvl.update({(self.curr_lvl,): true}),
            self.assign_lvl.update({(self.curr_lvl,): true}),
            self.fail.unchanged(),
            self.in_F.unchanged(),
        )

    @transition
    def reach_fail(self, c: Clause) -> BoolRef:
        i = Level("i")
        X = Variable("X")
        b = Bool("b")
        return And(
            self.in_F(c),
            ForAll(i, Not(self.decision_lvl(i))),
            ForAll(
                [X, b],
                Implies(self.appears(c, X, b), Exists(i, self.m_seq(i, X, b.neg()))),
            ),  # M models neg c
            self.decision_lvl.unchanged(),
            self.curr_lvl.unchanged(),
            self.m_seq.unchanged(),
            self.assign_lvl.unchanged(),
            self.next.fail,
            self.in_F.unchanged(),
        )

    @transition
    def backjump(
        self,
        c_learn: Clause,
        x_old: Variable,
        b_old: Bool,
        x_new: Variable,
        b_new: Bool,
        lvl: Level,
    ) -> BoolRef:
        i = Level("i")
        X = Variable("X")
        b = Bool("b")
        return And(
            self.m_seq(lvl, x_old, b_old),
            self.decision_lvl(lvl),
            self.appears(c_learn, x_new, b_new),
            # We do not encode the fact that F models c
            ForAll(
                [X, b],
                Implies(
                    And(self.appears(c_learn, X, b), Not(And(X == x_new, b == b_new))),
                    Exists(i, self.m_seq(i, X, b.neg())),
                ),
            ),  # M models neg c \ l_new
            self.undefined(x_new),
            self.occurs_in_clause_of_F(x_new),
            # transition:
            ForAll(
                i,
                self.next.decision_lvl(i)
                == And(self.decision_lvl(i), self.lvl_order(i, lvl), i != lvl),
            ),
            ForAll(
                i,
                self.next.assign_lvl(i)
                == And(self.assign_lvl(i), self.lvl_order(i, lvl)),
            ),
            self.succ(
                lvl, self.next.curr_lvl
            ),  # pushing back the next level one after lvl
            self.fail.unchanged(),
            ForAll(
                [i, X, b],
                self.next.m_seq(i, X, b)
                == Or(
                    And(
                        self.m_seq(i, X, b), self.lvl_order(i, lvl), i != lvl
                    ),  # all variable assignments before lvl stay
                    And(i == lvl, X == x_new, b == b_new),  # new variable assignment
                ),
            ),
            self.in_F.unchanged(),
        )

    @transition
    def learn(self, c_learn: Clause) -> BoolRef:

        return And(
            Not(self.in_F(c_learn)),
            # Not modeling the fact that c_learn follows from F - not safe
            self.decision_lvl.unchanged(),
            self.curr_lvl.unchanged(),
            self.m_seq.unchanged(),
            self.assign_lvl.unchanged(),
            self.fail.unchanged(),
            self.in_F.update({(c_learn,): true}),
        )


class CDCLProp(Prop[CDCL]):
    def prop(self) -> BoolRef:
        C = Clause("C")
        i = Level("i")
        X = Variable("X")
        b = Bool("b")
        return F(
            Or(
                self.sys.fail,
                ForAll(
                    C,
                    Implies(
                        self.sys.in_F(C),
                        Exists(
                            [i, X, b],
                            And(self.sys.m_seq(i, X, b), self.sys.appears(C, X, b)),
                        ),
                    ),
                ),
            )
        )


class CDCLProof(Proof[CDCL], prop=CDCLProp):
    @invariant
    def m_then_occurs(self, i: Level, X: Variable, b: Bool) -> BoolRef:
        return Implies(self.sys.m_seq(i, X, b), self.sys.occurs_in_clause_of_F(X))

    @invariant
    def consistent_m(
        self, i: Level, j: Level, X: Variable, b1: Bool, b2: Bool
    ) -> BoolRef:
        return Implies(
            And(
                self.sys.m_seq(i, X, b1),
                self.sys.m_seq(j, X, b2),
            ),
            And(i == j, b1 == b2),
        )

    @invariant
    def every_level_before_curr_assigned(self, i: Level) -> BoolRef:
        return Implies(
            And(self.sys.lvl_order(i, self.sys.curr_lvl), i != self.sys.curr_lvl),
            self.sys.assign_lvl(i),
        )

    @invariant
    def assign_agrees_with_order(self, i: Level, j: Level) -> BoolRef:
        return Implies(
            And(self.sys.lvl_order(i, j), self.sys.assign_lvl(j)),
            self.sys.assign_lvl(i),
        )

    @invariant
    def decision_then_assign(self, i: Level) -> BoolRef:
        return Implies(self.sys.decision_lvl(i), self.sys.assign_lvl(i))

    @invariant
    def assign_then_in_m(self, i: Level) -> BoolRef:
        X = Variable("X")
        b = Bool("b")
        return self.sys.assign_lvl(i) == Exists([X, b], self.sys.m_seq(i, X, b))

    @invariant
    def curr_not_assigned(self) -> BoolRef:
        return Not(self.sys.assign_lvl(self.sys.curr_lvl))

    @temporal_invariant
    def not_prop(self) -> BoolRef:
        C = Clause("C")
        i = Level("i")
        X = Variable("X")
        b = Bool("b")
        return Not(
            F(
                Or(
                    self.sys.fail,
                    ForAll(
                        C,
                        Implies(
                            self.sys.in_F(C),
                            Exists(
                                [i, X, b],
                                And(self.sys.m_seq(i, X, b), self.sys.appears(C, X, b)),
                            ),
                        ),
                    ),
                )
            )
        )

    def negated_pred(self, i: Level, j: Level) -> BoolRef:
        k = Level("k")
        return Not(
            And(
                self.sys.assign_lvl(i),
                self.sys.assign_lvl(j),
                self.sys.lvl_order(i, j),
                ForAll(
                    k,
                    Implies(
                        And(self.sys.lvl_order(i, k), self.sys.lvl_order(k, j)),
                        Not(self.sys.decision_lvl(k)),
                    ),
                ),
            )
        )

    def binary_ij(self) -> Rank:
        return BinRank(self.negated_pred)

    def sum_j(self) -> Rank:
        return DomainPointwiseRank(self.binary_ij(), ParamSpec(j=Level), None)

    def strict_order(self, i1: Level, i2: Level) -> BoolRef:
        return And(self.sys.lvl_order(i1, i2), i1 != i2)

    def lex(self) -> Rank:
        return DomainLexRank(self.sum_j(), self.strict_order)

    def undefined_x(self, x: Variable) -> BoolRef:
        return self.sys.undefined(x)

    def bin_unassigned(self) -> Rank:
        return BinRank(self.undefined_x)

    def num_unassigned(self) -> Rank:
        return DomainPointwiseRank.close(self.bin_unassigned(), None)

    def not_in_F(self, c: Clause) -> BoolRef:
        return Not(self.sys.in_F(c))

    def bin_not_in_F(self) -> Rank:
        return BinRank(self.not_in_F)

    def num_not_in_F(self) -> Rank:
        return DomainPointwiseRank.close(self.bin_not_in_F(), None)

    def rank(self) -> Rank:
        return LexRank(
            self.lex(),
            self.num_unassigned(),
            self.num_not_in_F(),
        )


CDCLProof().check()
