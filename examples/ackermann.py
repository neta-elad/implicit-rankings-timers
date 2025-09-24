from prelude import *

# @status - need to think of the rank

# Ackermann function implementation using a stack-based approach
# Slightly modified - removed the finish action, instead we prove eventually m=0 and len=0
# Additionally removed temporal instrumentation / witness variables
# Based on the implementation in Ivy, see The Power of Temporal Prophecy Paper (unpublished)


class Nat(Expr): ...


class AckermannSystem(TransitionSystem):
    # Immutable constants and relations
    zero: Immutable[Nat]
    le: Immutable[Rel[Nat, Nat]]

    # Mutable state variables
    len: Nat
    m: Nat  # initiated arbitrarily
    n: Nat  # initiated arbitrarily
    stack: Rel[Nat, Nat]  # one of these is stack variables and the other is data

    @axiom
    def le_axioms(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        return And(
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Or(self.le(X, Y), self.le(Y, X)),
            self.le(self.zero, X),
        )

    def succ(self, n1: Nat, n2: Nat) -> BoolRef:
        Z = Nat("Z")
        return And(
            n1 != n2,
            self.le(n1, n2),
            ForAll(Z, Implies(self.le(n1, Z), Or(Z == n1, self.le(n2, Z)))),
        )

    @init
    def initial(self, X: Nat, Y: Nat) -> BoolRef:
        return And(
            Not(self.stack(X, Y)),
            self.len == self.zero,
        )

    @transition
    def step1(self, m_pop: Nat, len_pop: Nat) -> BoolRef:
        X = Nat("X")
        Y = Nat("Y")
        return And(
            # guard
            self.m == self.zero,
            self.len != self.zero,
            self.succ(len_pop, self.len),
            self.stack(len_pop, m_pop),
            # updates
            self.next.len == len_pop,
            self.stack.update({(len_pop, m_pop): false}),
            self.next.m == m_pop,
            self.succ(self.n, self.next.n),
        )

    @transition
    def step2(self) -> BoolRef:
        return And(
            # guard
            self.m != self.zero,
            self.n == self.zero,
            # updates
            self.succ(self.next.m, self.m),
            self.succ(self.zero, self.next.n),
            self.stack.unchanged(),
            self.len.unchanged(),
        )

    @transition
    def step3(self, m_push: Nat) -> BoolRef:
        X = Nat("X")
        Y = Nat("Y")
        return And(
            # guard
            self.m != self.zero,
            self.n != self.zero,
            self.succ(m_push, self.m),
            # updates
            self.stack.update({(self.len, m_push): true}),
            self.succ(self.len, self.next.len),
            self.succ(self.next.n, self.n),
            self.m.unchanged(),
        )


class AckermannProp(Prop[AckermannSystem]):
    def prop(self) -> BoolRef:
        return Not(
            G(Not(And(self.sys.m == self.sys.zero, self.sys.len == self.sys.zero)))
        )


class AckermannProof(Proof[AckermannSystem], prop=AckermannProp):

    @invariant
    def stack_bounded_by_len(self, X: Nat, Y: Nat) -> BoolRef:
        # The stack is only populated for elements smaller than len
        return Implies(self.sys.stack(X, Y), Not(self.sys.le(self.sys.len, X)))

    @invariant
    def stack_unique_per_position(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        # The stack contains at most one element on each position
        return Implies(And(self.sys.stack(X, Y), self.sys.stack(X, Z)), Y == Z)

    @invariant
    def stack_decreasing(self, X: Nat, Y: Nat, Z: Nat, W: Nat) -> BoolRef:
        # The stack is always decreasing
        return Implies(
            And(self.sys.stack(X, Y), self.sys.stack(Z, W), self.sys.le(X, Z)),
            self.sys.le(W, Y),
        )

    @invariant
    def m_bounded_by_stack(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        # m is at most the greatest value in the stack + 1
        return Implies(
            And(self.sys.stack(X, Y), Not(self.sys.le(Z, Y))),
            self.sys.le(self.sys.m, Z),
        )

    @temporal_invariant
    def never_terminate(self) -> BoolRef:
        return G(Not(And(self.sys.m == self.sys.zero, self.sys.len == self.sys.zero)))

    # Ranking: track the stack values with m in position len
    # Different idea for ranking: just hold the values in the stack - with bot < 0 < 1 < 2 < ..
    # so we track the stack such that m is in position len in the stack.

    # def stack_value_predicate(self, i: Nat, k: Nat) -> BoolRef:
    #     X = Nat("X")
    #     return Or(
    #         # counting the number of values k such that k <= stack(i)
    #         And(
    #             Exists(X, self.sys.stack(i, X)),
    #             ForAll(X, Implies(self.sys.stack(i, X), self.sys.le(k, X))),
    #         ),
    #         # m is in position len in the stack
    #         And(i == self.sys.len, self.sys.le(k, self.sys.m))
    #     )

    # def stack_position_order(self, i1: Nat, i2: Nat) -> BoolRef:
    #     return And(self.sys.le(i1, i2), i1 != i2)

    # def stack_rank(self) -> Rank:
    #     return DomainLexRank(
    #         DomainPointwiseRank.close(BinRank(self.stack_value_predicate), None),
    #         self.stack_position_order
    #     )

    def dummy_predicate(self) -> BoolRef:
        return self.sys.zero == self.sys.zero

    def rank(self) -> Rank:
        return BinRank(self.dummy_predicate)


AckermannProof().check()
