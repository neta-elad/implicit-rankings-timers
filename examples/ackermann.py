"""
Stack-based implementation of the Ackermann function

Based on the implementation in Ivy, see The Power of Temporal Prophecy Paper (unpublished)
with removed temporal instrumentation / witness variables, except for m_init.

Stack-based implementation of the Ackermann function due to:
Dershowitz, N., Manna, Z.: Proving termination with multiset orderings. Commun.
ACM 22(8), 465–476 (Aug 1979), https://doi.org/10.1145/359138.359142

The Ackermann function is defined as:
A(0, n) = n + 1
A(m, 0) = A(m - 1, 1)
A(m, n) = A(m - 1, A(m, n - 1))
"""

# @status - done (except for wf check for order - simple)

from prelude import *


class Nat(Expr): ...


class AckermannSystem(TransitionSystem):
    zero: Immutable[Nat]
    lt: Immutable[
        WFRel[Nat]
    ]  # changed from <= to < but we can change back, it wasn't important

    len: Nat
    m: Nat
    n: Nat
    stack: Rel[Nat, Nat]  # one of these is stack index and the other is data
    started: Bool
    finished: Bool

    m_init: Nat  # ghost for what the value of m is at the start

    @axiom
    def lt_axioms(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        return And(
            Implies(And(self.lt(X, Y), self.lt(Y, Z)), self.lt(X, Z)),
            Implies(And(self.lt(X, Y), self.lt(Y, X)), false),
            Or(self.lt(X, Y), self.lt(Y, X), X == Y),
            Or(self.lt(self.zero, X), X == self.zero),
        )

    def succ(self, n1: Nat, n2: Nat) -> BoolRef:
        Z = Nat("Z")
        return And(
            self.lt(n1, n2),
            ForAll(Z, Implies(self.lt(n1, Z), Or(Z == n2, self.lt(n2, Z)))),
        )

    @init
    def initial(self, X: Nat, Y: Nat) -> BoolRef:
        return And(
            Not(self.stack(X, Y)),
            self.len == self.zero,
            self.m == self.zero,
            self.m_init == self.zero,
            self.n == self.zero,
            self.started == false,
            self.finished == false,
        )

    @transition
    def setup_m(self) -> BoolRef:
        return And(
            Not(self.started),
            self.succ(self.m, self.next.m),
            self.n.unchanged(),
            self.stack.unchanged(),
            self.len.unchanged(),
            self.started.unchanged(),
            self.finished.unchanged(),
            self.m_init.unchanged(),
        )

    @transition
    def setup_n(self) -> BoolRef:
        return And(
            Not(self.started),
            self.succ(self.n, self.next.n),
            self.m.unchanged(),
            self.stack.unchanged(),
            self.len.unchanged(),
            self.started.unchanged(),
            self.finished.unchanged(),
            self.m_init.unchanged(),
        )

    @transition
    def start(self) -> BoolRef:
        return And(
            Not(self.started),
            self.started.update(true),
            self.m.unchanged(),
            self.n.unchanged(),
            self.stack.unchanged(),
            self.len.unchanged(),
            self.finished.unchanged(),
            self.m_init.update(self.m),
        )

    def finish(self) -> BoolRef:
        return And(
            self.started,
            self.m == self.zero,
            self.len == self.zero,
            self.finished.update(true),
            self.started.unchanged(),
            self.m.unchanged(),
            self.n.unchanged(),
            self.stack.unchanged(),
            self.len.unchanged(),
            self.m_init.unchanged(),
        )

    @transition
    def step1(self, m_pop: Nat, len_pop: Nat) -> BoolRef:
        return And(
            self.started,
            self.m == self.zero,
            self.len != self.zero,
            self.succ(len_pop, self.len),
            self.stack(len_pop, m_pop),
            self.next.len == len_pop,
            self.stack.update({(len_pop, m_pop): false}),
            self.next.m == m_pop,
            self.succ(self.n, self.next.n),
            self.started.unchanged(),
            self.finished.unchanged(),
            self.m_init.unchanged(),
        )

    @transition
    def step2(self) -> BoolRef:
        return And(
            self.started,
            self.m != self.zero,
            self.n == self.zero,
            self.succ(self.next.m, self.m),
            self.succ(self.zero, self.next.n),
            self.stack.unchanged(),
            self.len.unchanged(),
            self.started.unchanged(),
            self.finished.unchanged(),
            self.m_init.unchanged(),
        )

    @transition
    def step3(self, m_push: Nat) -> BoolRef:
        return And(
            self.started,
            self.m != self.zero,
            self.n != self.zero,
            self.succ(m_push, self.m),
            self.stack.update({(self.len, m_push): true}),
            self.succ(self.len, self.next.len),
            self.succ(self.next.n, self.n),
            self.m.unchanged(),
            self.started.unchanged(),
            self.finished.unchanged(),
            self.m_init.unchanged(),
        )


class AckermannProp(Prop[AckermannSystem]):
    def prop(self) -> BoolRef:
        return Implies(F(self.sys.started), F(self.sys.finished))


class AckermannProof(Proof[AckermannSystem], prop=AckermannProp):

    @temporal_invariant
    def never_finished(self) -> BoolRef:
        return G(Not(self.sys.finished))

    @temporal_invariant
    def eventually_started(self) -> BoolRef:
        return F(self.sys.started)

    @invariant
    def stack_bounded_by_len(self, X: Nat, Y: Nat) -> BoolRef:
        return Implies(self.sys.stack(X, Y), self.sys.lt(X, self.sys.len))

    @invariant
    def stack_unique_per_position(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        return Implies(And(self.sys.stack(X, Y), self.sys.stack(X, Z)), Y == Z)

    @invariant
    def stack_decreasing(self, X: Nat, Y: Nat, Z: Nat, W: Nat) -> BoolRef:
        return Implies(
            And(
                self.sys.stack(X, Y),
                self.sys.stack(Z, W),
                Or(self.sys.lt(X, Z), X == Z),
            ),
            Or(self.sys.lt(W, Y), W == Y),
        )

    @invariant
    def m_bounded_by_stack(self, I: Nat, M: Nat, X: Nat) -> BoolRef:
        return Implies(
            And(self.sys.stack(I, M), self.sys.lt(M, X)),
            Or(self.sys.lt(self.sys.m, X), self.sys.m == X),
        )

    @invariant
    def len_zero_when_not_started(self) -> BoolRef:
        return Implies(Not(self.sys.started), self.sys.len == self.sys.zero)

    @invariant
    def m_bounded_by_m_init(self) -> BoolRef:
        return Implies(
            self.sys.started,
            Or(self.sys.lt(self.sys.m, self.sys.m_init), self.sys.m == self.sys.m_init),
        )

    @invariant
    def stack_bounded_by_m_init(self, I: Nat, M: Nat) -> BoolRef:
        return Implies(
            self.sys.stack(I, M),
            Or(self.sys.lt(M, self.sys.m_init), M == self.sys.m_init),
        )

    def timer_rank_start(self) -> Rank:
        return self.timer_rank(self.sys.started, None, None)

    # rank based on  "Proving Termination with Multiset Orderings" by Manna and Dershovitz.
    # rank = {(s_k + 1, 0), (s_k-1 + 1, 0) ..... (S_2 + 1, 0), (y,z)} multiset
    # equivalently: {stack_values x {0} union (m-1,n)}

    def stack_value_and_zero_pair(self, index: Nat, a: Nat, b: Nat) -> BoolRef:
        return And(self.sys.stack(index, a), b == self.sys.zero)

    def m_minus_one_and_n_pair(self, index: Nat, a: Nat, b: Nat) -> BoolRef:
        return And(
            index
            == self.sys.len,  # appears once, so we counts it only for len (which can't be a stack index)
            self.sys.succ(a, self.sys.m),  # a is m-1
            b == self.sys.n,  # b is n
        )

    def any_pair(self, index: Nat, a: Nat, b: Nat) -> BoolRef:
        return Or(
            self.stack_value_and_zero_pair(index, a, b),
            self.m_minus_one_and_n_pair(index, a, b),
        )

    def finiteness_lemma_for_index(self, index: Nat, a: Nat, b: Nat) -> BoolRef:
        return Or(
            And(
                self.sys.stack(index, a),
                b == self.sys.zero,
                self.sys.lt(index, self.sys.len),
            ),
            And(
                index == self.sys.len,
                self.sys.lt(a, self.sys.m),
                Or(self.sys.lt(b, self.sys.n), b == self.sys.n),
            ),
        )

    def number_of_pairs(self) -> Rank:
        return DomainPointwiseRank(
            BinRank(self.any_pair),
            ParamSpec(index=Nat),
            FiniteLemma(self.finiteness_lemma_for_index),
        )

    def finiteness_lemma_for_a_and_b(self, a: Nat, b: Nat) -> BoolRef:
        return Or(
            And(
                Or(
                    self.sys.lt(a, self.sys.m_init),
                    a == self.sys.m_init,
                    a == self.sys.m,
                    self.sys.lt(a, self.sys.m),
                ),
                b == self.sys.zero,
            ),
            And(self.sys.succ(a, self.sys.m), b == self.sys.n),
        )

    def multiset_rank(self) -> Rank:
        return DomainLexRank(
            self.number_of_pairs(),
            LexOrder(a=self.sys.lt, b=self.sys.lt),
            FiniteLemma(self.finiteness_lemma_for_a_and_b, m=2),
        )

    def rank(self) -> Rank:
        return LexRank(
            self.timer_rank_start(),
            self.multiset_rank(),
        )

    # alternative idea for a proof: with DomLex over Nat and not Nat*Nat,
    # Oded suggested that we consider this but for the stack "extended" with (n+1) copies of (m-1/2), but I don't know how to do that.
    # lexicographic order with the more significant being the higher values (otherwise not well-founded)
    # the intuition to use this is step1 which will "in the future" add unbounded number of values smaller than largest m

    # number of appearances in stack lexicographically, including n+1 copies of m-1. then m, then n (alternative that might also work: n copies of m and 1 copy of m-1)
    # A(0, n) = n + 1 -- step 1 decreases stack
    # A(m, 0) = A(m - 1, 1) -- step 2 decreases stack, m.
    # A(m, n) = A(m - 1, A(m, n - 1)) -- step 3 decreases n, doesn't change m or stack

    # examples:
    # stack=[3,3,3,2,1] m=0 n=2
    # step1
    # stack=[3,3,3,2] m=1 n=3 ghost stack = [3,3,3,2]+[0,0,0,0]
    # decreases in the stack is witness by the decrease in value 1 (increase in value 0)
    # the decrease is witnessed pointwise (i think) - no permutations needed.
    #
    # stack=[3,3,3,2] m=1 n=3 ghost stack = [3,3,3,2]+[0,0,0,0]
    # step3
    # stack=[3,3,3,2,0] m=1 n=2 ghost stack = [3,3,3,2,0]+[0,0,0]
    # stack is conserved
    # witnessed by conserved in all values
    # in the value 0, there is a permutation between a ghost value n=3 and concrete value x=len-1
    #
    # stack=[3,3,3,2] m=3 n=0 ghost stack = [3,3,3,2]+[2]
    # step2
    # stack=[3,3,3,2] m=2 n=1 ghost stack = [3,3,3,2]+[1,1]
    # decrease in stack (and in m)
    # the decrease is witnessed in value 2 pointwise

    # def position_of_m(self) -> Rank:
    #     return PosInOrderRank(self.sys.m, self.sys.lt)

    # def position_of_n(self) -> Rank:
    #     return PosInOrderRank(self.sys.n, self.sys.lt)

    # def stack_value_or_ghost(self, X: Nat, Y: Nat, T: StackType) -> BoolRef:
    #     # m_minus_1 = Nat("m_minus_1")
    #     return Or(
    #         # usual stack values
    #         And(
    #             self.sys.stack(X, Y),
    #             T == StackType.concrete,
    #         ),
    #         # n+1 copies of Y == m - 1
    #         And(
    #             Or(self.sys.lt(X, self.sys.n), X == self.sys.n),
    #             self.sys.succ(Y, self.sys.m),
    #             T == StackType.ghost,
    #         ),
    #         # # n copies of Y == m - 1
    #         # And(
    #         #     self.sys.lt(X, self.sys.n),
    #         #     self.sys.succ(Y, self.sys.m),
    #         #     T == StackType.ghost,
    #         # ),
    #         # # 1 copy of Y = m - 2
    #         # And(
    #         #     Exists(
    #         #         m_minus_1,
    #         #         And(
    #         #             self.sys.succ(Y, m_minus_1),
    #         #             self.sys.succ(m_minus_1, self.sys.m),
    #         #         ),
    #         #     ),
    #         #     X == self.sys.zero,
    #         #     T == StackType.ghost,
    #         # ),
    #     )

    # def finite_lemma_for_stack_value_or_ghost(
    #     self, X: Nat, Y: Nat, T: StackType
    # ) -> BoolRef:
    #     return Or(
    #         And(
    #             self.sys.stack(X, Y),
    #             T == StackType.concrete,
    #         ),
    #         And(self.sys.lt(X, self.sys.n), T == StackType.ghost),
    #     )

    # def stack_value_or_ghost_binary(self) -> Rank:
    #     return BinRank(self.stack_value_or_ghost)

    # def num_appearances_of_value_or_ghost(self) -> Rank:
    #     conserved_hints = [
    #         (
    #             # permute discussed above
    #             [{"X": self.sys.n, "T": StackType.ghost}],
    #             [{"X": self.sys.len_minus_1, "T": StackType.concrete}],
    #         ),
    #         (
    #             # no permute
    #             [{"X": self.sys.n, "T": StackType.concrete}],
    #             [{"X": self.sys.n, "T": StackType.concrete}],
    #         ),
    #     ]
    #     # decrease_hints = [
    #     #     (
    #     #         [{"i": self.sys.node1}],
    #     #         [{"i": self.sys.node2}],
    #     #         {"i": self.sys.node3},
    #     #     )
    #     # ]
    #     return DomainPermutedRank(
    #         self.stack_value_or_ghost_binary(),
    #         ParamSpec(X=Nat, T=StackType),
    #         k=1,
    #         finite_lemma=None,
    #         conserved_hints=conserved_hints,
    #     )

    # def stack_appearances_lexicographically(self) -> Rank:
    #     return DomainLexRank(
    #         # maybe we need here the reverse ordering?
    #         self.num_appearances_of_value_or_ghost(),
    #     )

    # def rank(self) -> Rank:
    #     return self.stack_appearances_lexicographically()
    #     LexRank(
    #         self.stack_appearances_lexicographically(),
    #         # self.position_of_m(),
    #         # self.position_of_n(),
    #     )


AckermannProof().check()
