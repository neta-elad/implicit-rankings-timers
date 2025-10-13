from inspect import stack
from prelude import *

# @status - done, except for soundness which we put away for now

# Ackermann function implementation using a stack-based approach
# Slightly modified - removed the finish action, instead we prove termination
# Additionally removed temporal instrumentation / witness variables
# Based on the implementation in Ivy, see The Power of Temporal Prophecy Paper (unpublished)

# The Ackermann function is defined as:
# A(0, n) = n + 1
# A(m, 0) = A(m - 1, 1)
# A(m, n) = A(m - 1, A(m, n - 1))


class Nat(Expr): ...


# class StackType(Enum):
#     concrete: "StackType"
#     ghost: "StackType"


class AckermannSystem(TransitionSystem):
    zero: Immutable[Nat]
    lt: Immutable[WFRel[Nat]]

    len: Nat
    m: Nat  # initiated arbitrarily
    n: Nat  # initiated arbitrarily
    stack: Rel[Nat, Nat]  # one of these is stack variables and the other is data

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
        )

    @transition
    def step1(self, m_pop: Nat, len_pop: Nat) -> BoolRef:
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
        return false


class AckermannProof(Proof[AckermannSystem], prop=AckermannProp):

    @invariant
    def stack_bounded_by_len(self, X: Nat, Y: Nat) -> BoolRef:
        # The stack is only populated for elements smaller than len
        return Implies(self.sys.stack(X, Y), self.sys.lt(X, self.sys.len))

    @invariant
    def stack_unique_per_position(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        # The stack contains at most one element on each position
        return Implies(And(self.sys.stack(X, Y), self.sys.stack(X, Z)), Y == Z)

    @invariant
    def stack_decreasing(self, X: Nat, Y: Nat, Z: Nat, W: Nat) -> BoolRef:
        # The stack is always decreasing
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
        # m is at most the greatest value in the stack + 1
        return Implies(
            And(self.sys.stack(I, M), self.sys.lt(M, X)),
            Or(self.sys.lt(self.sys.m, X), self.sys.m == X),
        )

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

    def number_of_pairs(self) -> Rank:
        return DomainPointwiseRank(
            BinRank(self.any_pair),
            ParamSpec(index=Nat),
            None,  # we need one - TODO
            None,  # maybe need hints
        )

    def nat_times_nat_lex_order(self, a1: Nat, b1: Nat, a2: Nat, b2: Nat) -> BoolRef:
        return Or(
            self.sys.lt(a1, a2),
            And(a1 == a2, self.sys.lt(b1, b2)),
        )

    def multiset_rank(self) -> Rank:
        return DomainLexRank(
            self.number_of_pairs(),
            self.nat_times_nat_lex_order,
        )

    def rank(self) -> Rank:
        return self.multiset_rank()

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
print(AckermannProof().rank().size)
