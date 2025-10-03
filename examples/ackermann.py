from inspect import stack
from prelude import *

# @status - It verifies but I'm suspicious, don't know if DomPerm is right!!

# Ackermann function implementation using a stack-based approach
# Slightly modified - removed the finish action, instead we prove eventually m=0 and len=0
# Additionally removed temporal instrumentation / witness variables
# Based on the implementation in Ivy, see The Power of Temporal Prophecy Paper (unpublished)

# The Ackermann function is defined as:
# A(0, n) = n + 1
# A(m, 0) = A(m - 1, 1)
# A(m, n) = A(m - 1, A(m, n - 1))


class Nat(Expr): ...


class StackType(Enum):
    concrete: "StackType"
    ghost: "StackType"


class AckermannSystem(TransitionSystem):
    # Immutable constants and relations
    zero: Immutable[Nat]
    lt: Immutable[Rel[Nat, Nat]]  # changed from leq to lt

    # Mutable state variables
    len: Nat
    m: Nat  # initiated arbitrarily
    n: Nat  # initiated arbitrarily
    stack: Rel[Nat, Nat]  # one of these is stack variables and the other is data

    @axiom
    def le_axioms(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
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
        return Not(
            G(Not(And(self.sys.m == self.sys.zero, self.sys.len == self.sys.zero)))
        )


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
            And(self.sys.stack(X, Y), self.sys.stack(Z, W), self.sys.lt(X, Z)),
            self.sys.lt(W, Y),
        )

    @invariant
    def m_bounded_by_stack(self, X: Nat, Y: Nat, Z: Nat) -> BoolRef:
        # m is at most the greatest value in the stack + 1
        return Implies(
            And(self.sys.stack(X, Y), self.sys.lt(Y, Z)),
            Or(self.sys.lt(self.sys.m, Z), self.sys.m == Z),
        )

    @temporal_invariant
    def never_terminate(self) -> BoolRef:
        return G(Not(And(self.sys.m == self.sys.zero, self.sys.len == self.sys.zero)))

    def position_of_m(self) -> Rank:
        return PosInOrderRank(self.sys.lt, self.sys.m)

    def position_of_n(self) -> Rank:
        return PosInOrderRank(self.sys.lt, self.sys.n)

    # this is a way more complicated one that also works? why?
    def stack_value_or_ghost(self, X: Nat, Y: Nat, T: StackType) -> BoolRef:
        m_minus_1 = Nat("m_minus_1")
        return Or(
            # usual stack values
            And(
                self.sys.stack(X, Y),
                T == StackType.concrete,
            ),
            # # n copies of Y == m - 1
            # And(
            #     self.sys.lt(X, self.sys.n),
            #     self.sys.succ(Y, self.sys.m),
            #     T == StackType.ghost,
            # ),
            # # 1 copy of Y = m - 2
            # And(
            #     Exists(
            #         m_minus_1,
            #         And(
            #             self.sys.succ(Y, m_minus_1),
            #             self.sys.succ(m_minus_1, self.sys.m),
            #         ),
            #     ),
            #     X == self.sys.zero,
            #     T == StackType.ghost,
            # ),
            # n+1 copies of Y == m - 1
            And(
                Or(self.sys.lt(X, self.sys.n), X == self.sys.n),
                self.sys.succ(Y, self.sys.m),
                T == StackType.ghost,
            ),
        )

    def finite_lemma_for_stack_value_or_ghost(
        self, X: Nat, Y: Nat, T: StackType
    ) -> BoolRef:
        return Or(
            And(
                self.sys.stack(X, Y),
                T == StackType.concrete,
            ),
            And(self.sys.lt(X, self.sys.n), T == StackType.ghost),
        )

    def stack_value_or_ghost_binary(self) -> Rank:
        return BinRank(self.stack_value_or_ghost)

    def num_appearances_of_value_or_ghost(self) -> Rank:
        return DomainPermutedRank(
            self.stack_value_or_ghost_binary(),
            ParamSpec(X=Nat, T=StackType),
            k=1,
            finite_lemma=None,
        )

    # def stack_value(self, X: Nat, Y: Nat) -> BoolRef:
    #     return self.sys.stack(X, Y)

    # def stack_value_binary(self) -> Rank:
    #     return BinRank(self.stack_value)

    # # this was verified as decreasing but this was a bug with DomPerm
    # def num_appearances_of_value(self) -> Rank:
    #     return DomainPermutedRank(
    #         self.stack_value_binary(),
    #         ParamSpec(X=Nat),
    #         k=1,
    #         finite_lemma=None,
    #     )

    def stack_appearances_lexicographically(self) -> Rank:
        return DomainLexRank(
            self.num_appearances_of_value_or_ghost(), self.sys.lt, ("Y", Nat)
        )

    def rank(self) -> Rank:
        return LexRank(
            self.stack_appearances_lexicographically(),
            self.position_of_m(),
            self.position_of_n(),
        )

    # this is intuitively close
    # Oded suggested that we consider this but for the stack "extended" with (n+1) copies of (m-1/2), but I don't know how to do that.

    # lexicographic order with the more significant being the higher values (otherwise not well-founded)
    # the intuition to use this is step1 which will "in the future" add unbounded number of values smaller than largest m
    # still why does this decrease?

    # idea: when m!=0 and n!=0 the next thing we will do is step3, pushing m-1 to stack and n=n-1
    # so we can think of the stack as having n copies of m-1 (because that's what's going to happen)
    # then implcilty step 3 doesn't do anything, but decreases n so good.
    # should we also include the current m in position len?

    # step 2 is simple, it just decreases m and increases n and doesn't touch the stack,
    # but it will implicitly change the stack because of the above, adding one copy of (new) m-1 -- increasing rank.

    # step 1

    # if we consider a rank that is based only on m,n and the number of times each value appears in the stack *including* m itself then it can't capture this.
    # because the second and fourth state are equivalent based on those measures. -> m itself shouldn't be in the stack

    # consider this sequence of steps:

    # stack = [4, 3, 2, 1, 0] m=0 n=2 ghost: [4,3,2,1,0]
    # step1
    # stack = [4, 3, 2, 1] m=0 n=2 ghost: [4,3,2,1]
    # step1
    # stack = [4, 3, 2] m=1 n=3 ghost: [4,3,2,0,0,0]
    # step3
    # stack = [4, 3, 2, 0] m=1 n=2 ghost: [4,3,2,0,0,0]
    # step3
    # stack = [4, 3, 2, 0, 0] m=1 n=1 ghost: [4,3,2,0,0,0]
    # step 3
    # stack = [4, 3, 2, 0, 0, 0] m=1 n=0 ghost: [4,3,2,0,0,0]
    # step 2
    # stack = [4, 3, 2, 0, 0, 0] m=0 n=1 ghost: [4,3,2,0,0,0]

    # what happens in a case of step 2 with m!=1
    #
    # stack = [5, 5, 5, 5, 5] m=6 n=0: [5, 5, 5, 5, 5]
    # step2
    # stack = [5, 5, 5, 5, 5] m=5 n=1 ghost: [5, 5, 5, 5, 5, 4]
    # problematic
    # but maybe this is why oded wanted n+1
    # becuase then its
    # stack = [5, 5, 5, 5, 5] m=6 n=0: [5, 5, 5, 5, 5, 5]
    # step2
    # stack = [5, 5, 5, 5, 5] m=5 n=1 ghost: [5, 5, 5, 5, 5, 4, 4]

    # idea: n copies of m and 1 copy of m-1??
    # then its
    # stack = [5, 5, 5, 5, 5] m=6 n=0: ghost: [5, 5, 5, 5, 5, 4]
    # step2
    # stack = [5, 5, 5, 5, 5] m=5 n=1 ghost: [5, 5, 5, 5, 5, 4]

    # so my final idea currently
    # number of appearances in stack lexicographically, including n+1 copies of m-1. then m, then n
    # step 3 decreases n, doesn't change m or stack
    # step 2 decreases stack, m.
    # step 1 decreases stack
    # a bit strange because most clean would be step 3 decreases n, step 2 decreases m, step 1 decreases stack

    # how to implement this n+1 copies of m:
    # probably need DomPerm with the enum like we did for the complex dijkstra ones.


AckermannProof().check()
