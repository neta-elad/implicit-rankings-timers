from prelude import *

# @status - inv fails

# Toy stabilization example from the paper Implicit Rankings for Verification of Liveness Properties in First-Order Logic / Raz Lotan & Sharon Shoham
# Inspired by Dijsktra's k-state self-stabilization algorithm.


class Node(Finite): ...


class ToyStabilizationSystem(TransitionSystem):
    top: Immutable[Node]
    leq: Immutable[Rel[Node, Node]]
    next_node: Immutable[Fun[Node, Node]]
    sched: Node

    token: Rel[Node]
    scheduled: Rel[Node]

    def succ_node(self, u: Node, v: Node) -> BoolRef:
        # ring successor
        W = Node("W")
        return Or(
            ForAll(W, And(self.leq(v, W), self.leq(W, u))),
            And(u != v, self.leq(u, v), ForAll(W, Or(self.leq(v, W), self.leq(W, u)))),
        )

    @axiom
    def axiom_leq_node(self, X: Node, Y: Node, Z: Node) -> BoolRef:
        return And(
            Implies(And(self.leq(X, Y), self.leq(Y, Z)), self.leq(X, Z)),
            Implies(And(self.leq(X, Y), self.leq(Y, X)), X == Y),
            Or(self.leq(X, Y), self.leq(Y, X)),
            self.leq(X, self.top),
            self.succ_node(X, self.next_node(X)),
        )

    @init
    def initial(self) -> BoolRef:
        N = Node("N")
        return Exists(N, self.token(N))

    @transition
    def wakeup(self, n: Node) -> BoolRef:
        N = Node("N")
        return And(
            n == self.sched,
            ForAll(N, self.scheduled(N) == (N == n)),
            If(
                self.token(n),
                And(
                    self.token.update({(n,): false, (self.next_node(n),): true}),
                ),
                And(self.token.unchanged()),
            ),
        )


class ToyStabilizationProperty(Prop[ToyStabilizationSystem]):
    # The property we want to prove -- if infinitely often a node with a token moves then eventually top moves
    def prop(self) -> BoolRef:
        X = Node("X")
        return Implies(
            G(
                F(
                    Implies(
                        Exists(X, self.sys.token(X)),
                        # ForAll(X, Implies(self.sys.scheduled(X), self.sys.token(X))),
                        self.sys.token(self.sys.sched),
                    )
                )
            ),
            # F(self.sys.scheduled(self.sys.top)),
            F(self.sys.sched == self.sys.top),
        )


class ToyStabilizationProof(
    Proof[ToyStabilizationSystem], prop=ToyStabilizationProperty
):
    @temporal_invariant
    def token_scheduling(self) -> BoolRef:
        X = Node("X")
        return G(
            F(
                Implies(
                    Exists(X, self.sys.token(X)),
                    # ForAll(X, Implies(self.sys.scheduled(X), self.sys.token(X))),
                    self.sys.token(self.sys.sched),
                )
            )
        )

    @temporal_invariant
    def top_unscheduled(self) -> BoolRef:
        # return G(Not(self.sys.scheduled(self.sys.top)))
        return G(self.sys.sched != self.sys.top)  # todo: better nnf

    @invariant
    def exists_token(self) -> BoolRef:
        X = Node("X")
        return Exists(X, self.sys.token(X))

    def j_counts_towards_i(self, i: Node, j: Node) -> BoolRef:
        return And(self.sys.token(i), self.sys.leq(i, j), i != j)

    def binary_rank_ij(self) -> Rank:
        return BinRank(self.j_counts_towards_i)

    # def i(self, i: Node) -> Node:
    #     return i

    def sum_over_j(self) -> Rank:
        hints = [{"j": self.sys.sched}]
        return DomainPointwiseRank(
            self.binary_rank_ij(),
            ParamSpec(j=Node),
            None,
            hints,
        )

    # @witness
    # def sched(self, T: Node) -> BoolRef:
    #     return self.sys.scheduled(T)

    def sum_over_i(self) -> Rank:
        conserved_hint = [
            ([{"i": self.sys.sched}], [{"i": self.sys.sched}]),
            ([{"i": self.sys.sched}], [{"i": self.sys.next_node(self.sys.sched)}])
        ]
        decreases_hint = [
            (
                [{"i": self.sys.sched}],
                [{"i": self.sys.next_node(self.sys.sched)}],
                {"i": self.sys.sched},
            )
        ]
        return DomainPermutedRank(
            self.sum_over_j(),
            ParamSpec(i=Node),
            1,
            None,
            conserved_hint,
            decreases_hint,
        )

    def scheduling_of_token(self) -> BoolRef:
        X = Node("X")
        return Implies(
            Exists(X, self.sys.token(X)),
            # ForAll(X, Implies(self.sys.scheduled(X), self.sys.token(X))),
            self.sys.token(self.sys.sched),
        )

    def scheduling_of_token_timer_rank(self) -> Rank:
        return self.timer_rank(self.scheduling_of_token, None, None)

    def rank(self) -> Rank:
        # return LexRank(self.sum_over_i(), self.scheduling_of_token_timer_rank())
        return self.sum_over_i()


ToyStabilizationProof().check()
