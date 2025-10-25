"""
Leader Election in a Ring, due to Chang and Roberts
Chang, E.J.H., Roberts, R.: An improved algorithm for decentralized extrema-finding in circular configurations of processes.
Commun. ACM 22(5), 281–283 (1979), https://doi.org/10.1145/359104.359108

We based our modeling and invariants on:
Feldman, Y.M.Y., Padon, O., Immerman, N., Sagiv, M., Shoham, S.:
Bounded quantifier instantiation for checking inductive invariants.
Log. Methods Comput. Sci. 15(3) (2019), https://doi.org/10.23638/LMCS-15(3:18)2019
"""

# @status - done

from prelude import *


class Node(Finite): ...


class Id(Expr): ...


class RingLeader(TransitionSystem):
    btw: Immutable[Rel[Node, Node, Node]]
    le: Immutable[Rel[Id, Id]]
    id: Immutable[Fun[Node, Id]]
    max: Immutable[Node]

    leader: Rel[Node]
    pending: Rel[Id, Node]
    sent_own: Rel[Node]
    scheduled: Rel[Node]

    @axiom
    def btw_axioms(self, X: Node, Y: Node, Z: Node, W: Node) -> BoolRef:
        return And(
            # characterising axioms of the btw relation
            Implies(And(self.btw(W, X, Y), self.btw(W, Y, Z)), self.btw(W, X, Z)),
            Implies(self.btw(W, X, Y), Not(self.btw(W, Y, X))),
            Or(self.btw(W, X, Y), self.btw(W, Y, X), W == X, W == Y, X == Y),
            Implies(self.btw(X, Y, Z), self.btw(Y, Z, X)),
        )

    @axiom
    def le_axioms(self, A: Id, B: Id, C: Id) -> BoolRef:
        return And(
            Implies(And(self.le(A, B), self.le(B, A)), A == B),
            Implies(And(self.le(A, B), self.le(B, C)), self.le(A, C)),
            Or(self.le(A, B), self.le(B, A)),
        )

    @axiom
    def unique_ids(self, X: Node, Y: Node) -> BoolRef:
        return And(Implies(self.id(X) == self.id(Y), X == Y))

    @axiom
    def max_node(self, X: Node) -> BoolRef:
        return self.le(self.id(X), self.id(self.max))

    @init
    def initial(self, A: Id, X: Node) -> BoolRef:
        return And(
            self.leader(X) == False,
            self.pending(A, X) == False,
            self.sent_own(X) == False,
        )

    @transition
    def wakeup(self, n: Node, succ: Node) -> BoolRef:
        N = Node("N")
        Z = Node("Z")
        A = Id("A")
        B = Id("B")
        return And(
            ForAll(N, self.scheduled(N) == (N == n)),
            n != succ,
            ForAll(Z, Or(self.btw(n, succ, Z), Z == n, Z == succ)),
            If(
                self.sent_own(n),
                If(
                    ForAll(A, Not(self.pending(A, n))),
                    # already sent own and no pending messages -> skip
                    And(
                        self.leader.unchanged(),
                        self.sent_own.unchanged(),
                        self.pending.unchanged(),
                    ),
                    # there is a pending message - process message B
                    Exists(
                        B,
                        And(
                            self.pending(B, n),
                            If(
                                B == self.id(n),
                                # B is the same as n's id -> elect n as leader
                                And(
                                    self.leader.update({(n,): true}),
                                    self.sent_own.unchanged(),
                                    self.pending.update({(B, n): false}),
                                ),
                                If(
                                    self.le(self.id(n), B),
                                    # B is higher - pass forward
                                    And(
                                        self.leader.unchanged(),
                                        self.sent_own.unchanged(),
                                        self.pending.update(
                                            {(B, n): false, (B, succ): true}
                                        ),
                                    ),
                                    # B is lower - drop
                                    And(
                                        self.leader.unchanged(),
                                        self.sent_own.unchanged(),
                                        self.pending.update({(B, n): false}),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
                # yet to send own id
                And(
                    self.leader.unchanged(),
                    self.sent_own.update({(n,): true}),
                    self.pending.update({(self.id(n), succ): true}),
                ),
            ),
        )


class RingLeaderProp(Prop[RingLeader]):
    def prop(self) -> BoolRef:
        N = Node("N")
        return Implies(
            ForAll(N, G(F(self.sys.scheduled(N)))),
            Exists(N, F(self.sys.leader(N))),
        )


class RingLeaderProof(Proof[RingLeader], prop=RingLeaderProp):

    @temporal_invariant
    def scheduling(self, N: Node) -> BoolRef:
        return G(F(self.sys.scheduled(N)))

    @temporal_invariant
    def no_leader(self, N: Node) -> BoolRef:
        return G(Not(self.sys.leader(N)))

    @invariant
    # simpler way to say whats needed for conserved of rank
    def pending_ids_less_than_max(self, A: Id, N: Node) -> BoolRef:
        return Implies(
            self.sys.pending(A, N), self.sys.le(A, self.sys.id(self.sys.max))
        )

    @invariant
    def max_id_always_in_ring(self) -> BoolRef:
        N = Node("N")
        return Or(
            self.sys.leader(self.sys.max),
            Not(self.sys.sent_own(self.sys.max)),
            Exists(N, self.sys.pending(self.sys.id(self.sys.max), N)),
        )

    def not_sent_own(self, n: Node) -> BoolRef:
        return Not(self.sys.sent_own(n))

    def set_of_not_sent_own(self) -> Rank:
        return DomainPointwiseRank(BinRank(self.not_sent_own), ParamSpec(n=Node), None)

    def pending_id(self, A: Id, n: Node) -> BoolRef:
        return self.sys.pending(A, n)

    def finiteness_lemma_for_id(self, A: Id, n: Node) -> BoolRef:
        N = Node("N")
        return Exists(N, self.sys.pending(A, N))

    def set_of_pending_ids(self) -> Rank:
        return DomainPointwiseRank(
            BinRank(self.pending_id),
            ParamSpec(A=Id),
            FiniteLemma(self.finiteness_lemma_for_id),
        )

    def lt_max_minimal(self, n1: Node, n2: Node) -> BoolRef:
        return Or(
            And(
                n1 == self.sys.max,
                n2 != self.sys.max,
            ),
            self.sys.btw(self.sys.max, n2, n1),
        )

    def rank_agg_n2(self) -> Rank:
        return DomainLexRank(self.set_of_pending_ids(), self.lt_max_minimal)

    def rank_bin_sent_max(self) -> Rank:
        return BinRank(Not(self.sys.sent_own(self.sys.max)))

    def scheduling_helpful(self, N: Node) -> BoolRef:
        A = Id("A")
        return Or(Not(self.sys.sent_own(N)), Exists(A, self.sys.pending(A, N)))

    def scheduled(self, N: Node) -> BoolRef:
        return self.sys.scheduled(N)

    def scheduling_rank(self) -> Rank:
        return self.timer_rank(self.scheduled, self.scheduling_helpful, None)

    def rank(self) -> Rank:
        return LexRank(
            self.set_of_not_sent_own(),
            self.rank_bin_sent_max(),
            self.rank_agg_n2(),
            self.scheduling_rank(),
        )


RingLeaderProof().check()
