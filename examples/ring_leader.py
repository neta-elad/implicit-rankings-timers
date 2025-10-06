from prelude import *

# @status - rank too complex to work, maybe go back to DomLex rank


# Leader Election in a Ring, due to Chang and Roberts
# Chang, E.J.H., Roberts, R.: An improved algorithm for decentralized extremafinding in circular configurations of processes.
# Commun. ACM 22(5), 281–283 (1979), https://doi.org/10.1145/359104.359108
# we based our modeling and invariants on
# Feldman, Y.M.Y., Padon, O., Immerman, N., Sagiv, M., Shoham, S.:
# Bounded quantifier instantiation for checking inductive invariants.
# Log. Methods Comput. Sci. 15(3) (2019), https://doi.org/10.23638/LMCS-15(3:18)2019


class Node(Finite): ...


class Id(Expr): ...


class RingLeader(TransitionSystem):

    btw: Immutable[Rel[Node, Node, Node]]
    le: Immutable[Rel[Id, Id]]
    id: Immutable[Fun[Node, Id]]

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
            F(Exists(N, self.sys.leader(N))),
        )


class RingLeaderProof(Proof[RingLeader], prop=RingLeaderProp):

    # @invariant
    def safety(self, X: Node, Y: Node) -> BoolRef:
        return Implies(And(self.sys.leader(X), self.sys.leader(Y)), X == Y)

    # @invariant
    def leader_max(self, X: Node, Y: Node) -> BoolRef:
        return Implies(self.sys.leader(X), self.sys.le(self.sys.id(Y), self.sys.id(X)))

    # @invariant
    def self_pending_highest_id(self, X: Node, Y: Node) -> BoolRef:
        return Implies(
            self.sys.pending(self.sys.id(X), X),
            self.sys.le(self.sys.id(Y), self.sys.id(X)),
        )

    # @invariant
    def no_bypass(self, X: Node, Y: Node, Z: Node) -> BoolRef:
        return Implies(
            And(self.sys.pending(self.sys.id(X), Y), self.sys.btw(X, Z, Y)),
            self.sys.le(self.sys.id(Z), self.sys.id(X)),
        )

    @invariant
    def pending_sent_own(self, X: Node, Y: Node) -> BoolRef:
        return Implies(self.sys.pending(self.sys.id(X), Y), self.sys.sent_own(X))

    @invariant
    def pending_ids(self, A: Id, X: Node) -> BoolRef:
        Y = Node("Y")
        return ForAll(
            [A, X], Implies(self.sys.pending(A, X), Exists(Y, self.sys.id(Y) == A))
        )

    def no_leader_then_to_send(self) -> BoolRef:
        X = Node("X")
        Y = Node("Y")
        return Or(
            Exists(X, self.sys.leader(X)),
            Exists(X, Not(self.sys.sent_own(X))),
            Exists([X, Y], self.sys.pending(self.sys.id(Y), X)),
        )

    @invariant
    def not_leader_then_pending(self, X: Node) -> BoolRef:
        Y = Node("Y")
        return Implies(
            And(self.sys.sent_own(X), Not(self.sys.leader(X))),
            # quantifier alteration that is hard
            Exists(
                Y,
                Or(
                    Not(self.sys.le(self.sys.id(Y), self.sys.id(X))),
                    self.sys.pending(self.sys.id(X), Y),
                ),
            ),
        )

    @temporal_invariant
    def scheduling(self, N: Node) -> BoolRef:
        return G(F(self.sys.scheduled(N)))

    @temporal_invariant
    def no_leader(self) -> BoolRef:
        N = Node("N")
        return G(ForAll(N, Not(self.sys.leader(N))))

    # the ranking we had before is kind of problematic because it uses DomLex with 2 parameters, which we don't have
    # but it was also not so intuitive, we can find something more intuitive with DomPerm or DomPW
    # for every Id how many nodes does it have to go through
    # but also we need total number of ids in the ring i think maybe not?

    def not_sent_own(self, N: Node) -> BoolRef:
        return Not(self.sys.sent_own(N))

    def set_not_sent_own(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.not_sent_own), None)

    # def id_of_node_in_ring(self, N: Node) -> BoolRef:
    #     X = Node("X")
    #     return Exists(X, self.sys.pending(self.sys.id(N), X))
    # def set_of_ids(self) -> Rank:
    #     return DomainPointwiseRank.close(BinRank(self.id_of_node_in_ring), None)

    # when we further aggregate over this, it will count the total distance all messages would need to go
    # assuming no messages are ever dropped (even rightfully) which is just an upper bound
    def node_might_process_id(self, M: Node, N: Node) -> BoolRef:
        # Node N is between a node X that holds node M's id and M
        X = Node("X")
        return Exists(
            X, And(self.sys.pending(self.sys.id(M), X), self.sys.btw(X, N, M))
        )

    def all_distances(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.node_might_process_id), None)

    # scheduling timers

    def scheduled(self, N: Node) -> BoolRef:
        return self.sys.scheduled(N)

    def scheduling_helpful(self, N: Node) -> BoolRef:
        X = Node("X")
        return Or(
            Not(self.sys.sent_own(N)), Exists(X, self.sys.pending(self.sys.id(X), N))
        )

    def scheduling_rank(self) -> Rank:
        return self.timer_rank(self.scheduled, self.scheduling_helpful, None)

    # final rank
    # currently seems to be too complex to work, and the hints are complex as well.
    def rank(self) -> Rank:
        return LexRank(
            self.set_not_sent_own(),
            self.all_distances(),
            # self.set_of_ids(),
            # self.scheduling_rank(),
        )

    # extracting an order from the ring structure, such that max is maximal.
    # less_btw_n2_by_max = lambda sym, param1, param2: Or(
    #     sym["btw"](param1["n2"], param2["n2"], sym["max"]),
    #     And(param2["n2"] == sym["max"], param1["n2"] != sym["max"]),
    # )
    # rank_bin_pending = BinaryFreeRank(pred_pending_n1n2, n1n2_dict)
    # rank_agg_pending = ParPointwiseFreeRank(
    #     rank_bin_pending, {"n1": Node}, n2_dict
    # )  # n2 is still free
    # rank_bin_sent_n2 = BinaryFreeRank(pred_sent_n2, n2_dict)
    # rank_n2 = LexFreeRank([rank_bin_sent_n2, rank_agg_pending], n2_dict)
    # rank_agg_n2 = ParLexFreeRank(rank_n2, n2_dict, less_btw_n2_by_max)
    # rank_bin_sent_max = BinaryFreeRank(pred_sent_max)
    # rank1 = LexFreeRank([rank_bin_sent_max, rank_agg_n2])

    # Alternative ranking, a little nicer
    # This is the one I use in the paper
    # rank_agg_pending_both = ParLexFreeRank(
    #     rank_bin_pending, n1n2_dict, less_btw_n2_by_max
    # )
    # rank_agg_sent = ParPointwiseFreeRank(rank_bin_sent_n2, n2_dict)
    # rank2 = LexFreeRank([rank_agg_sent, rank_agg_pending_both])


RingLeaderProof().check()
