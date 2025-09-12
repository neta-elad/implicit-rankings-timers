from prelude import *

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

    btw : Immutable[Rel[Node, Node, Node]]
    le : Immutable[Rel[Id, Id]]
    id : Immutable[Fun[Node, Id]]

    leader : Rel[Node]
    pending : Rel[Id, Node]
    sent_own : Rel[Node]
    scheduled : Rel[Node]

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
            self.sent_own(X) == False
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
                                    self.leader.update(
                                        lambda old, new, N: new(N) == Or(old(N), N == n)
                                    ),
                                    self.sent_own.unchanged(),
                                    self.pending.update(
                                        lambda old, new, A, N: new(A, N)
                                        == And(old(A, N), Not(And(A == B, N == n)))
                                    ),
                                ),
                                If(
                                    self.le(self.id(n), B),
                                    # B is higher - pass forward
                                    And(
                                        self.leader.unchanged(),
                                        self.sent_own.unchanged(),
                                        self.pending.update(
                                            lambda old, new, A, N: new(A, N)
                                            == Or(
                                                And(
                                                    old(A, N), Not(And(A == B, N == n))
                                                ),
                                                And(N == succ, A == B),
                                            )
                                        ),
                                    ),
                                    # B is lower - drop
                                    And(
                                        self.leader.unchanged(),
                                        self.sent_own.unchanged(),
                                        self.pending.update(
                                            lambda old, new, A, N: new(A, N)
                                            == And(old(A, N), Not(And(A == B, N == n))),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
                # yet to send own id
                And(
                    self.leader.unchanged(),
                    self.sent_own.update(
                        lambda old, new, N: new(N) == Or(old(N), N == n)
                    ),
                    self.pending.update(
                        lambda old, new, A, N: new(A, N)
                        == Or(old(A, N), And(A == self.id(n), N == succ))
                    ),
                ),
            ),
        )

class RingLeaderProp(Prop[RingLeader]):
    def negated_prop(self) -> BoolRef:
        N = Node("N")
        return And(
            ForAll(N, G(F(self.sys.scheduled(N)))),
            F(
                Exists(N, self.sys.leader(N))
            ),
        )

class RingLeaderProof(Proof[RingLeader],prop=RingLeaderProp):

    @invariant
    def safety(self, X:Node,Y:Node) -> BoolRef:
        return Implies(And(self.sys.leader(X), self.sys.leader(Y)), X == Y)

    @invariant
    def leader_max(self, X: Node, Y: Node) -> BoolRef:
        return Implies(self.sys.leader(X), self.sys.le(self.sys.id(Y), self.sys.id(X)))

    @invariant
    def self_pending_highest_id(self, X: Node, Y: Node) -> BoolRef:
        return Implies(self.sys.pending(self.sys.id(X), X), self.sys.le(self.sys.id(Y), self.sys.id(X)))

    @invariant
    def no_bypass(self, X: Node, Y: Node, Z: Node) -> BoolRef:
        return Implies(
            And(self.sys.pending(self.sys.id(X), Y), self.sys.btw(X, Z, Y)),
            self.sys.le(self.sys.id(Z), self.sys.id(X)),
        )

    # rho = lambda sym: And(
    #     # ForAll([X,Y],Implies(self.pending(sym['id'](X),Y),self.sent_own(X))),
    #     # inv_safety(sym),
    #     ForAll([A, X], Implies(self.pending(A, X), Exists(Y, sym["id"](Y) == A))),
    #     Or(
    #         q(sym),
    #         Exists(X, Not(self.sent_own(X))),
    #         Exists([X, Y], self.pending(sym["id"](Y), X)),
    #     ),
    #     ForAll(
    #         X,
    #         Implies(
    #             And(self.sent_own(X), Not(self.leader(X))),
    #             Exists(
    #                 Y,
    #                 Or(  # quantifier alteration that is hard
    #                     Not(self.le(sym["id"](Y), sym["id"](X))),
    #                     self.pending(sym["id"](X), Y),
    #                 ),
    #             ),
    #         ),
    #     ),
    # )
    # phi = lambda sym: And(Not(q(sym)), rho(sym))
    # psi = lambda sym, param: Or(
    #     Not(self.sent_own(n)), Exists(X, self.pending(sym["id"](X), n))
    # )
    # pred_pending_n1n2 = lambda sym, param: self.pending(
    #     sym["id"](param["n1"]), param["n2"]
    # )
    # pred_sent_n2 = lambda sym, param: Not(self.sent_own(param["n2"]))
    # pred_sent_max = lambda sym, param: Not(self.sent_own(sym["max"]))

    # # extracting an order from the ring structure, such that max is maximal.
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

    # proof1 = LivenessProof(prop, rank1, rho, phi, [psi])
    # # proof1.check_proof(ts)

    # # Alternative ranking, a little nicer
    # # This is the one I use in the paper
    # rank_agg_pending_both = ParLexFreeRank(
    #     rank_bin_pending, n1n2_dict, less_btw_n2_by_max
    # )
    # rank_agg_sent = ParPointwiseFreeRank(rank_bin_sent_n2, n2_dict)
    # rank2 = LexFreeRank([rank_agg_sent, rank_agg_pending_both])

    # proof2 = LivenessProof(prop, rank2, rho, phi, [psi])
    # proof2.check_proof(ts)

    def scheduled(self, N: Node) -> BoolRef:
        return self.sys.scheduled(N)

    def scheduling_rank(self) -> Rank:
        return self.timer_rank(self.scheduled, None, None)
    
    def rank(self) -> Rank:
        return self.scheduling_rank()

RingLeaderProof().check()