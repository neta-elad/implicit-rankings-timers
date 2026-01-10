"""
Hybrid Reliable Broadcast - Relay Property

Second Property - Relay:
Under the same assumptions as correctness, if some correct node accepts,
then eventually all correct nodes accept.
"""

# @status - done

from prelude import *

from hrb import HybridReliableBroadcast, Node, QuorumA, QuorumB


class RelayHRB(Prop[HybridReliableBroadcast]):
    # Second Property - Relay
    # Under the same assumptions as correctness, if some correct node accepts,
    # then eventually all correct nodes accept.
    def prop(self) -> BoolRef:
        N = Node("N")
        M = Node("M")
        return Implies(
            And(
                Implies(
                    Exists(N, And(self.sys.correct(N), G(Not(self.sys.accept(N))))),
                    And(
                        self.sys.correct(self.sys.witness_correct_not_accept),
                        G(Not(self.sys.accept(self.sys.witness_correct_not_accept))),
                    ),
                ),
                Implies(
                    Exists(
                        N, And(self.sys.correct(N), G(Not(self.sys.sent_msg_proj(N))))
                    ),
                    And(
                        self.sys.correct(self.sys.witness_correct_not_sent),
                        G(
                            Not(
                                self.sys.sent_msg_proj(
                                    self.sys.witness_correct_not_sent
                                )
                            )
                        ),
                    ),
                ),
                ForAll(
                    [N, M],
                    Implies(
                        And(self.sys.correct(N), self.sys.rcv_init(N)),
                        F(self.sys.sent_msg(N, M)),
                    ),
                ),
                ForAll(
                    [N, M],
                    G(
                        Implies(
                            And(self.sys.sent_msg(N, M), self.sys.correct(M)),
                            F(self.sys.rcv_msg(N, M)),
                        )
                    ),
                ),
                F(Exists(N, And(self.sys.correct(N), self.sys.accept(N)))),
                F(
                    And(
                        self.sys.correct(self.sys.witness_correct_and_accept),
                        self.sys.accept(self.sys.witness_correct_and_accept),
                    )
                ),
            ),
            ForAll(N, Implies(self.sys.correct(N), F(self.sys.accept(N)))),
        )


class RelayHRBProof(Proof[HybridReliableBroadcast], prop=RelayHRB):

    @temporal_invariant
    def recv_init_eventually(self, N: Node, M: Node) -> BoolRef:
        return Implies(
            And(self.sys.correct(N), self.sys.rcv_init(N)),
            F(self.sys.sent_msg(N, M)),
        )

    @temporal_invariant
    def sent_correct_eventually_recv(self, N: Node, M: Node) -> BoolRef:
        return G(
            Implies(
                And(self.sys.sent_msg(N, M), self.sys.correct(M)),
                F(self.sys.rcv_msg(N, M)),
            )
        )

    @temporal_invariant
    def exists_correct_and_accept(self) -> BoolRef:
        # N = Node("N")
        return F(
            And(
                self.sys.correct(self.sys.witness_correct_and_accept),
                self.sys.accept(self.sys.witness_correct_and_accept),
            )
        )

    @temporal_invariant
    def property_violation(self) -> BoolRef:
        N = Node("N")
        return Exists(N, And(self.sys.correct(N), G(Not(self.sys.accept(N)))))

    # @temporal_invariant
    # def property_violation_vers(self) -> BoolRef:
    #     N = Node("N")
    #     return Exists(N, And(self.sys.correct(N), Not(self.sys.accept(N))))

    @temporal_invariant
    def witness_correct_not_accept_def(self) -> BoolRef:
        N = Node("N")
        return Implies(
            Exists(N, And(self.sys.correct(N), G(Not(self.sys.accept(N))))),
            And(
                self.sys.correct(self.sys.witness_correct_not_accept),
                G(Not(self.sys.accept(self.sys.witness_correct_not_accept))),
            ),
        )

    @temporal_invariant
    def witness_correct_not_sent(self) -> BoolRef:
        N = Node("N")
        return Implies(
            Exists(N, And(self.sys.correct(N), G(Not(self.sys.sent_msg_proj(N))))),
            And(
                self.sys.correct(self.sys.witness_correct_not_sent),
                G(Not(self.sys.sent_msg_proj(self.sys.witness_correct_not_sent))),
            ),
        )

    @temporal_invariant
    def witness_correct_not_accept_def_realized(self) -> BoolRef:
        n1 = self.sys.witness_correct_not_accept
        return And(
            self.sys.correct(n1),
            G(Not(self.sys.accept(n1))),
        )

    @system_invariant
    # passes - follows just from receive_msg def
    def correct_and_accept_then_B_quorum(self) -> BoolRef:
        B = QuorumB("B")
        N = Node("N")
        n0 = self.sys.witness_correct_and_accept
        return Implies(
            And(self.sys.correct(n0), self.sys.accept(n0)),
            Exists(
                B, ForAll(N, Implies(self.sys.member_b(N, B), self.sys.rcv_msg(N, n0)))
            ),
        )

    @system_invariant
    def relay_invariant_b(self, B: QuorumB) -> BoolRef:
        n1 = self.sys.witness_correct_not_accept
        M = Node("M")
        return Implies(
            And(self.sys.correct(n1), Not(self.sys.accept(n1))),
            Exists(M, And(self.sys.member_b(M, B), Not(self.sys.rcv_msg(M, n1)))),
        )

    @system_invariant
    def relay_invariant_a(self, A: QuorumA) -> BoolRef:
        n2 = self.sys.witness_correct_not_sent
        M = Node("M")
        return Implies(
            And(self.sys.correct(n2), Not(self.sys.sent_msg_proj(n2))),
            Exists(M, And(self.sys.member_a(M, A), Not(self.sys.rcv_msg(M, n2)))),
        )

    # System invariants from ivy file

    # @invariant
    # def safety_property(self) -> BoolRef:
    #     # Safety Property: if some obedient node accepted then some obedient node initially received the message
    #     M = Node("M")
    #     N = Node("N")
    #     return Implies(
    #         Exists(N, And(self.sys.obedient(N), self.sys.accept(N))),
    #         Exists(M, And(self.sys.obedient(M), self.sys.rcv_init(M))),
    #     )

    @system_invariant
    def sent_msg_implies_sent_msg_proj(self, N1: Node, N2: Node) -> BoolRef:
        return And(
            Implies(self.sys.sent_msg(N1, N2), self.sys.sent_msg_proj(N1)),
            # Implies(self.sys.sent_msg_proj(N1), Exists(N, self.sys.sent_msg(N1, N))),
        )

    @system_invariant
    def obedient_rcv_implies_sent(self, N1: Node, N2: Node) -> BoolRef:
        return And(
            Implies(
                And(self.sys.obedient(N2), self.sys.rcv_msg(N1, N2)),
                self.sys.sent_msg(N1, N2),
            ),
        )

    @system_invariant
    def symmetric_sends_to_all(self, N1: Node, N2: Node) -> BoolRef:
        return And(
            Implies(
                And(self.sys.symmetric(N1), self.sys.sent_msg_proj(N1)),
                self.sys.sent_msg(N1, N2),
            ),
        )

    # @invariant
    # def obedient_sends_after_A_quorum(self, N1: Node, N2: Node) -> BoolRef:
    #     A = QuorumA("A")
    #     M = Node("M")
    #     return Implies(
    #         And(
    #             self.sys.obedient(N1),
    #             self.sys.sent_msg(N1, N2),
    #             Not(self.sys.rcv_init(N1)),
    #         ),
    #         Exists(
    #             A,
    #             ForAll(M, Implies(self.sys.member_a(M, A), self.sys.sent_msg_proj(M))),
    #         ),
    #     )

    # @invariant
    # def obedient_accepts_after_B_quorum(self, N1: Node) -> BoolRef:
    #     B = QuorumB("B")
    #     M = Node("M")
    #     return Implies(
    #         And(self.sys.obedient(N1), self.sys.accept(N1)),
    #         Exists(
    #             B,
    #             ForAll(M, Implies(self.sys.member_b(M, B), self.sys.sent_msg_proj(M))),
    #         ),
    #     )

    # @invariant
    # def A_quorum_sent_implies_rcv_init(self) -> BoolRef:
    #     A = QuorumA("A")
    #     M = Node("M")
    #     N = Node("N")
    #     return Implies(
    #         Exists(
    #             A,
    #             ForAll(
    #                 M,
    #                 Implies(
    #                     And(self.sys.member_a(M, A), self.sys.obedient(M)),
    #                     self.sys.sent_msg_proj(M),
    #                 ),
    #             ),
    #         ),
    #         Exists(N, And(self.sys.obedient(N), self.sys.rcv_init(N))),
    #     )

    def not_sent(self, n: Node, m: Node) -> BoolRef:
        return Not(self.sys.sent_msg(n, m))

    def set_of_unsent(self) -> Rank:
        return DomainPointwiseRank(
            BinRank(self.not_sent), ParamSpec(n=Node, m=Node), None
        )

    def not_recv_m_correct(self, n: Node, m: Node) -> BoolRef:
        return And(Not(self.sys.rcv_msg(n, m)), self.sys.correct(m))

    def set_of_unrecv(self) -> Rank:
        return DomainPointwiseRank(
            BinRank(self.not_recv_m_correct), ParamSpec(n=Node, m=Node), None
        )

    def correct_not_accepted(self, n: Node) -> BoolRef:
        return And(self.sys.correct(n), Not(self.sys.accept(n)))

    def set_correct_not_accepted(self) -> Rank:
        return DomainPointwiseRank(
            BinRank(self.correct_not_accepted), ParamSpec(n=Node), None
        )

    def sent_formula(self, N: Node, M: Node) -> BoolRef:
        return self.sys.sent_msg(N, M)

    def correct_and_unsent(self, N: Node, M: Node) -> BoolRef:
        return And(self.sys.correct(N), Not(self.sys.sent_msg(N, M)))

    def all_sent_timers(self) -> Rank:
        return self.timer_rank(self.sent_formula, self.correct_and_unsent, None)

    def recv_formula(self, N: Node, M: Node) -> BoolRef:
        return self.sys.rcv_msg(N, M)

    def correct_sent_not_recv(self, N: Node, M: Node) -> BoolRef:
        return And(
            self.sys.correct(M),
            self.sys.sent_msg(N, M),
            Not(self.sys.rcv_msg(N, M)),
        )

    def all_rcv_timers(self) -> Rank:
        return self.timer_rank(self.recv_formula, self.correct_sent_not_recv, None)

    def exists_correct_accept(self) -> BoolRef:
        # N = Node("N")
        n0 = self.sys.witness_correct_and_accept
        return And(self.sys.correct(n0), self.sys.accept(n0))

    def timer_exists_correct_accept(self) -> Rank:
        return self.timer_rank(self.exists_correct_accept, None, None)

    # simplifying assumption for debugging - don't affect final proof

    # def not_exists_accept(self) -> BoolRef:
    #     N = Node("N")
    #     return Not(Exists(N, And(self.sys.correct(N), self.sys.accept(N))))

    # def exists_correct_rcv_init_not_sent_msg(self) -> BoolRef:
    #     N = Node("N")
    #     M = Node("M")
    #     return Exists(
    #         [N, M],
    #         And(
    #             self.sys.correct(N),
    #             self.sys.rcv_init(N),
    #             Not(self.sys.sent_msg(N, M)),
    #         ),
    #     )

    # def exists_sent_msg_not_recv(self) -> BoolRef:
    #     N = Node("N")
    #     M = Node("M")
    #     return Exists(
    #         [N, M],
    #         And(
    #             self.sys.sent_msg(N, M),
    #             self.sys.correct(M),
    #             Not(self.sys.rcv_msg(N, M)),
    #         ),
    #     )

    # def unsent_n2_accept_n0(self) -> BoolRef:
    #     # N = Node("N")
    #     n2 = self.sys.witness_correct_not_sent
    #     n0 = self.sys.witness_correct_and_accept
    #     return And(
    #         self.sys.correct(n2),
    #         Not(self.sys.sent_msg_proj(n2)),
    #         self.sys.correct(n0),
    #         self.sys.accept(n0),
    #     )

    # def usent_n2(self) -> BoolRef:
    #     # N = Node("N")
    #     n2 = self.sys.witness_correct_not_sent
    #     n0 = self.sys.witness_correct_and_accept
    #     return And(
    #         self.sys.correct(n2),
    #         Not(self.sys.sent_msg_proj(n2)),
    #     )  # works

    # def never_sent_n2(self) -> BoolRef:
    #     n2 = self.sys.witness_correct_not_sent
    #     return And(
    #         self.sys.correct(n2),
    #         timer_zero(self.t(G(Not(self.sys.sent_msg_proj(n2))))()),
    #     )

    # if there is n2 such that not sent_msg_proj
    # some correct node n0 accepted ->
    # there is a B0 for which member(N,B0)->rcv_msg(N,n0)
    # for B0 there is A0 that has only symmetric nodes from B0
    # from relay_invariant_a:
    # if n2 has not yet sent
    # exists M1. member_a(M1,A0) and not recv_msg(M1,n2)
    # members of A0 are members of B0 so they all have
    # rcv_msg(M1,n0) & n0 is correct -> sent_msg(M1,n0) ->[symmetric] sent_msg(M1,n2) -> we are waiting for it to receive.
    # in summary: if there is a correct node that hasn't sent sent this should be the way to finish.

    # this captures this case
    def exists_correct_never_sent(self) -> BoolRef:
        N = Node("N")
        return timer_infinite(
            self.t(
                ForAll(N, Or(Not(self.sys.correct(N)), F(self.sys.sent_msg_proj(N))))
            )()
        )

    # this invariant captures the reasoning, maybe not needed
    @system_invariant
    def supporting_invariant_for_case_unsent(self) -> BoolRef:
        n2 = self.sys.witness_correct_not_sent
        n0 = self.sys.witness_correct_and_accept
        N = Node("N")
        B = QuorumB("B")
        A = QuorumA("A")
        M1 = Node("M1")
        return Implies(
            And(
                self.sys.correct(n2),
                Not(self.sys.sent_msg_proj(n2)),
                self.sys.correct(n0),
                self.sys.accept(n0),
            ),
            Exists(
                B,
                And(
                    ForAll(
                        N, Implies(self.sys.member_b(N, B), self.sys.rcv_msg(N, n0))
                    ),
                    Exists(
                        A,
                        And(
                            ForAll(
                                N,
                                Implies(
                                    self.sys.member_a(N, A),
                                    And(
                                        self.sys.member_b(N, B),
                                        self.sys.symmetric(N),
                                    ),
                                ),
                            ),
                            Exists(
                                M1,
                                And(
                                    self.sys.member_a(M1, A),  # relay_invariant_a
                                    Not(self.sys.rcv_msg(M1, n2)),
                                    self.sys.symmetric(M1),  # def A
                                    self.sys.member_b(M1, B),  # def A
                                    self.sys.rcv_msg(M1, n0),  # def B
                                    self.sys.sent_msg(M1, n0),  # n0 is correct
                                    self.sys.sent_msg(M1, n2),  # M1 is symmetric
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )

    # else:
    # we know that all correct eventually send
    # we can add this with Cond(timer_rank(sent_msg_proj(N)), G(forall(N,correct(N)->sent_msg_proj(N)))

    # n1 not accepted ->
    # there is a b quorum B0 that has all correct nodes
    # from relay_invariant_b:
    # exists M. member_b(M,B0) & ~rcv_msg(M,n1)
    # like before we want to show eventually sent_msg(M,n1)

    # this captures this case
    def all_correct_eventually_sent(self) -> BoolRef:
        N = Node("N")
        return timer_zero(
            self.t(
                ForAll(N, Or(Not(self.sys.correct(N)), F(self.sys.sent_msg_proj(N))))
            )()
        )

    # works
    def all_correct_sent_n1_not_accept(self) -> BoolRef:
        n1 = self.sys.witness_correct_not_accept
        N = Node("N")
        return And(
            self.sys.correct(n1),
            Not(self.sys.accept(n1)),
            ForAll(N, Implies(self.sys.correct(N), self.sys.sent_msg_proj(N))),
        )

    def all_correct_sent(self) -> BoolRef:
        N = Node("N")
        return And(ForAll(N, Implies(self.sys.correct(N), self.sys.sent_msg_proj(N))))

    # supporting invariant shows the reasoning
    @system_invariant
    def supporting_invariant_for_case_all_sent(self) -> BoolRef:
        n1 = self.sys.witness_correct_not_accept
        n0 = self.sys.witness_correct_and_accept
        N = Node("N")
        B = QuorumB("B")
        A = QuorumA("A")
        M1 = Node("M1")
        return Implies(
            And(
                self.sys.correct(n1),
                Not(self.sys.accept(n1)),
                ForAll(N, Implies(self.sys.correct(N), self.sys.sent_msg_proj(N))),
            ),
            Exists(
                B,
                And(
                    ForAll(N, Implies(self.sys.member_b(N, B), self.sys.correct(N))),
                    Exists(
                        M1,
                        And(
                            self.sys.member_b(M1, B),
                            Not(self.sys.rcv_msg(M1, n1)),
                            self.sys.sent_msg(M1, n1),
                        ),
                    ),
                ),
            ),
        )

    @invariant
    def correct_sent_msg_proj_sent_all(self, N: Node, M: Node) -> BoolRef:
        return Implies(
            And(
                self.sys.correct(N),
                self.sys.sent_msg_proj(N),
            ),
            self.sys.sent_msg(N, M),
        )

    def sent_msg_proj(self, N: Node) -> BoolRef:
        return self.sys.sent_msg_proj(N)

    def correct_and_all_correct_eventually_sent(self, N: Node) -> BoolRef:
        return And(
            self.sys.correct(N),
            self.all_correct_eventually_sent(),
        )

    def all_sent_proj_timers(self) -> Rank:
        return self.timer_rank(
            self.sent_msg_proj, self.correct_and_all_correct_eventually_sent, None
        )

    def rank(self) -> Rank:
        # could be PWRank partially at least
        return PointwiseRank(
            self.timer_exists_correct_accept(),
            # self.set_of_unrecv(),
            # self.set_correct_not_accepted(),
            self.all_sent_timers(),
            self.all_sent_proj_timers(),
            LexRank(
                self.set_of_unsent(),
                self.all_rcv_timers(),
            ),
        )

    def l2s_ivy_file(self) -> str | None:
        return "hybrid_reliable_broadcast_cisa_relay"


RelayHRBProof().check()
