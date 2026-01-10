"""
Hybrid Reliable Broadcast - Correctness Property

First Property - Correctness:
If all obedient nodes initially hold the message and all correct nodes eventually send and receive
then eventually some node accepts
"""

# @status - done

from prelude import *

from hrb import HybridReliableBroadcast, Node, QuorumA, QuorumB


class CorrectnessHRB(Prop[HybridReliableBroadcast]):
    # First Property - Correctness
    # If all obedient nodes initially hold the message and all correct nodes eventually send and receive
    # then eventually some node accepts
    def prop(self) -> BoolRef:
        N = Node("N")
        M = Node("M")
        return Implies(
            And(
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
                ForAll(N, Implies(self.sys.obedient(N), self.sys.rcv_init(N))),
            ),
            F(Exists(N, (And(self.sys.correct(N), self.sys.accept(N))))),
        )


class CorrectnessHRBProof(Proof[HybridReliableBroadcast], prop=CorrectnessHRB):

    # intuition:
    # all correct nodes are obedient so they receive init
    # we wait for some correct node to send to all nodes
    # we then wait for the message to be received by all nodes in a B quorum that has all the correct nodes
    # then any correct node will accept
    # giving contradiction to the negated property

    # @invariant
    def safety_invariants(self, N1: Node, N2: Node) -> BoolRef:
        M = Node("M")
        N = Node("N")
        A = QuorumA("A")
        B = QuorumB("B")
        return And(
            # System invariants from ivy file - currently not needed
            # Safety Property: if some obedient node accepted then some obedient node initially received the message
            Implies(
                Exists(N, And(self.sys.obedient(N), self.sys.accept(N))),
                Exists(M, And(self.sys.obedient(M), self.sys.rcv_init(M))),
            ),
            Implies(
                self.sys.sent_msg(N1, N2), self.sys.sent_msg_proj(N1)
            ),  # invariant using sent_msg_proj - not necessary
            # Implies(self.sys.sent_msg_proj(N1), Exists(N, self.sys.sent_msg(N1, N))),
            Implies(
                And(self.sys.obedient(N2), self.sys.rcv_msg(N1, N2)),
                self.sys.sent_msg(N1, N2),
            ),
            Implies(
                And(
                    self.sys.symmetric(N1), self.sys.sent_msg_proj(N1)
                ),  # using sent_msg_proj - can replace with no new quantification
                self.sys.sent_msg(N1, N2),
            ),
            Implies(
                And(
                    self.sys.obedient(N1),
                    self.sys.sent_msg(N1, N2),
                    Not(self.sys.rcv_init(N1)),
                ),
                Exists(
                    A,
                    ForAll(
                        M,
                        Implies(
                            self.sys.member_a(M, A), self.sys.sent_msg_proj(M)
                        ),  # invariant using sent_msg_proj
                    ),
                ),
            ),
            Implies(
                And(self.sys.obedient(N1), self.sys.accept(N1)),
                Exists(
                    B,
                    ForAll(
                        M,
                        Implies(
                            self.sys.member_b(M, B), self.sys.sent_msg_proj(M)
                        ),  # invariant using sent_msg_proj
                    ),
                ),
            ),
            Implies(
                Exists(
                    A,
                    ForAll(
                        M,
                        Implies(
                            And(self.sys.member_a(M, A), self.sys.obedient(M)),
                            self.sys.sent_msg_proj(M),  # invariant using sent_msg_proj
                        ),
                    ),
                ),
                Exists(N, And(self.sys.obedient(N), self.sys.rcv_init(N))),
            ),
        )

    @invariant
    def liveness_invariant(self, N1: Node, N2: Node) -> BoolRef:
        M = Node("M")
        N = Node("N")
        A = QuorumA("A")
        B = QuorumB("B")
        return And(
            # invariant from liveness proof in l2s:
            self.sys.correct(self.sys.witness_exists_correct),
            Not(
                Exists(
                    B,
                    ForAll(
                        N,
                        Implies(
                            self.sys.member_b(N, B),
                            self.sys.rcv_msg(N, self.sys.witness_exists_correct),
                        ),
                    ),
                )
            ),
        )

    @temporal_invariant
    @track
    def timer_invariant(self, N: Node, M: Node) -> BoolRef:
        return And(
            Implies(
                And(self.sys.correct(N), self.sys.rcv_init(N)),
                F(self.sys.sent_msg(N, M)),
            ),
            G(
                Implies(
                    And(self.sys.sent_msg(N, M), self.sys.correct(M)),
                    F(self.sys.rcv_msg(N, M)),
                )
            ),
            ForAll(N, Implies(self.sys.obedient(N), self.sys.rcv_init(N))),
            Not(F(Exists(N, (And(self.sys.correct(N), self.sys.accept(N)))))),
        )

    # system ranks

    def not_sent(self, n: Node, m: Node) -> BoolRef:
        return Not(self.sys.sent_msg(n, m))

    def set_of_unsent(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.not_sent), None)

    def not_recv_both_correct(self, n: Node, m: Node) -> BoolRef:
        return And(
            Not(self.sys.rcv_msg(n, m)), self.sys.correct(n), self.sys.correct(m)
        )

    def set_of_unrecv(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.not_recv_both_correct), None)

    def correct_not_accepted(self, n: Node) -> BoolRef:
        return And(self.sys.correct(n), Not(self.sys.accept(n)))

    def set_correct_not_accepted(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.correct_not_accepted), None)

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

    def rank(self) -> Rank:
        # could be PWRank partially at least
        return LexRank(
            self.set_of_unrecv(),
            self.set_of_unsent(),
            self.all_sent_timers(),
            self.all_rcv_timers(),
        )

    def l2s_ivy_file(self) -> str | None:
        return "hybrid_reliable_broadcast_cisa_correctness"


CorrectnessHRBProof().check()
