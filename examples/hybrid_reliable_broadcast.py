from prelude import *

# HRB from Berkovits' paper (Hybrid Reliable Broadcast)
# currently not encoding the finiteness, and not checking side conditions
# currently commented out sent_msg_proj but maybe we do need it


class Node(Finite): ...


class QuorumA(Finite): ...


class QuorumB(Finite): ...


class HybridReliableBroadcast(TransitionSystem):
    witness_exists_correct: Immutable[Node]

    # Immutable relations
    member_a: Immutable[Rel[Node, QuorumA]]
    member_b: Immutable[Rel[Node, QuorumB]]
    member_fa: Immutable[Rel[Node]]
    member_fc: Immutable[Rel[Node]]
    member_fs: Immutable[Rel[Node]]
    member_fi: Immutable[Rel[Node]]
    correct: Immutable[Rel[Node]]
    obedient: Immutable[Rel[Node]]
    symmetric: Immutable[Rel[Node]]
    rcv_init: Immutable[Rel[Node]]

    # Mutable relations
    accept: Rel[Node]
    sent_msg: Rel[Node, Node]
    rcv_msg: Rel[Node, Node]
    sent_msg_proj: Rel[Node]

    @axiom
    def system_axioms(
        self, B: QuorumB, A_BP: QuorumA, B_CF: QuorumB, A: QuorumA, N: Node
    ) -> BoolRef:
        return And(
            # There is a B quorum that has all correct nodes
            # In every A quorum there is a node that is obedient (that is, someone has to check something - i guess then these are large quorums?)
            # Every B quorum has an A quorum that has only symmetric nodes from it (why is it important i dont know)
            Exists(B, ForAll(N, Implies(self.member_b(N, B), self.correct(N)))),
            ForAll(A_BP, Exists(N, And(self.member_a(N, A_BP), self.obedient(N)))),
            ForAll(
                B_CF,
                Exists(
                    A,
                    ForAll(
                        N,
                        Implies(
                            self.member_a(N, A),
                            And(self.member_b(N, B_CF), self.symmetric(N)),
                        ),
                    ),
                ),
            ),
            Not(And(self.member_fc(N), self.member_fi(N))),
            Not(And(self.member_fc(N), self.member_fs(N))),
            Not(And(self.member_fc(N), self.member_fa(N))),
            Not(And(self.member_fi(N), self.member_fs(N))),
            Not(And(self.member_fi(N), self.member_fa(N))),
            Not(And(self.member_fs(N), self.member_fa(N))),
        )

    # maybe this an old artifact
    @axiom
    def witness_axiom(self) -> BoolRef:
        N = Node("N")
        return Implies(
            Exists(N, self.correct(N)), self.correct(self.witness_exists_correct)
        )

    @axiom
    def derived_relations_axiom(self, N: Node) -> BoolRef:
        return And(
            self.obedient(N) == And(Not(self.member_fs(N)), Not(self.member_fa(N))),
            self.symmetric(N) == And(Not(self.member_fi(N)), Not(self.member_fa(N))),
            self.correct(N)
            == And(
                Not(self.member_fi(N)),
                Not(self.member_fa(N)),
                Not(self.member_fs(N)),
                Not(self.member_fc(N)),
            ),
        )

    @init
    def initial(self, X: Node, Y: Node) -> BoolRef:
        return And(
            Not(self.accept(X)),
            Not(self.sent_msg(X, Y)),
            Not(self.sent_msg_proj(X)),
            Not(self.rcv_msg(X, Y)),
        )

    @transition
    def receive_init(self, n: Node) -> BoolRef:
        N2 = Node("N2")
        return And(
            self.rcv_init(n),
            self.accept.unchanged(),
            self.rcv_msg.unchanged(),
            self.sent_msg.update(
                lambda old, new, N1, N2: new(N1, N2) == Or(old(N1, N2), N1 == n)
            ),
            self.sent_msg_proj.update(
                lambda old, new, N1: new(N1)
                == If(N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1))
            ),
        )

    @transition
    def receive_msg(self, s: Node, n: Node) -> BoolRef:
        N2 = Node("N2")
        A = QuorumA("A")
        B = QuorumB("B")
        N = Node("N")
        return And(
            self.sent_msg(s, n),
            self.rcv_msg.update(
                lambda old, new, N1, N2: new(N1, N2)
                == Or(old(N1, N2), And(N1 == s, N2 == n))
            ),
            If(
                Exists(
                    B, ForAll(N, Implies(self.member_b(N, B), self.next.rcv_msg(N, n)))
                ),
                self.accept.update(lambda old, new, N: new(N) == Or(old(N), N == n)),
                self.accept.unchanged(),
            ),
            If(
                Exists(
                    A, ForAll(N, Implies(self.member_a(N, A), self.next.rcv_msg(N, n)))
                ),
                And(
                    self.sent_msg.update(
                        lambda old, new, N1, N2: new(N1, N2) == Or(old(N1, N2), N1 == n)
                    ),
                    self.sent_msg_proj.update(
                        lambda old, new, N1: new(N1)
                        == If(N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1))
                    ),
                ),
                And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
            ),
        )

    @transition
    def receive_msg_c(self, s: Node, n: Node) -> BoolRef:
        N2 = Node("N2")
        A = QuorumA("A")
        B = QuorumB("B")
        N = Node("N")
        return And(
            self.sent_msg(s, n),
            self.member_fc(n),
            self.rcv_msg.update(
                lambda old, new, N1, N2: new(N1, N2)
                == Or(old(N1, N2), And(N1 == s, N2 == n))
            ),
            If(
                Exists(
                    B, ForAll(N, Implies(self.member_b(N, B), self.next.rcv_msg(N, n)))
                ),
                self.accept.update(lambda old, new, N: new(N) == Or(old(N), N == n)),
                self.accept.unchanged(),
            ),
            If(
                Exists(
                    A, ForAll(N, Implies(self.member_a(N, A), self.next.rcv_msg(N, n)))
                ),
                Or(
                    And(
                        self.sent_msg.update(
                            lambda old, new, N1, N2: new(N1, N2)
                            == Or(old(N1, N2), N1 == n)
                        ),
                        self.sent_msg_proj.update(
                            lambda old, new, N1: new(N1)
                            == If(
                                N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1)
                            )
                        ),
                    ),
                    And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
                ),
                And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
            ),
        )

    @transition
    def receive_init_i(self, n: Node) -> BoolRef:
        N1 = Node("N1")
        N2 = Node("N2")
        N = Node("N")
        return And(
            self.member_fi(n),
            self.rcv_init(n),
            Implies(
                self.sent_msg_proj(n), Exists(N, self.sent_msg(n, N))
            ),  # instrumentation is right for n
            self.accept.unchanged(),
            self.rcv_msg.unchanged(),
            ForAll(
                [N1, N2],
                Implies(self.next.sent_msg(N1, N2), Or(self.sent_msg(N1, N2), N1 == n)),
            ),  # messages can only be sent from n - arbitrarily
            ForAll(
                [N1, N2], Implies(self.sent_msg(N1, N2), self.next.sent_msg(N1, N2))
            ),  # all existing messages remain
            self.sent_msg_proj.update(
                lambda old, new, N1: new(N1)
                == If(N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1))
            ),
        )

    @transition
    def trans_receive_msg_i(self, s: Node, n: Node) -> BoolRef:
        N1 = Node("N1")
        N2 = Node("N2")
        A = QuorumA("A")
        B = QuorumB("B")
        N = Node("N")
        return And(
            self.member_fi(n),
            self.sent_msg(s, n),
            self.rcv_msg.update(
                lambda old, new, N1, N2: new(N1, N2)
                == Or(old(N1, N2), And(N1 == s, N2 == n))
            ),
            If(
                Exists(
                    B, ForAll(N, Implies(self.member_b(N, B), self.next.rcv_msg(N, n)))
                ),
                self.accept.update(
                    lambda old, new, N1: new(N1) == Or(old(N1), N1 == n)
                ),
                self.accept.unchanged(),
            ),
            If(
                Exists(
                    A, ForAll(N, Implies(self.member_a(N, A), self.next.rcv_msg(N, n)))
                ),
                Or(
                    And(
                        # sent_msg(n,N) := *; assume old sent_msg(n,N) -> sent_msg(n,N);
                        Implies(
                            self.sent_msg_proj(n), Exists(N, self.sent_msg(n, N))
                        ),  # instrumentation is right
                        ForAll(
                            [N1, N2],
                            Implies(
                                self.next.sent_msg(N1, N2),
                                Or(self.sent_msg(N1, N2), N1 == n),
                            ),
                        ),  # only messages from n are sent
                        ForAll(
                            [N1, N2],
                            Implies(self.sent_msg(N1, N2), self.next.sent_msg(N1, N2)),
                        ),  # messages are not deleted.
                        self.sent_msg_proj.update(
                            lambda old, new, N1: new(N1)
                            == If(
                                N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1)
                            )
                        ),
                    ),
                    And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
                ),
                And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
            ),
        )

    @transition
    def trans_faulty_send_s(self, n: Node) -> BoolRef:
        N2 = Node("N2")
        return And(
            self.member_fs(n),
            self.accept.unchanged(),
            self.rcv_msg.unchanged(),
            self.sent_msg.update(
                lambda old, new, N1, N2: new(N1, N2) == Or(old(N1, N2), N1 == n)
            ),
            self.sent_msg_proj.update(
                lambda old, new, N1: new(N1)
                == If(N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1))
            ),
        )

    @transition
    def trans_faulty_state_sa(self, n: Node) -> BoolRef:
        N = Node("N")
        N1 = Node("N1")
        return And(
            Or(self.member_fs(n), self.member_fa(n)),
            ForAll(N, Implies(N != n, self.next.accept(N) == self.accept(N))),
            ForAll(
                [N, N1],
                Implies(N1 != n, self.next.rcv_msg(N, N1) == self.rcv_msg(N, N1)),
            ),
            self.sent_msg.unchanged(),
            self.sent_msg_proj.unchanged(),
        )

    @transition
    def trans_faulty_send_a(self, n: Node) -> BoolRef:
        N1 = Node("N1")
        N2 = Node("N2")
        N = Node("N")
        return And(
            self.member_fa(n),
            self.accept.unchanged(),
            self.rcv_msg.unchanged(),
            Implies(
                self.sent_msg_proj(n), Exists(N, self.sent_msg(n, N))
            ),  # instrumentation is right
            ForAll(
                [N1, N2],
                Implies(N1 != n, self.next.sent_msg(N1, N2) == self.sent_msg(N1, N2)),
            ),  # arbitrary creation of messages from n
            ForAll(
                [N1, N2], Implies(self.sent_msg(N1, N2), self.next.sent_msg(N1, N2))
            ),  # messages are not deleted.
            self.sent_msg_proj.update(
                lambda old, new, N1: new(N1)
                == If(N1 == n, Exists(N2, self.next.sent_msg(N1, N2)), old(N1))
            ),
        )


class CorrectnessHRB(Prop[HybridReliableBroadcast]):
    # First Property - Correctness
    # If all obedient nodes initially hold the message and all correct nodes eventually send and receive
    # then eventually some node accepts
    def prop(self) -> BoolRef:
        N = Node("N")
        M = Node("M")
        return Not(
            And(  # todo: simplify
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
                G(ForAll(N, Not(And(self.sys.correct(N), self.sys.accept(N))))),
            )
        )


class CorrectnessHRBProof(Proof[HybridReliableBroadcast], prop=CorrectnessHRB):

    # intuition:
    # all correct nodes are obedient so they receive init
    # we wait for some correct node to send to all nodes
    # we then wait for the message to be received by all nodes in a B quorum that has all the correct nodes
    # then any correct node will accept
    # giving contradiction to the negated property

    @invariant
    def system_invariant(self, N1: Node, N2: Node) -> BoolRef:
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
            Implies(self.sys.sent_msg(N1, N2), self.sys.sent_msg_proj(N1)),
            # Implies(self.sys.sent_msg_proj(N1), Exists(N, self.sys.sent_msg(N1, N))),
            Implies(
                And(self.sys.obedient(N2), self.sys.rcv_msg(N1, N2)),
                self.sys.sent_msg(N1, N2),
            ),
            Implies(
                And(self.sys.symmetric(N1), self.sys.sent_msg_proj(N1)),
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
                        M, Implies(self.sys.member_a(M, A), self.sys.sent_msg_proj(M))
                    ),
                ),
            ),
            Implies(
                And(self.sys.obedient(N1), self.sys.accept(N1)),
                Exists(
                    B,
                    ForAll(
                        M, Implies(self.sys.member_b(M, B), self.sys.sent_msg_proj(M))
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
                            self.sys.sent_msg_proj(M),
                        ),
                    ),
                ),
                Exists(N, And(self.sys.obedient(N), self.sys.rcv_init(N))),
            ),
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
            # all these quantified non-EPR invariants are not verifiable
            # not from original ivy file
            # Implies(
            #     ForAll(
            #         [N, M],
            #         Implies(
            #             And(self.sys.correct(N), self.sys.correct(M)),
            #             self.sys.rcv_msg(N, M),
            #         ),
            #     ),
            #     Exists(N, And(self.sys.correct(N), self.sys.accept(N))),
            # ),
            # only for the relay property - they instantiate this invariant only for specific witness nodes because its not EPR
            # invariant forall N,B. correct(N) & ~accept(N) -> exists M. member_b(M,B) & ~rcv_msg(M,N)
            # ForAll(
            #     [N, B],
            #     Implies(
            #         And(self.sys.correct(N), Not(self.sys.accept(N))),
            #         Exists(
            #             M, And(self.sys.member_b(M, B), Not(self.sys.rcv_msg(M, N)))
            #         ),
            #     ),
            # ),
            # # invariant forall N,A. correct(N) & ~sent_msg_proj(N) -> exists M. member_a(M,A) & ~rcv_msg(M,N)
            # ForAll(
            #     [N, A],
            #     Implies(
            #         And(self.sys.correct(N), Not(Exists(M, self.sys.sent_msg(N, M)))),
            #         Exists(
            #             M, And(self.sys.member_a(M, A), Not(self.sys.rcv_msg(M, N)))
            #         ),
            #     ),
            # ),
        )

    @invariant
    def timer_invariant_correctness(self, N: Node, M: Node) -> BoolRef:
        return And(
            timer_zero(
                self.t(
                    G(ForAll(N, Not(And(self.sys.correct(N), self.sys.accept(N)))))
                )()
            ),
            Implies(self.sys.obedient(N), self.sys.rcv_init(N)),
            Implies(
                And(self.sys.correct(N), self.sys.rcv_init(N)),
                timer_finite(self.t(self.sys.sent_msg(N, M))(N, M)),
            ),
            timer_zero(
                self.t(
                    G(
                        Implies(
                            And(self.sys.sent_msg(N, M), self.sys.correct(M)),
                            F(self.sys.rcv_msg(N, M)),
                        )
                    )
                )(N, M)
            ),
            Implies(
                And(
                    self.sys.correct(M),
                    self.sys.sent_msg(N, M),
                    Not(self.sys.rcv_msg(N, M)),
                ),
                timer_finite(self.t(self.sys.rcv_msg(N, M))(N, M)),
            ),
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


CorrectnessHRBProof().check()


## Waiting for ability to have witnesses for temporal formulas
class RelayHRB(Prop[HybridReliableBroadcast]):
    # Second Property - Relay
    # Under the same assumptions as correctness, if some correct node accepts,
    # then eventually all correct nodes accept.
    def prop(self) -> BoolRef:
        N = Node("N")
        M = Node("M")
        return Not(
            And(  # todo: simplify
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
                G(Exists(N, And(self.sys.correct(N), Not(self.sys.accept(N))))),
            )
        )


class RelayHRBProof(Proof[HybridReliableBroadcast], prop=RelayHRB):

    pass
    # intuition:
    # first we wait for some obedient node n0 to accept
    # let B0 be the quorum that has all the correct nodes
    # and let A0 be the quorum that has only symmetric nodes from B0
    # we want to show that eventually all correct nodes accept through B0
    # didn't compeletely get this but this is related to the non-EPR invariants above.

    # def timer_invariant_relay(sym):
    #     return And(
    #         sym["t_<G(Exists(N, And(correct(N), Not(accept(N)))))>"] == 0,
    #         ForAll(
    #             [N, M],
    #             Implies(
    #                 And(
    #                     self.correct(N),
    #                     self.sys.rcv_init(N),
    #                     Not(self.sent_msg(N, M)),
    #                 ),
    #                 sym["t_<sent_msg(N, M)>"](N, M) > 0,
    #             ),
    #         ),
    #         ForAll(
    #             [N, M],
    #             sym[
    #                 "t_<G(Or(Or(Not(sent_msg(N, M)), Not(correct(M))), F(rcv_msg(N, M))))>"
    #             ](N, M)
    #             == 0,
    #         ),
    #         ForAll(
    #             [N, M],
    #             Implies(
    #                 And(
    #                     self.correct(M),
    #                     self.sent_msg(N, M),
    #                     Not(self.rcv_msg(N, M)),
    #                 ),
    #                 sym["t_<rcv_msg(N, M)>"](N, M) > 0,
    #             ),
    #         ),
    #         Or(
    #             Exists(N, And(self.sys.obedient(N), self.accept(N))),
    #             sym["t_<Exists(N, And(obedient(N), accept(N)))>"] > 0,
    #         ),
    #     )

    # def invariant_relay(sym):
    #     return And(system_invariant(sym), timer_invariant_relay(sym))

    # # more ranks

    # not_accept_correct = lambda sym, param: And(
    #     self.correct(param["N"]), Not(self.accept(param["N"]))
    # )
    # bin_not_accept = BinaryFreeRank(not_accept_correct, {"N": Node})
    # pw_not_accept = ParPointwiseFreeRank(bin_not_accept, {"N": Node})

    # # should be packaged somehow
    # timer_exists_accept = PositionInOrderFreeRank(
    #     lambda sym, param1, param2: param1["x"] < param2["x"],
    #     param_int,
    #     {"x": lambda sym, param: sym["t_<Exists(N, And(obedient(N), accept(N)))>"]},
    #     {},
    # )
    # exists_accept = lambda sym, param: Exists(
    #     N, And(self.sys.obedient(N), self.accept(N))
    # )
    # not_exists_accept = lambda sym, param: Not(exists_accept(sym, param))
    # timer_exists_accept_lin = LinFreeRank(
    #     [timer_exists_accept, trivial_rank], [not_exists_accept, exists_accept]
    # )

    # # not necessarily important or needed at all
    # correct_rcv_init_and_unsent = lambda sym, param: And(
    #     self.correct(param["N"]),
    #     self.sys.rcv_init(param["N"]),
    #     Not(self.sent_msg(param["N"], param["M"])),
    # )
    # ow3 = lambda sym, param: Not(correct_rcv_init_and_unsent(sym, param))
    # sent_timer_for_good = LinFreeRank(
    #     [sent_timer, trivial_rank], [correct_rcv_init_and_unsent, ow3]
    # )
    # all_sent_timers_refined = ParPointwiseFreeRank(sent_timer_for_good, param_NM)

    # not_sent = lambda sym, param: Not(self.sent_msg(param["N"], param["M"]))
    # correct_sent_not_recv_accept = lambda sym, param: And(
    #     self.correct(param["M"]),
    #     self.correct(param["N"]),
    #     self.sent_msg(param["N"], param["M"]),
    #     Not(self.rcv_msg(param["N"], param["M"])),
    #     Not(self.accept(param["M"])),
    # )
    # ow4 = lambda sym, param: And(
    #     Not(correct_sent_not_recv_accept(sym, param)), Not(not_sent(sym, param))
    # )
    # sent_timer_for_good = LinFreeRank(
    #     [trivial_rank, rcv_timer, trivial_rank],
    #     [not_sent, correct_sent_not_recv_accept, ow4],
    # )
    # all_rcv_timers_refined = ParPointwiseFreeRank(sent_timer_for_good, param_NM)

    # # the rank below might be good enough but there is either a problem with the timer ranks or the invariant is not good enough.

    # rank_relay = PointwiseFreeRank(
    #     [
    #         pw_not_sent,
    #         pw_not_recv,
    #         pw_not_accept,
    #         timer_exists_accept_lin,
    #         all_rcv_timers_refined,
    #         all_sent_timers_refined,
    #     ]
    # )
