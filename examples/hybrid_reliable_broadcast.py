"""
Hybrid Reliable Broadcast

In this file we only have the system, the properties and proofs are in
hybrid_reliable_broadcast_correct.py and hybrid_reliable_broadcast_relay.py

Taken from the Ivy implementation of HRB:
Berkovits, I., Lazic, M., Losa, G., Padon, O., Shoham, S.: Verification of threshold-based distributed algorithms by decomposition to decidable logics.
In: Computer Aided Verification - 31st International Conference, CAV 2019 (2019), https://doi.org/10.1007/978-3-030-25543-5_15

Protocol from:
Widder, J., Schmid, U.: Booting clock synchronization in partially synchronous systems with hybrid process and link failures.
Distributed Comput. 20(2), 115–140 (2007). https://doi.org/10.1007/S00446-007-0026-0
"""

from prelude import *


class Node(Finite): ...


class QuorumA(Finite): ...


class QuorumB(Finite): ...


class HybridReliableBroadcast(TransitionSystem):
    witness_exists_correct: Immutable[Node]  # used only for first proof
    witness_correct_not_accept: Immutable[Node]  # used only for second proof
    witness_correct_not_sent: Immutable[Node]  # used only for second proof
    witness_correct_and_accept: Immutable[Node]  # used only for second proof

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
            self.sent_msg.forall(
                lambda N1, N2: self.next.sent_msg(N1, N2)
                == Or(self.sent_msg(N1, N2), N1 == n)
            ),
            self.sent_msg_proj.update({(n,): Exists(N2, self.next.sent_msg(n, N2))}),
        )

    @transition
    def receive_msg(self, s: Node, n: Node) -> BoolRef:
        N2 = Node("N2")
        A = QuorumA("A")
        B = QuorumB("B")
        N = Node("N")
        return And(
            self.sent_msg(s, n),
            self.rcv_msg.update({(s, n): true}),
            If(
                Exists(
                    B, ForAll(N, Implies(self.member_b(N, B), self.next.rcv_msg(N, n)))
                ),
                self.accept.update({(n,): true}),
                self.accept.unchanged(),
            ),
            If(
                Exists(
                    A, ForAll(N, Implies(self.member_a(N, A), self.next.rcv_msg(N, n)))
                ),
                And(
                    self.sent_msg.forall(
                        lambda N1, N2: (
                            self.next.sent_msg(N1, N2)
                            == Or(self.sent_msg(N1, N2), N1 == n)
                        )
                    ),
                    self.sent_msg_proj.update(
                        {(n,): Exists(N2, self.next.sent_msg(n, N2))}
                    ),
                ),
                And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
            ),
        )

    # @transition
    def receive_msg_c(self, s: Node, n: Node) -> BoolRef:
        N2 = Node("N2")
        A = QuorumA("A")
        B = QuorumB("B")
        N = Node("N")
        return And(
            self.sent_msg(s, n),
            self.member_fc(n),
            self.rcv_msg.update({(s, n): true}),
            If(
                Exists(
                    B, ForAll(N, Implies(self.member_b(N, B), self.next.rcv_msg(N, n)))
                ),
                self.accept.update({(n,): true}),
                self.accept.unchanged(),
            ),
            If(
                Exists(
                    A, ForAll(N, Implies(self.member_a(N, A), self.next.rcv_msg(N, n)))
                ),
                Or(
                    And(
                        self.sent_msg.forall(
                            lambda N1, N2: self.next.sent_msg(N1, N2)
                            == Or(self.sent_msg(N1, N2), N1 == n)
                        ),
                        self.sent_msg_proj.update(
                            {(n,): Exists(N2, self.next.sent_msg(n, N2))}
                        ),
                    ),
                    And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
                ),
                And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
            ),
        )

    # @transition
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
            self.sent_msg_proj.update({(n,): Exists(N2, self.next.sent_msg(n, N2))}),
        )

    # @transition
    def trans_receive_msg_i(self, s: Node, n: Node) -> BoolRef:
        N1 = Node("N1")
        N2 = Node("N2")
        A = QuorumA("A")
        B = QuorumB("B")
        N = Node("N")
        return And(
            self.member_fi(n),
            self.sent_msg(s, n),
            self.rcv_msg.update({(s, n): true}),
            If(
                Exists(
                    B, ForAll(N, Implies(self.member_b(N, B), self.next.rcv_msg(N, n)))
                ),
                self.accept.update({(n,): true}),
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
                            {(n,): Exists(N2, self.next.sent_msg(n, N2))}
                        ),
                    ),
                    And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
                ),
                And(self.sent_msg.unchanged(), self.sent_msg_proj.unchanged()),
            ),
        )

    # @transition
    def trans_faulty_send_s(self, n: Node) -> BoolRef:
        N2 = Node("N2")
        return And(
            self.member_fs(n),
            self.accept.unchanged(),
            self.rcv_msg.unchanged(),
            self.sent_msg.forall(
                lambda N1, N2: self.next.sent_msg(N1, N2)
                == Or(self.sent_msg(N1, N2), N1 == n)
            ),
            self.sent_msg_proj.update({(n,): Exists(N2, self.next.sent_msg(n, N2))}),
        )

    # @transition
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

    # @transition
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
            self.sent_msg_proj.update({(n,): Exists(N2, self.next.sent_msg(n, N2))}),
        )
