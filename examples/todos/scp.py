"""
Stellar Consensus Protocol (SCP)

The Stellar Consensus Protocol provides federated Byzantine agreement.
This implementation is based on the Ivy specification.

https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy
"""

# pretty sure this can't work, i looked at the proof and it seems super complicated and requires using the cascade theorem in a complicated way.

from prelude import *


class Value(Expr): ...


class Node(Finite): ...


class NSet(Expr): ...


class Ballot(Expr): ...


class SCPSystem(TransitionSystem):
    well_behaved: Immutable[Rel[Node]]
    intertwined: Immutable[Rel[Node]]
    intact: Immutable[Rel[Node]]

    member: Immutable[Rel[Node, NSet]]
    is_quorum: Immutable[Rel[NSet]]
    blocks_slices: Immutable[Rel[NSet, Node]]

    lt: Immutable[Rel[Ballot, Ballot]]

    q0: Immutable[NSet]
    n0: Immutable[Node]
    p: Immutable[Rel[Node]]

    voted_prepared: Rel[Node, Ballot, Value]
    accepted_prepared: Rel[Node, Ballot, Value]
    confirmed_prepared: Rel[Node, Ballot, Value]
    voted_committed: Rel[Node, Ballot, Value]
    accepted_committed: Rel[Node, Ballot, Value]
    confirmed_committed: Rel[Node, Ballot, Value]
    nomination_output: Rel[Node, Value]
    started: Rel[Node, Ballot]
    left_ballot: Rel[Node, Ballot]

    received_vote_prepare: Rel[Node, Node, Ballot, Value]
    received_accept_prepare: Rel[Node, Node, Ballot, Value]
    received_vote_commit: Rel[Node, Node, Ballot, Value]
    received_accept_commit: Rel[Node, Node, Ballot, Value]

    @axiom
    def ballot_order_axioms(self, B1: Ballot, B2: Ballot, B3: Ballot) -> BoolRef:
        return And(
            Implies(And(self.lt(B1, B2), self.lt(B2, B3)), self.lt(B1, B3)),
            Implies(And(self.lt(B1, B2), self.lt(B2, B1)), false),
            Or(self.lt(B1, B2), self.lt(B2, B1), B1 == B2),
        )

    @axiom
    def node_properties(self, N: Node) -> BoolRef:
        return And(
            Implies(self.intact(N), self.intertwined(N)),
            Implies(self.intertwined(N), self.well_behaved(N)),
        )

    @axiom
    def quorum_intersection_intertwined(self, Q1: NSet, Q2: NSet) -> BoolRef:
        N1 = Node("N1")
        N2 = Node("N2")
        N3 = Node("N3")
        return Implies(
            And(
                self.is_quorum(Q1),
                self.is_quorum(Q2),
                Exists(N1, And(self.intertwined(N1), self.member(N1, Q1))),
                Exists(N2, And(self.intertwined(N2), self.member(N2, Q2))),
            ),
            Exists(
                N3,
                And(
                    self.well_behaved(N3),
                    self.member(N3, Q1),
                    self.member(N3, Q2),
                ),
            ),
        )

    @axiom
    def quorum_intersection_intact(self, Q1: NSet, Q2: NSet) -> BoolRef:
        N1 = Node("N1")
        N2 = Node("N2")
        N3 = Node("N3")
        return Implies(
            And(
                self.is_quorum(Q1),
                self.is_quorum(Q2),
                Exists(N1, And(self.intact(N1), self.member(N1, Q1))),
                Exists(N2, And(self.intact(N2), self.member(N2, Q2))),
            ),
            Exists(
                N3,
                And(self.intact(N3), self.member(N3, Q1), self.member(N3, Q2)),
            ),
        )

    @axiom
    def slice_blocks_ne(self, S: NSet) -> BoolRef:
        N = Node("N")
        N2 = Node("N2")
        return Implies(
            Exists(N, And(self.intact(N), self.blocks_slices(S, N))),
            Exists(N2, And(self.member(N2, S), self.intact(N2))),
        )

    @axiom
    def intact_is_quorum(self) -> BoolRef:
        Q = NSet("Q")
        N = Node("N")
        return Exists(
            Q,
            And(
                self.is_quorum(Q),
                ForAll(N, self.member(N, Q) == self.intact(N)),
            ),
        )

    @axiom
    def cascade_thm(self) -> BoolRef:
        N = Node("N")
        N2 = Node("N2")
        N3 = Node("N3")
        S = NSet("S")
        return And(
            And(
                self.is_quorum(self.q0),
                self.intact(self.n0),
                self.member(self.n0, self.q0),
            ),
            ForAll(
                N,
                Implies(
                    And(self.intact(N), self.member(N, self.q0)),
                    self.p(N),
                ),
            ),
            Or(
                ForAll(N, Implies(self.intact(N), self.p(N))),
                Exists(
                    [N2, S],
                    And(
                        self.intact(N2),
                        Not(self.p(N2)),
                        self.blocks_slices(S, N2),
                        ForAll(
                            N3,
                            Implies(
                                self.member(N3, S),
                                And(self.intact(N3), self.p(N3)),
                            ),
                        ),
                    ),
                ),
            ),
        )

    # definitions used later in transitions
    def quorum_na_member_received_vote_prepare_accept_prepare(
        self, na: Node, b: Ballot, v: Value
    ) -> BoolRef:
        Q = NSet("Q")
        N = Node("N")
        return Exists(
            Q,
            And(
                self.is_quorum(Q),
                self.member(na, Q),
                ForAll(
                    N,
                    Implies(
                        self.member(N, Q),
                        Or(
                            self.next.received_vote_prepare(na, N, b, v),
                            self.next.received_accept_prepare(na, N, b, v),
                        ),
                    ),
                ),
            ),
        )

    def quorum_na_member_received_accept_prepare(
        self, na: Node, b: Ballot, v: Value
    ) -> BoolRef:
        Q = NSet("Q")
        N = Node("N")
        return Exists(
            Q,
            And(
                self.is_quorum(Q),
                self.member(na, Q),
                ForAll(
                    N,
                    Implies(
                        self.member(N, Q),
                        self.next.received_accept_prepare(na, N, b, v),
                    ),
                ),
            ),
        )

    def quorum_na_member_received_vote_commit_or_accept_commit(
        self, na: Node, b: Ballot, v: Value
    ) -> BoolRef:
        Q = NSet("Q")
        N = Node("N")
        return Exists(
            Q,
            And(
                self.is_quorum(Q),
                self.member(na, Q),
                ForAll(
                    N,
                    Implies(
                        self.member(N, Q),
                        Or(
                            self.next.received_vote_commit(na, N, b, v),
                            self.next.received_accept_commit(na, N, b, v),
                        ),
                    ),
                ),
            ),
        )

    def quorum_na_member_received_accept_commit(
        self, na: Node, b: Ballot, v: Value
    ) -> BoolRef:
        Q = NSet("Q")
        N = Node("N")
        return Exists(
            Q,
            And(
                self.is_quorum(Q),
                self.member(na, Q),
                ForAll(
                    N,
                    Implies(
                        self.member(N, Q),
                        self.next.received_accept_commit(na, N, b, v),
                    ),
                ),
            ),
        )

    def slice_blocking_accept_prepare(self, na: Node, b: Ballot, v: Value) -> BoolRef:
        S = NSet("S")
        N = Node("N")
        return Exists(
            S,
            And(
                self.blocks_slices(S, na),
                ForAll(
                    N,
                    Implies(
                        self.member(N, S),
                        self.next.received_accept_prepare(na, N, b, v),
                    ),
                ),
            ),
        )

    def slice_blocking_accept_commit(self, na: Node, b: Ballot, v: Value) -> BoolRef:
        S = NSet("S")
        N = Node("N")
        return Exists(
            S,
            And(
                self.blocks_slices(S, na),
                ForAll(
                    N,
                    Implies(
                        self.member(N, S),
                        self.next.received_accept_commit(na, N, b, v),
                    ),
                ),
            ),
        )

    def no_higher_ballot_accepted_committed_different_value(
        self, na: Node, b: Ballot, v: Value
    ) -> BoolRef:
        B = Ballot("B")
        V = Value("V")
        return ForAll(
            [B, V],
            Not(
                And(
                    self.accepted_committed(na, B, V),
                    self.lt(B, b),
                    V != v,
                )
            ),
        )

    def no_higher_ballot_accepted_prepared_different_value(
        self, na: Node, b: Ballot, v: Value
    ) -> BoolRef:
        B = Ballot("B")
        V = Value("V")
        return ForAll(
            [B, V],
            Not(
                And(
                    self.accepted_prepared(na, B, V),
                    self.lt(b, B),
                    V != v,
                )
            ),
        )

    def no_accepted_prepared_value(self, na: Node, b: Ballot) -> BoolRef:
        V = Value("V")
        return ForAll(V, Not(self.accepted_prepared(na, b, V)))

    def not_accepted_committed_twice(self, na: Node, b: Ballot) -> BoolRef:
        V = Value("V")
        return ForAll(V, Not(self.accepted_committed(na, b, V)))

    @init
    def initial(self, N: Node, N1: Node, N2: Node, B: Ballot, V: Value) -> BoolRef:
        return And(
            Not(self.voted_prepared(N, B, V)),
            Not(self.accepted_prepared(N, B, V)),
            Not(self.confirmed_prepared(N, B, V)),
            Not(self.voted_committed(N, B, V)),
            Not(self.accepted_committed(N, B, V)),
            Not(self.confirmed_committed(N, B, V)),
            Not(self.nomination_output(N, V)),
            Not(self.left_ballot(N, B)),
            Not(self.started(N, B)),
            Not(self.received_vote_prepare(N1, N2, B, V)),
            Not(self.received_accept_prepare(N1, N2, B, V)),
            Not(self.received_vote_commit(N1, N2, B, V)),
            Not(self.received_accept_commit(N1, N2, B, V)),
        )

    @transition
    def nomination_update(self, n: Node, v: Value) -> BoolRef:
        N = Node("N")
        V = Value("V")
        return And(
            ForAll(
                [N, V],
                self.next.nomination_output(N, V)
                == If(N == n, V == v, self.nomination_output(N, V)),
            ),
            self.voted_prepared.unchanged(),
            self.accepted_prepared.unchanged(),
            self.confirmed_prepared.unchanged(),
            self.voted_committed.unchanged(),
            self.accepted_committed.unchanged(),
            self.confirmed_committed.unchanged(),
            self.started.unchanged(),
            self.left_ballot.unchanged(),
            self.received_vote_prepare.unchanged(),
            self.received_accept_prepare.unchanged(),
            self.received_vote_commit.unchanged(),
            self.received_accept_commit.unchanged(),
        )

    @transition
    def change_ballot(self, n: Node, b: Ballot) -> BoolRef:
        B = Ballot("B")
        N = Node("N")
        B_MAX = Ballot("B_MAX")
        V_MAX = Value("V_MAX")
        V = Value("V")
        return And(
            Not(self.left_ballot(n, b)),
            Not(self.started(n, b)),
            ForAll(
                [N, B],
                self.next.left_ballot(N, B)
                == If(N == n, self.lt(B, b), self.left_ballot(N, B)),
            ),
            ForAll(
                [N, B],
                self.next.started(N, B)
                == If(And(N == n, B == b), true, self.started(N, B)),
            ),
            Exists(
                [B_MAX, V_MAX],
                And(
                    Or(
                        And(
                            ForAll(
                                [B, V],
                                Implies(
                                    self.lt(B, b),
                                    Not(self.confirmed_prepared(n, B, V)),
                                ),
                            ),
                            self.nomination_output(n, V_MAX),
                        ),
                        And(
                            self.lt(B_MAX, b),
                            self.confirmed_prepared(n, B_MAX, V_MAX),
                            ForAll(
                                [B, V],
                                Implies(
                                    And(
                                        self.lt(B, b),
                                        self.confirmed_prepared(n, B, V),
                                    ),
                                    Not(self.lt(B_MAX, B)),
                                ),
                            ),
                        ),
                    ),
                    self.voted_prepared.update({(n, b, V_MAX): true}),
                ),
            ),
            self.accepted_prepared.unchanged(),
            self.confirmed_prepared.unchanged(),
            self.voted_committed.unchanged(),
            self.accepted_committed.unchanged(),
            self.confirmed_committed.unchanged(),
            self.nomination_output.unchanged(),
            self.received_vote_prepare.unchanged(),
            self.received_accept_prepare.unchanged(),
            self.received_vote_commit.unchanged(),
            self.received_accept_commit.unchanged(),
        )

    @transition
    def receive_vote_prepare(self, na: Node, nb: Node, b: Ballot, v: Value) -> BoolRef:
        return And(
            self.voted_prepared(nb, b, v),
            self.received_vote_prepare.update({(na, nb, b, v): true}),
            If(
                And(
                    self.quorum_na_member_received_vote_prepare_accept_prepare(
                        na, b, v
                    ),
                    self.no_higher_ballot_accepted_committed_different_value(na, b, v),
                    self.no_accepted_prepared_value(na, b),
                ),
                self.accepted_prepared.update({(na, b, v): true}),
                self.accepted_prepared.unchanged(),
            ),
            self.voted_prepared.unchanged(),
            self.confirmed_prepared.unchanged(),
            self.voted_committed.unchanged(),
            self.accepted_committed.unchanged(),
            self.confirmed_committed.unchanged(),
            self.nomination_output.unchanged(),
            self.started.unchanged(),
            self.left_ballot.unchanged(),
            self.received_accept_prepare.unchanged(),
            self.received_vote_commit.unchanged(),
            self.received_accept_commit.unchanged(),
        )

    @transition
    def receive_accept_prepare(
        self, na: Node, nb: Node, b: Ballot, v: Value
    ) -> BoolRef:
        return And(
            self.accepted_prepared(nb, b, v),
            self.received_accept_prepare.update({(na, nb, b, v): true}),
            If(
                self.quorum_na_member_received_accept_prepare(na, b, v),
                And(
                    self.confirmed_prepared.update({(na, b, v): true}),
                    If(
                        Not(self.left_ballot(na, b)),
                        self.voted_committed.update({(na, b, v): true}),
                        self.voted_committed.unchanged(),
                    ),
                ),
                And(
                    self.confirmed_prepared.unchanged(),
                    self.voted_committed.unchanged(),
                ),
            ),
            If(
                And(
                    Or(
                        self.quorum_na_member_received_vote_prepare_accept_prepare(
                            na, b, v
                        ),
                        self.slice_blocking_accept_prepare(na, b, v),
                    ),
                    self.no_higher_ballot_accepted_committed_different_value(na, b, v),
                    self.no_accepted_prepared_value(na, b),
                ),
                self.accepted_prepared.update({(na, b, v): true}),
                self.accepted_prepared.unchanged(),
            ),
            self.voted_prepared.unchanged(),
            self.voted_committed.unchanged(),
            self.accepted_committed.unchanged(),
            self.confirmed_committed.unchanged(),
            self.nomination_output.unchanged(),
            self.started.unchanged(),
            self.left_ballot.unchanged(),
            self.received_vote_prepare.unchanged(),
            self.received_vote_commit.unchanged(),
            self.received_accept_commit.unchanged(),
        )

    @transition
    def receive_vote_commit(self, na: Node, nb: Node, b: Ballot, v: Value) -> BoolRef:
        return And(
            self.voted_committed(nb, b, v),
            self.received_vote_commit.update({(na, nb, b, v): true}),
            If(
                And(
                    self.quorum_na_member_received_vote_commit_or_accept_commit(
                        na, b, v
                    ),
                    self.no_higher_ballot_accepted_prepared_different_value(na, b, v),
                    self.not_accepted_committed_twice(na, b),
                    self.confirmed_prepared(na, b, v),
                ),
                self.accepted_committed.update({(na, b, v): true}),
                self.accepted_committed.unchanged(),
            ),
            self.voted_prepared.unchanged(),
            self.accepted_prepared.unchanged(),
            self.confirmed_prepared.unchanged(),
            self.voted_committed.unchanged(),
            self.confirmed_committed.unchanged(),
            self.nomination_output.unchanged(),
            self.started.unchanged(),
            self.left_ballot.unchanged(),
            self.received_vote_prepare.unchanged(),
            self.received_accept_prepare.unchanged(),
            self.received_accept_commit.unchanged(),
        )

    @transition
    def receive_accept_commit(self, na: Node, nb: Node, b: Ballot, v: Value) -> BoolRef:
        return And(
            self.accepted_committed(nb, b, v),
            self.received_accept_commit.update({(na, nb, b, v): true}),
            If(
                self.quorum_na_member_received_accept_commit(na, b, v),
                self.confirmed_committed.update({(na, b, v): true}),
                self.confirmed_committed.unchanged(),
            ),
            If(
                And(
                    Or(
                        self.quorum_na_member_received_vote_commit_or_accept_commit(
                            na, b, v
                        ),
                        self.slice_blocking_accept_commit(na, b, v),
                    ),
                    self.no_higher_ballot_accepted_prepared_different_value(na, b, v),
                    self.not_accepted_committed_twice(na, b),
                    self.confirmed_prepared(na, b, v),
                ),
                self.accepted_committed.update({(na, b, v): true}),
                self.accepted_committed.unchanged(),
            ),
            self.voted_prepared.unchanged(),
            self.accepted_prepared.unchanged(),
            self.confirmed_prepared.unchanged(),
            self.voted_committed.unchanged(),
            self.nomination_output.unchanged(),
            self.started.unchanged(),
            self.left_ballot.unchanged(),
            self.received_vote_prepare.unchanged(),
            self.received_accept_prepare.unchanged(),
            self.received_vote_commit.unchanged(),
        )

    @transition
    def byzantine_step(self) -> BoolRef:
        N = Node("N")
        N1 = Node("N1")
        N2 = Node("N2")
        B = Ballot("B")
        V = Value("V")
        return And(
            ForAll(
                [N, B, V],
                Implies(
                    self.well_behaved(N),
                    And(
                        self.next.voted_prepared(N, B, V)
                        == self.voted_prepared(N, B, V),
                        self.next.accepted_prepared(N, B, V)
                        == self.accepted_prepared(N, B, V),
                        self.next.voted_committed(N, B, V)
                        == self.voted_committed(N, B, V),
                        self.next.accepted_committed(N, B, V)
                        == self.accepted_committed(N, B, V),
                        self.next.confirmed_prepared(N, B, V)
                        == self.confirmed_prepared(N, B, V),
                        self.next.confirmed_committed(N, B, V)
                        == self.confirmed_committed(N, B, V),
                        self.next.nomination_output(N, V)
                        == self.nomination_output(N, V),
                        self.next.started(N, B) == self.started(N, B),
                        self.next.left_ballot(N, B) == self.left_ballot(N, B),
                    ),
                ),
            ),
            ForAll(
                [N1, N2, B, V],
                Implies(
                    self.well_behaved(N1),
                    And(
                        self.next.received_vote_prepare(N1, N2, B, V)
                        == self.received_vote_prepare(N1, N2, B, V),
                        self.next.received_accept_prepare(N1, N2, B, V)
                        == self.received_accept_prepare(N1, N2, B, V),
                        self.next.received_vote_commit(N1, N2, B, V)
                        == self.received_vote_commit(N1, N2, B, V),
                        self.next.received_accept_commit(N1, N2, B, V)
                        == self.received_accept_commit(N1, N2, B, V),
                    ),
                ),
            ),
        )
