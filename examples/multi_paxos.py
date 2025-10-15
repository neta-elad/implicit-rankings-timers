from prelude import *

# @ status - in progress

# Multi-Paxos consensus protocol implementation
# Based on the Ivy implementation in multi_paxos_liveness.ivy


class Node(Finite): ...


class Value(Expr): ...


class Quorum(Finite): ...


class Round(Finite): ...


class Inst(Finite): ...


class Votemap(Finite): ...


class MultiPaxosSystem(TransitionSystem):
    none: Immutable[Round]
    le: Immutable[Rel[Round, Round]]  # total order on rounds
    member: Immutable[Rel[Node, Quorum]]  # quorum membership
    r0: Immutable[Round]  # the round after which no ballot must be started
    q0: Immutable[Quorum]  # the quorum that must be responsive
    i0: Immutable[
        Inst
    ]  # the instance in which nothing is chosen (from negation of liveness property)

    # Functions for votemap operations
    maxr: Immutable[
        Fun[Votemap, Inst, Round]
    ]  # maxr(M,I) = the round of the max vote for instance I in votemap M
    maxv: Immutable[
        Fun[Votemap, Inst, Value]
    ]  # maxv(M,I) = the value of the max vote for instance I in votemap M

    one_a: Rel[Round]
    one_b_msg: Rel[Node, Round, Votemap]
    proposal: Rel[Inst, Round, Value]  # 2a messages
    active: Rel[
        Round
    ]  # round R has received a quorum of 1b and can now propose new values
    vote: Rel[Node, Inst, Round, Value]  # 2b messages

    # Tracking fairness of message arrival
    one_b_votemap_received: Rel[Round, Node, Votemap]
    one_a_received: Rel[Node, Round]
    proposal_received: Rel[Node, Inst, Round, Value]
    join_acks_called: Rel[Round]  # process_join_acks is called with round r
    propose_called: Rel[Round, Inst]  # propose is called with round r and instance i

    # Projection relations for abstraction
    proposed: Rel[
        Inst, Round
    ]  # invariant: proposed(I,R) <-> exists V . proposal(I,R,V)
    one_b_received: Rel[
        Round, Node
    ]  # invariant: one_b_received(R,N) <-> exists M . one_b_votemap_received(R,N,M)
    skolem_value: Immutable[
        Value
    ]  # skolem_value that will be proposed in r0 and voted for in i0 ### not sure this works, but temp

    @axiom
    def total_order_axioms(self, X: Round, Y: Round, Z: Round) -> BoolRef:
        return And(
            self.le(X, X),
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Or(self.le(X, Y), self.le(Y, X)),
        )

    @axiom
    def none_is_minimal(self, R: Round) -> BoolRef:
        return self.le(self.none, R)

    @axiom
    def quorum_intersection(self, Q1: Quorum, Q2: Quorum) -> BoolRef:
        N = Node("N")
        return Exists(N, And(self.member(N, Q1), self.member(N, Q2)))

    @axiom
    def r0_not_none(self) -> BoolRef:
        return self.r0 != self.none

    @init
    def initial(self, R: Round, N: Node, I: Inst, V: Value, M: Votemap) -> BoolRef:
        return And(
            # Initialize all protocol relations to false
            Not(self.one_a(R)),
            Not(self.one_b_msg(N, R, M)),
            Not(self.proposal(I, R, V)),
            Not(self.vote(N, I, R, V)),
            Not(self.active(R)),
            Not(self.one_b_votemap_received(R, N, M)),
            Not(self.one_a_received(N, R)),
            Not(self.proposal_received(N, I, R, V)),
            Not(self.proposed(I, R)),
            Not(self.one_b_received(R, N)),
        )

    @transition
    def send_1a(self, r: Round) -> BoolRef:
        I = Inst("I")
        R = Round("R")
        return And(
            # guard
            r != self.none,
            Not(self.one_a(r)),
            ForAll(R, Not(self.join_acks_called(R))),
            ForAll([R, I], Not(self.propose_called(R, I))),
            # self.le(r, self.r0),  # assumption for liveness (the "fairness" assumption) # will be added to property
            # updates
            self.one_a.update({(r,): true}),
            # other relations unchanged
            self.one_b_msg.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.active.unchanged(),
            self.one_b_votemap_received.unchanged(),
            self.one_a_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def join_round(self, n: Node, r: Round, m: Votemap) -> BoolRef:
        R = Round("R")
        M = Votemap("M")
        I = Inst("I")
        V = Value("V")
        return And(
            # guard
            r != self.none,
            self.one_a(r),
            ForAll(R, Not(self.join_acks_called(R))),
            ForAll([R, I], Not(self.propose_called(R, I))),
            self.one_a_received.update({(n, r): true}),
            # find the maximal vote in a round less than r, for all instances
            If(
                ForAll(
                    [R, M],
                    Implies(self.one_b_msg(n, R, M), self.le(R, r)),
                ),
                And(
                    # For each instance I, either:
                    # 1. maxr(m,I) = none and no votes in rounds >= r, OR
                    # 2. maxr(m,I) != none and it's the maximal round < r with a vote
                    ForAll(
                        I,
                        Or(
                            And(
                                self.maxr(m, I) == self.none,
                                ForAll(
                                    [R, V],
                                    Not(And(self.vote(n, I, R, V), Not(self.le(r, R)))),
                                ),
                            ),
                            And(
                                self.vote(n, I, self.maxr(m, I), self.maxv(m, I)),
                                Not(self.le(r, self.maxr(m, I))),
                                ForAll(
                                    [R, V],
                                    Implies(
                                        And(self.vote(n, I, R, V), Not(self.le(r, R))),
                                        self.le(R, self.maxr(m, I)),
                                    ),
                                ),
                            ),
                        ),
                    ),
                    # send the 1b message
                    self.one_b_msg.update({(n, r, m): true}),
                ),
                self.one_b_msg.unchanged(),
            ),
            # other relations unchanged
            self.one_a.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.active.unchanged(),
            self.one_b_votemap_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def receive_one_b(self, r: Round, n: Node, m: Votemap) -> BoolRef:
        I = Inst("I")
        R = Round("R")
        return And(
            # guard
            r != self.none,
            self.one_b_msg(n, r, m),
            ForAll(R, Not(self.join_acks_called(R))),
            ForAll([R, I], Not(self.propose_called(R, I))),
            # updates
            self.one_b_votemap_received.update({(r, n, m): true}),
            self.one_b_received.update({(r, n): true}),
            # other relations unchanged
            self.one_a.unchanged(),
            self.one_b_msg.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.active.unchanged(),
            self.one_a_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
        )

    @transition
    def process_join_acks(self, r: Round, q: Quorum, m: Votemap) -> BoolRef:
        N = Node("N")
        M = Votemap("M")
        I = Inst("I")
        V = Value("V")
        Q = Quorum("Q")
        R = Round("R")
        return And(
            # guard
            r != self.none,
            ForAll(R, self.join_acks_called(R) == (R == r)),
            ForAll([R, I], Not(self.propose_called(R, I))),
            Implies(
                ForAll(
                    [N, Q],
                    Implies(
                        self.member(N, Q),
                        Exists(M, self.one_b_votemap_received(r, N, M)),
                    ),
                ),
                ForAll(
                    N,
                    Implies(
                        self.member(N, q),
                        Exists(M, self.one_b_votemap_received(r, N, M)),
                    ),
                ),
            ),
            If(
                And(
                    Not(self.active(r)),
                    ForAll(
                        N,
                        Implies(
                            self.member(N, q),
                            Exists(M, self.one_b_votemap_received(r, N, M)),
                        ),
                    ),
                ),
                And(
                    # find the maximal vote in the quorum for each instance
                    ForAll(
                        I,
                        Or(
                            And(
                                self.maxr(m, I) == self.none,
                                ForAll(
                                    [N, M],
                                    Not(
                                        And(
                                            self.member(N, q),
                                            self.one_b_votemap_received(r, N, M),
                                            self.maxr(M, I) != self.none,
                                        )
                                    ),
                                ),
                            ),
                            And(
                                Exists(
                                    [N, M],
                                    And(
                                        self.member(N, q),
                                        self.one_b_votemap_received(r, N, M),
                                        self.maxr(M, I) != self.none,
                                        self.maxr(M, I) == self.maxr(m, I),
                                        self.maxv(M, I) == self.maxv(m, I),
                                    ),
                                ),
                                ForAll(
                                    [N, M],
                                    Implies(
                                        And(
                                            self.member(N, q),
                                            self.one_b_votemap_received(r, N, M),
                                            self.maxr(M, I) != self.none,
                                        ),
                                        self.le(self.maxr(M, I), self.maxr(m, I)),
                                    ),
                                ),
                            ),
                        ),
                    ),
                    # updates
                    self.active.update({(r,): true}),
                    # propose in all instances in which some vote was reported
                    ForAll(
                        [I, V],
                        self.next.proposal(I, r, V)
                        == Or(
                            self.proposal(I, r, V),
                            And(self.maxr(m, I) != self.none, V == self.maxv(m, I)),
                        ),
                    ),
                    ForAll(
                        I,
                        self.next.proposed(I, r)
                        == Or(self.proposed(I, r), self.maxr(m, I) != self.none),
                    ),
                ),
                And(
                    self.active.unchanged(),
                    self.proposal.unchanged(),
                    self.proposed.unchanged(),
                ),
            ),
            # other relations unchanged
            self.one_a.unchanged(),
            self.one_b_msg.unchanged(),
            self.vote.unchanged(),
            self.one_b_votemap_received.unchanged(),
            self.one_a_received.unchanged(),
            self.proposal_received.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def propose(self, r: Round, i: Inst, v: Value) -> BoolRef:
        V = Value("V")
        R = Round("R")
        I = Inst("I")
        return And(
            # guard
            r != self.none,
            ForAll(R, Not(self.join_acks_called(R))),
            ForAll([R, I], self.propose_called(R, I) == (R == r and I == i)),
            If(
                And(self.active(r), ForAll(V, Not(self.proposal(i, r, V)))),
                And(
                    self.proposal.update({(i, r, v): true}),
                    self.proposed.update({(i, r): true}),
                ),
                And(self.proposal.unchanged(), self.proposed.unchanged()),
            ),
            # other relations unchanged
            self.one_a.unchanged(),
            self.one_b_msg.unchanged(),
            self.vote.unchanged(),
            self.active.unchanged(),
            self.one_b_votemap_received.unchanged(),
            self.one_a_received.unchanged(),
            self.proposal_received.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def cast_vote(self, n: Node, v: Value, r: Round, i: Inst) -> BoolRef:
        R = Round("R")
        M = Votemap("M")
        V = Value("V")
        I = Inst("I")
        return And(
            # guard
            r != self.none,
            self.proposal(i, r, v),
            ForAll(R, Not(self.join_acks_called(R))),
            ForAll([R, I], Not(self.propose_called(R, I))),
            self.proposal_received.update({(n, i, r, v): true}),
            If(
                And(
                    ForAll(
                        [R, M],
                        Implies(self.one_b_msg(n, R, M), self.le(R, r)),
                    ),
                    ForAll(V, Not(self.vote(n, i, r, V))),
                ),
                And(
                    self.vote.update({(n, i, r, v): true}),
                    # (in ivy)
                    # from negation of the liveness property:
                    # if i = i0 & exists Q . forall N . member(N,Q) -> vote(N,i0,r0,v) {
                    #     assume false
                    # }
                    # This is handled by the property, not here
                ),
                self.vote.unchanged(),
            ),
            # other relations unchanged
            self.one_a.unchanged(),
            self.one_b_msg.unchanged(),
            self.proposal.unchanged(),
            self.active.unchanged(),
            self.one_b_votemap_received.unchanged(),
            self.one_a_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )


# to review
# Property: For every instance, a quorum of nodes eventually votes for the same value in round r0
class MultiPaxosProperty(Prop[MultiPaxosSystem]):
    def prop(self) -> BoolRef:
        V = Value("V")
        Q = Quorum("Q")
        N = Node("N")
        R = Round("R")
        I = Inst("I")
        M = Votemap("M")
        fairness_conditions = And(
            F(self.sys.one_a(self.sys.r0)),
            G(
                ForAll(
                    R,
                    Implies(
                        self.sys.one_a(R),
                        self.sys.le(R, self.sys.r0),
                    ),
                )
            ),
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    And(
                        G(
                            Implies(
                                self.sys.one_a(self.sys.r0),
                                F(self.sys.one_a_received(N, self.sys.r0)),
                            )
                        ),
                        ForAll(
                            M,
                            G(
                                Implies(
                                    self.sys.one_b_msg(N, self.sys.r0, M),
                                    F(self.sys.one_b_received(self.sys.r0, N)),
                                )
                            ),  # this is slightly different from the ivy comment, which doesn't make sense
                        ),
                        ForAll(
                            [I, V],
                            G(
                                Implies(
                                    self.sys.proposal(I, self.sys.r0, V),
                                    F(self.sys.proposal_received(N, I, self.sys.r0, V)),
                                )
                            ),
                        ),
                    ),
                ),
            ),
            ForAll(
                I,
                G(
                    F(self.sys.propose_called(self.sys.r0, I))
                ),  # slightly different from ivy, we use propose_called
            ),
            G(
                F(self.sys.join_acks_called(self.sys.r0))
            ),  # slightly different from ivy, we use join_acks_called
        )

        liveness_property = Exists(
            [Q],
            F(
                ForAll(
                    N,
                    Implies(
                        self.sys.member(N, Q),
                        self.sys.vote(
                            N, self.sys.i0, self.sys.r0, self.sys.skolem_value
                        ),
                    ),
                )
            ),
        )

        return Implies(fairness_conditions, liveness_property)


class MultiPaxosProof(Proof[MultiPaxosSystem], prop=MultiPaxosProperty):

    @temporal_invariant
    def fairness(self) -> BoolRef:
        R = Round("R")
        N = Node("N")
        M = Votemap("M")
        I = Inst("I")
        V = Value("V")
        return And(
            F(self.sys.one_a(self.sys.r0)),
            G(
                ForAll(
                    R,
                    Implies(
                        self.sys.one_a(R),
                        self.sys.le(R, self.sys.r0),
                    ),
                )
            ),
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    And(
                        G(
                            Implies(
                                self.sys.one_a(self.sys.r0),
                                F(self.sys.one_a_received(N, self.sys.r0)),
                            )
                        ),
                        ForAll(
                            M,
                            G(
                                Implies(
                                    self.sys.one_b_msg(N, self.sys.r0, M),
                                    F(self.sys.one_b_received(self.sys.r0, N)),
                                )
                            ),  # this is slightly different from the ivy comment, which doesn't make sense
                        ),
                        ForAll(
                            [I, V],
                            G(
                                Implies(
                                    self.sys.proposal(I, self.sys.r0, V),
                                    F(self.sys.proposal_received(N, I, self.sys.r0, V)),
                                )
                            ),
                        ),
                    ),
                ),
            ),
            ForAll(
                I,
                G(
                    F(self.sys.propose_called(self.sys.r0, I))
                ),  # slightly different from ivy, we use propose_called
            ),
            G(
                F(self.sys.join_acks_called(self.sys.r0))
            ),  # slightly different from ivy, we use join_acks_called
        )

    # Proposals are unique per round
    # @invariant
    def active_implies_no_proposal(self, R: Round, I: Inst, V: Value) -> BoolRef:
        return Implies(Not(self.sys.active(R)), Not(self.sys.proposal(I, R, V)))

    # @invariant
    def proposal_uniqueness(self, I: Inst, R: Round, V1: Value, V2: Value) -> BoolRef:
        return Implies(
            And(self.sys.proposal(I, R, V1), self.sys.proposal(I, R, V2)), V1 == V2
        )

    # Only vote for proposed values
    # @invariant
    def vote_proposal_consistency(
        self, N: Node, I: Inst, R: Round, V: Value
    ) -> BoolRef:
        return Implies(self.sys.vote(N, I, R, V), self.sys.proposal(I, R, V))

    # Nothing happens after r0
    @invariant
    def no_one_a_after_r0(self, R: Round) -> BoolRef:
        return Implies(self.sys.one_a(R), self.sys.le(R, self.sys.r0))

    @invariant
    def no_one_b_msg_after_r0(self, N: Node, R: Round, M: Votemap) -> BoolRef:
        return Implies(self.sys.one_b_msg(N, R, M), self.sys.le(R, self.sys.r0))

    @invariant
    def no_one_b_votemap_received_after_r0(
        self, R: Round, N: Node, M: Votemap
    ) -> BoolRef:
        return Implies(
            self.sys.one_b_votemap_received(R, N, M), self.sys.le(R, self.sys.r0)
        )

    @invariant
    def no_one_b_msg_maxr_after_r0(
        self, N: Node, R: Round, M: Votemap, I: Inst
    ) -> BoolRef:
        return Implies(
            self.sys.one_b_msg(N, R, M), self.sys.le(self.sys.maxr(M, I), self.sys.r0)
        )

    @invariant
    def no_proposal_after_r0(self, I: Inst, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.proposal(I, R, V), self.sys.le(R, self.sys.r0))

    @invariant
    def no_vote_after_r0(self, N: Node, I: Inst, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.vote(N, I, R, V), self.sys.le(R, self.sys.r0))

    # @invariant
    def no_active_after_r0(self, R: Round) -> BoolRef:
        return Implies(self.sys.active(R), self.sys.le(R, self.sys.r0))

    # Projection properties
    # @invariant
    def projection_proposal(self, I: Inst, R: Round) -> BoolRef:
        V = Value("V")
        return self.sys.proposed(I, R) == Exists(V, self.sys.proposal(I, R, V))

    # @invariant
    def proposal_received_implies_proposed(
        self, N: Node, I: Inst, R: Round, V: Value
    ) -> BoolRef:
        return Implies(self.sys.proposal_received(N, I, R, V), self.sys.proposed(I, R))

    # @invariant
    def one_b_received_projection(self, R: Round, N: Node) -> BoolRef:
        M = Votemap("M")
        return self.sys.one_b_received(R, N) == Exists(
            M, self.sys.one_b_votemap_received(R, N, M)
        )

    # Progress conjectures for r0 and i0 - if msg a is received, msg b is sent
    # @invariant
    def one_a_received_iff_one_b_msg(self, N: Node) -> BoolRef:
        M = Votemap("M")
        return self.sys.one_a_received(N, self.sys.r0) == Exists(
            M, self.sys.one_b_msg(N, self.sys.r0, M)
        )

    # @invariant
    def proposal_received_iff_vote(self, N: Node, V: Value) -> BoolRef:
        return self.sys.proposal_received(
            N, self.sys.i0, self.sys.r0, V
        ) == self.sys.vote(N, self.sys.i0, self.sys.r0, V)

    # Once a proposal is sent, we will always wait for at least one node
    # @invariant
    # def exists_node_not_voted(self) -> BoolRef:
    #     N = Node("N")
    #     V = Value("V")
    #     return Exists(N, ForAll(V, And(self.sys.member(N, self.sys.q0), Not(self.sys.vote(N, self.sys.i0, self.sys.r0, V)))))

    def rank(self) -> Rank:
        return BinRank(true)


proof = MultiPaxosProof()
proof.check()
