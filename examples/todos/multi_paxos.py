"""
Multi-Paxos Consensus Protocol Implementation

Based on the Ivy implementation in multi_paxos_liveness.ivy
"""

# @status - todo

from prelude import *


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

    # Functions for votemap type
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
            ForAll(R, self.join_acks_called(R) == (R == r)),  # fairness relations
            ForAll([R, I], Not(self.propose_called(R, I))),  # fairness relations
            Implies(
                Exists(
                    Q,
                    ForAll(
                        N,
                        Implies(
                            self.member(N, Q),
                            Exists(M, self.one_b_votemap_received(r, N, M)),
                        ),
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
                        [I, R, V],
                        self.next.proposal(I, R, V)
                        == Or(
                            self.proposal(I, R, V),
                            And(
                                R == r,
                                self.maxr(m, I) != self.none,
                                V == self.maxv(m, I),
                            ),
                        ),  # this is what the ivy syntax unpacks to.
                    ),
                    ForAll(
                        [I, R],
                        self.next.proposed(I, R)
                        == Or(
                            self.proposed(I, R),
                            And(R == r, self.maxr(m, I) != self.none),
                        ),
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
            ForAll([R, I], self.propose_called(R, I) == And(R == r, I == i)),
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
            [V, Q, I],
            F(
                ForAll(
                    N,
                    Implies(
                        self.sys.member(N, Q),
                        self.sys.vote(N, self.sys.i0, self.sys.r0, V),
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
                            ),
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
                G(F(self.sys.propose_called(self.sys.r0, I))),
            ),
            G(F(self.sys.join_acks_called(self.sys.r0))),
        )

    @system_invariant
    def not_active_implies_no_proposal(self, R: Round, I: Inst, V: Value) -> BoolRef:
        return Implies(Not(self.sys.active(R)), Not(self.sys.proposal(I, R, V)))

    @system_invariant
    def proposal_uniqueness(self, I: Inst, R: Round, V1: Value, V2: Value) -> BoolRef:
        return Implies(
            And(self.sys.proposal(I, R, V1), self.sys.proposal(I, R, V2)), V1 == V2
        )

    @system_invariant
    def vote_proposal_consistency(
        self, N: Node, I: Inst, R: Round, V: Value
    ) -> BoolRef:
        return Implies(self.sys.vote(N, I, R, V), self.sys.proposal(I, R, V))

    # Nothing happens after r0
    @invariant
    def no_one_a_after_r0(self, R: Round) -> BoolRef:
        return Implies(self.sys.one_a(R), self.sys.le(R, self.sys.r0))

    @invariant(omit_timer_axioms_in_init=True)
    def no_one_b_msg_after_r0(self, N: Node, R: Round, M: Votemap) -> BoolRef:
        return Implies(self.sys.one_b_msg(N, R, M), self.sys.le(R, self.sys.r0))

    @invariant(omit_timer_axioms_in_init=True)
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

    @invariant(omit_timer_axioms_in_init=True)
    def no_proposal_after_r0(self, I: Inst, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.proposal(I, R, V), self.sys.le(R, self.sys.r0))

    @invariant(omit_timer_axioms_in_init=True)
    def no_vote_after_r0(self, N: Node, I: Inst, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.vote(N, I, R, V), self.sys.le(R, self.sys.r0))

    @invariant
    def no_active_after_r0(self, R: Round) -> BoolRef:
        return Implies(self.sys.active(R), self.sys.le(R, self.sys.r0))

    # Projection properties
    @system_invariant
    def projection_proposal(self, I: Inst, R: Round) -> BoolRef:
        V = Value("V")
        return self.sys.proposed(I, R) == Exists(V, self.sys.proposal(I, R, V))

    @system_invariant
    def proposal_received_implies_proposed(
        self, N: Node, I: Inst, R: Round, V: Value
    ) -> BoolRef:
        return Implies(self.sys.proposal_received(N, I, R, V), self.sys.proposed(I, R))

    @system_invariant
    def one_b_received_projection(self, R: Round, N: Node) -> BoolRef:
        M = Votemap("M")
        return self.sys.one_b_received(R, N) == Exists(
            M, self.sys.one_b_votemap_received(R, N, M)
        )

    # Progress conjectures for r0 and i0 - if msg a is received, msg b is sent
    @invariant(omit_timer_axioms_in_init=True)
    def one_a_received_iff_one_b_msg(self, N: Node) -> BoolRef:
        M = Votemap("M")
        return self.sys.one_a_received(N, self.sys.r0) == Exists(
            M, self.sys.one_b_msg(N, self.sys.r0, M)
        )

    @invariant(omit_timer_axioms_in_init=True)
    def proposal_received_iff_vote(self, N: Node, V: Value) -> BoolRef:
        return self.sys.proposal_received(
            N, self.sys.i0, self.sys.r0, V
        ) == self.sys.vote(N, self.sys.i0, self.sys.r0, V)

    # need to think about this:
    # Once a proposal is sent, we will always wait for at least one node
    # @invariant
    # def exists_node_not_voted(self) -> BoolRef:
    #     N = Node("N")
    #     V = Value("V")
    #     return Exists(N, ForAll(V, And(self.sys.member(N, self.sys.q0), Not(self.sys.vote(N, self.sys.i0, self.sys.r0, V)))))

    # ranks

    def one_a_r0_timer_rank(self) -> Rank:
        return self.timer_rank(self.sys.one_a(self.sys.r0), None, None)

    def one_a_received_r0(self, N: Node) -> BoolRef:
        return self.sys.one_a_received(N, self.sys.r0)

    def one_a_received_timer_rank(self) -> Rank:
        return self.timer_rank(self.one_a_received_r0, None, None)

    def one_b_received_r0(self, N: Node) -> BoolRef:
        return self.sys.one_b_received(self.sys.r0, N)

    def one_b_received_timer_rank(self) -> Rank:
        return self.timer_rank(self.one_b_received_r0, None, None)

    # rank that decreases when a proposal is made
    def no_proposed_in_r0_and_i0(self) -> BoolRef:
        return Not(self.sys.proposed(self.sys.i0, self.sys.r0))

    def binary_no_proposed_in_r0_and_i0(self) -> Rank:
        return BinRank(self.no_proposed_in_r0_and_i0())

    def r0_not_active(self) -> BoolRef:
        return Not(self.sys.active(self.sys.r0))

    def binary_r0_not_active(self) -> Rank:
        return BinRank(self.r0_not_active())

    def proposal_received_in_r0(self, N: Node, I: Inst, V: Value) -> BoolRef:
        return self.sys.proposal_received(N, I, self.sys.r0, V)

    def proposal_receiver_in_r0_timer(self) -> Rank:
        return self.timer_pos_in_order_rank(self.proposal_received_in_r0)

    def proposal_received_timer_rank_in_r0_all_nodes(self) -> Rank:
        return DomainPointwiseRank(
            self.proposal_receiver_in_r0_timer(),
            ParamSpec(N=Node),
            None,
        )

    # no reason to actually do this like that but it doesn't work if I remove I from parameters
    # otherwise we get the error AssertionError: No timer for t_<proposal_received(N, i0, r0, V)>; closest match: t_<proposal_received(N, I, r0, V)>. All timers:
    def value_proposed_in_r0_and_i0(self, V: Value, I: Inst) -> BoolRef:
        return And(self.sys.proposal(I, self.sys.r0, V), I == self.sys.i0)

    def cond_prop_recv_timer_in_r0_all_nodes(self) -> Rank:
        return CondRank(
            self.proposal_received_timer_rank_in_r0_all_nodes(),
            self.value_proposed_in_r0_and_i0,
        )

    def cond_prop_recv_timer_in_r0_all_nodes_values_instances(self) -> Rank:
        return DomainPointwiseRank.close(
            self.cond_prop_recv_timer_in_r0_all_nodes(),
            FiniteLemma(self.value_proposed_in_r0_and_i0),
        )

    def join_acks_called_in_r0(self) -> BoolRef:
        return self.sys.join_acks_called(self.sys.r0)

    def join_acks_helpful(self) -> BoolRef:
        N = Node("N")
        M = Votemap("M")
        return And(
            Not(self.sys.active(self.sys.r0)),
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    Exists(M, self.sys.one_b_votemap_received(self.sys.r0, N, M)),
                ),
            ),
        )

    # in ivy they have the conjecture
    # conjecture l2s.saved & ~l2s.w_process_join_acks_r0 & ~l2s.s_active(r0) & (exists Q . forall N . member(N,Q) -> l2s.s_one_b_received(r0,N)) -> active(r0)
    # that is probably related to what I'm trying to do here.

    def join_acks_called_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.join_acks_called_in_r0, self.join_acks_helpful, None
        )

    # no reason to actually do this like that but it doesn't work if I remove I from parameters
    # because it does not recognize propose_called(r0,i0) as an instantiation of propose_called(r0,I)
    def propose_called_in_r0_and_I(self, I: Inst) -> BoolRef:
        return self.sys.propose_called(self.sys.r0, I)

    def propose_helpful(self, I: Inst) -> BoolRef:
        return And(
            self.sys.active(self.sys.r0),
            I == self.sys.i0,
            self.no_proposed_in_r0_and_i0(),
        )

    # seems to possibly increase in propose and process_join_acks
    # process_join_acks - can set to true, needs to decrease some previous lex component
    # propose - usual fairness thing, needs to guarantee that the propose action decreases some previous lex componenet
    def propose_called_timer_rank_if_active(self) -> Rank:
        return self.timer_rank(
            self.propose_called_in_r0_and_I,
            self.propose_helpful,
            None,
        )

    # currently conserved doesn't work for
    # join_acks_called_timer_rank
    # i guess this is because of states where helpful becomes true
    def rank(self) -> Rank:
        return LexRank(
            self.one_a_r0_timer_rank(),
            self.one_a_received_timer_rank(),
            self.one_b_received_timer_rank(),
            self.binary_r0_not_active(),
            self.join_acks_called_timer_rank()
        )

    # cases for debugging - don't affect final proof.

    # decreases one_a_r0_timer_rank
    def case_1(self) -> BoolRef:
        return Not(self.sys.one_a(self.sys.r0))

    # decreases one_a_received_timer_rank
    def case_2(self) -> BoolRef:
        N = Node("N")
        return And(
            self.sys.one_a(self.sys.r0),
            Exists(
                N,
                And(
                    self.sys.member(N, self.sys.q0),
                    Not(self.sys.one_a_received(N, self.sys.r0)),
                ),
            ),
        )

    # decreases one_b_received_timer_rank
    def case_3(self) -> BoolRef:
        N = Node("N")
        return And(
            self.sys.one_a(self.sys.r0),
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    self.sys.one_a_received(N, self.sys.r0),
                ),
            ),
            Exists(
                N,
                And(
                    self.sys.member(N, self.sys.q0),
                    Not(self.sys.one_b_received(self.sys.r0, N)),
                ),
            ),
        )

    # decreases binary_r0_not_active
    def case_4(self) -> BoolRef:
        N = Node("N")
        M = Votemap("M")
        return And(
            self.sys.one_a(self.sys.r0),
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    self.sys.one_a_received(N, self.sys.r0),
                ),
            ),
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    Exists(M, self.sys.one_b_votemap_received(self.sys.r0, N, M)),
                ),
            ),
            Not(self.sys.active(self.sys.r0)),
        )


proof = MultiPaxosProof()
# proof.check(check_conserved=True)

print("case1")
proof._check_conserved(assumption=proof.case_1())
proof._check_decreases(assumption=proof.case_1())

print("case2")
proof._check_conserved(assumption=proof.case_2())
proof._check_decreases(assumption=proof.case_2())

print("case3")
proof._check_conserved(assumption=proof.case_3())
proof._check_decreases(assumption=proof.case_3())

print("case4")
proof._check_conserved(assumption=proof.case_4())
proof._check_decreases(assumption=proof.case_4())

print("all cases")
proof._check_conserved()
proof._check_decreases()