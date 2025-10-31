"""
Paxos Consensus Protocol

From liveness to safety:
Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., Shoham, S.: Reducing liveness to safety in first-order logic.
Proc. ACM Program. Lang. 2(POPL), 26:1–26:33 (2018). https://doi.org/10.1145/3158114

Protocol from:
Lamport, L.: The part-time parliament. ACM Trans. Program. Lang. Syst. 16(2), 133–169 (Mar 1994). https://doi.org/10.1145/174674.174675
"""

# @status - everything works except for 2 annoying invariant checks in init because of the quantifier altenration in init

from prelude import *


class Node(Finite): ...


class Value(Expr): ...


class Quorum(Finite): ...


class Round(Expr): ...


class PaxosSystem(TransitionSystem):
    none: Immutable[Round]
    le: Immutable[Rel[Round, Round]]  # total order on rounds
    member: Immutable[Rel[Node, Quorum]]  # quorum membership
    r0: Immutable[Round]  # the round after which no ballot must be started
    q0: Immutable[Quorum]  # the quorum that must be responsive

    one_a: Rel[Round]
    one_b_max_vote: Rel[Node, Round, Round, Value]
    proposal: Rel[Round, Value]
    vote: Rel[Node, Round, Value]
    one_a_received: Rel[Node, Round]
    one_b_max_vote_received: Rel[Round, Node, Round, Value]
    proposal_received: Rel[Node, Round, Value]

    # Projection relations for abstraction (from original model)
    proposed: Rel[Round]
    # invariant: proposed(R) <-> exists V . proposal(R,V)
    one_b_received: Rel[Round, Node]
    # invariant: one_b_received(R,N) <-> exists R2,V. one_b_max_vote_received(R,N,R2,V)

    @axiom
    def total_order_axioms(self, X: Round, Y: Round, Z: Round) -> BoolRef:
        return And(
            self.le(X, X),
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Or(self.le(X, Y), self.le(Y, X)),
        )

    @axiom
    def quorum_intersection(self, Q1: Quorum, Q2: Quorum) -> BoolRef:
        N = Node("N")
        return Exists(N, And(self.member(N, Q1), self.member(N, Q2)))

    @axiom
    def r0_not_none(self) -> BoolRef:
        return self.r0 != self.none

    @init
    def initial(self, R1: Round, R2: Round, R: Round, N: Node, V: Value) -> BoolRef:
        return And(
            Not(self.one_a(R)),
            Not(self.one_b_max_vote(N, R1, R2, V)),
            Not(self.proposal(R, V)),
            Not(self.vote(N, R, V)),
            Not(self.one_a_received(N, R)),
            Not(self.one_b_max_vote_received(R1, N, R2, V)),
            Not(self.proposal_received(N, R, V)),
            Not(self.proposed(R)),
            Not(self.one_b_received(R, N)),
        )

    @transition
    def send_1a(self, r: Round) -> BoolRef:
        # A proposer selects a round and sends a message asking nodes to join the round
        return And(
            r != self.none,
            Not(self.one_a(r)),
            self.one_a.update({(r,): true}),
            self.one_b_max_vote.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.one_a_received.unchanged(),
            self.one_b_max_vote_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def join_round(self, n: Node, r: Round, maxr: Round, v: Value) -> BoolRef:
        # receive 1a and answer with 1b
        R1 = Round("R1")
        R2 = Round("R2")
        MAXR = Round("MAXR")
        V = Value("V")
        return And(
            r != self.none,
            self.one_a(r),
            self.one_a_received.update({(n, r): true}),
            # find the maximal vote in a round less than r
            If(
                ForAll(
                    [R1, R2, V],
                    Implies(self.one_b_max_vote(n, R1, R2, V), self.le(R1, r)),
                ),
                # maxr and v are chosen non-deterministically to satisfy the conditions
                And(
                    Or(
                        # case 1: maxr = none and no votes in rounds >= r
                        And(
                            maxr == self.none,
                            ForAll(
                                [MAXR, V],
                                Not(And(Not(self.le(r, MAXR)), self.vote(n, MAXR, V))),
                            ),
                        ),
                        # case 2: maxr != none and maxr is the maximal round < r with a vote
                        And(
                            maxr != self.none,
                            Not(self.le(r, maxr)),
                            self.vote(n, maxr, v),
                            ForAll(
                                [MAXR, V],
                                Implies(
                                    And(Not(self.le(r, MAXR)), self.vote(n, MAXR, V)),
                                    self.le(MAXR, maxr),
                                ),
                            ),
                        ),
                    ),
                    self.one_b_max_vote.update({(n, r, maxr, v): true}),
                ),
                self.one_b_max_vote.unchanged(),
            ),
            self.one_a.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.one_b_max_vote_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def receive_one_b(self, r: Round, n: Node, maxr: Round, v: Value) -> BoolRef:
        return And(
            r != self.none,
            self.one_b_max_vote(n, r, maxr, v),
            self.one_b_max_vote_received.update({(r, n, maxr, v): true}),
            self.one_b_received.update({(r, n): true}),
            self.one_a.unchanged(),
            self.one_b_max_vote.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.one_a_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
        )

    @transition
    def propose(self, r: Round, v: Value, q: Quorum, maxr: Round) -> BoolRef:
        N = Node("N")
        MAXR = Round("MAXR")
        V = Value("V")
        Q = Quorum("Q")
        return And(
            r != self.none,
            Implies(
                ForAll(
                    [N, Q],
                    Implies(
                        self.member(N, Q),
                        Exists([MAXR, V], self.one_b_max_vote_received(r, N, MAXR, V)),
                    ),
                ),
                ForAll(
                    N,
                    Implies(
                        self.member(N, q),
                        Exists([MAXR, V], self.one_b_max_vote_received(r, N, MAXR, V)),
                    ),
                ),
            ),
            If(
                And(
                    ForAll(V, Not(self.proposal(r, V))),
                    ForAll(
                        N,
                        Implies(
                            self.member(N, q),
                            Exists(
                                [MAXR, V], self.one_b_max_vote_received(r, N, MAXR, V)
                            ),
                        ),
                    ),
                ),
                And(
                    # find the maximal max_vote in the quorum
                    Or(
                        And(
                            maxr == self.none,
                            ForAll(
                                [N, MAXR, V],
                                Not(
                                    And(
                                        self.member(N, q),
                                        MAXR != self.none,
                                        self.one_b_max_vote_received(r, N, MAXR, V),
                                    )
                                ),
                            ),
                        ),
                        And(
                            maxr != self.none,
                            Exists(
                                N,
                                And(
                                    self.member(N, q),
                                    Not(self.le(r, maxr)),
                                    self.one_b_max_vote_received(r, N, maxr, v),
                                ),
                            ),
                            ForAll(
                                [N, MAXR, V],
                                Implies(
                                    And(
                                        self.member(N, q),
                                        Not(self.le(r, MAXR)),
                                        self.one_b_max_vote_received(r, N, MAXR, V),
                                        MAXR != self.none,
                                    ),
                                    self.le(MAXR, maxr),
                                ),
                            ),
                        ),
                    ),
                    self.proposal.update({(r, v): true}),
                    self.proposed.update({(r,): true}),
                ),
                And(self.proposal.unchanged(), self.proposed.unchanged()),
            ),
            self.one_a.unchanged(),
            self.one_b_max_vote.unchanged(),
            self.vote.unchanged(),
            self.one_a_received.unchanged(),
            self.one_b_max_vote_received.unchanged(),
            self.proposal_received.unchanged(),
            self.one_b_received.unchanged(),
        )

    @transition
    def cast_vote(self, n: Node, v: Value, r: Round) -> BoolRef:
        R1 = Round("R1")
        R2 = Round("R2")
        V = Value("V")
        return And(
            r != self.none,
            self.proposal(r, v),
            self.proposal_received.update({(n, r, v): true}),
            If(
                ForAll(
                    [R1, R2, V],
                    Implies(
                        Not(self.le(R1, r)), Not(self.one_b_max_vote(n, R1, R2, V))
                    ),
                ),
                And(
                    self.vote.update({(n, r, v): true}),
                    # here in ivy they use the violation -- this is a bit cheaty, the skolemization is a better approach (REIVIEW HERE)
                ),
                self.vote.unchanged(),
            ),
            self.one_a.unchanged(),
            self.one_b_max_vote.unchanged(),
            self.proposal.unchanged(),
            self.one_a_received.unchanged(),
            self.one_b_max_vote_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )


# Property: A quorum of nodes eventually votes for the same value in round r0
class PaxosProperty(Prop[PaxosSystem]):
    def prop(self) -> BoolRef:
        V = Value("V")
        Q = Quorum("Q")
        N = Node("N")
        R = Round("R")
        fairness_conditions = And(
            F(self.sys.one_a(self.sys.r0)),
            # this was implemented manually in the one_a transition in ivy
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
                            [R, V],
                            G(
                                Implies(
                                    self.sys.one_b_max_vote(N, self.sys.r0, R, V),
                                    F(self.sys.one_b_received(self.sys.r0, N)),
                                )
                            ),
                        ),
                        ForAll(
                            V,
                            G(
                                Implies(
                                    self.sys.proposal(self.sys.r0, V),
                                    F(self.sys.proposal_received(N, self.sys.r0, V)),
                                )
                            ),
                        ),
                    ),
                ),
            ),
            F(self.sys.proposed(self.sys.r0)),
        )
        liveness_property = Exists(
            [V, Q],
            F(
                ForAll(
                    N,
                    Implies(self.sys.member(N, Q), self.sys.vote(N, self.sys.r0, V)),
                )
            ),
        )
        return Implies(fairness_conditions, liveness_property)


class PaxosProof(Proof[PaxosSystem], prop=PaxosProperty):

    @temporal_invariant(leaf=True)
    def eventually_one_r0(self) -> BoolRef:
        return F(self.sys.one_a(self.sys.r0))

    @temporal_invariant(leaf=True)
    def fairness2(self) -> BoolRef:
        V = Value("V")
        N = Node("N")
        R = Round("R")
        return ForAll(
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
                        [R, V],
                        G(
                            Implies(
                                self.sys.one_b_max_vote(N, self.sys.r0, R, V),
                                F(self.sys.one_b_received(self.sys.r0, N)),
                            )
                        ),
                    ),
                    ForAll(
                        V,
                        G(
                            Implies(
                                self.sys.proposal(self.sys.r0, V),
                                F(self.sys.proposal_received(N, self.sys.r0, V)),
                            )
                        ),
                    ),
                ),
            ),
        )

    @temporal_invariant(leaf=True)
    def eventually_proposed_r0(self) -> BoolRef:
        return F(self.sys.proposed(self.sys.r0))

    @invariant
    def proposal_uniqueness(self, R: Round, V1: Value, V2: Value) -> BoolRef:
        return Implies(
            And(self.sys.proposal(R, V1), self.sys.proposal(R, V2)), V1 == V2
        )

    @invariant
    def vote_proposal_consistency(self, N: Node, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.vote(N, R, V), self.sys.proposal(R, V))

    @temporal_invariant
    def no_one_a_after_r0_temporal(self) -> BoolRef:
        R = Round("R")
        return G(
            ForAll(
                R,
                Implies(
                    self.sys.one_a(R),
                    self.sys.le(R, self.sys.r0),
                ),
            )
        )

    @invariant
    def no_one_a_after_r0(self, R: Round) -> BoolRef:
        return Implies(self.sys.one_a(R), self.sys.le(R, self.sys.r0))

    @invariant
    def no_one_b_max_vote_after_r0(
        self, N: Node, R1: Round, R2: Round, V: Value
    ) -> BoolRef:
        return Implies(
            self.sys.one_b_max_vote(N, R1, R2, V), self.sys.le(R1, self.sys.r0)
        )

    @invariant
    def no_one_b_max_vote_received_after_r0(
        self, R: Round, N: Node, R2: Round, V: Value
    ) -> BoolRef:
        return Implies(
            self.sys.one_b_max_vote_received(R, N, R2, V),
            self.sys.le(R, self.sys.r0),
        )

    @invariant
    def no_proposal_after_r0(self, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.proposal(R, V), self.sys.le(R, self.sys.r0))

    @invariant
    def no_vote_after_r0(self, N: Node, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.vote(N, R, V), self.sys.le(R, self.sys.r0))

    @system_invariant
    def projection_proposal_one_sided(self, R: Round, V: Value) -> BoolRef:
        return Implies(self.sys.proposal(R, V), self.sys.proposed(R))

    @system_invariant
    def proposal_received_implies_proposed(
        self, N: Node, R: Round, V: Value
    ) -> BoolRef:
        return Implies(self.sys.proposal_received(N, R, V), self.sys.proposed(R))

    @system_invariant
    def proposal_received_implies_proposal(
        self, N: Node, R: Round, V: Value
    ) -> BoolRef:
        return Implies(self.sys.proposal_received(N, R, V), self.sys.proposal(R, V))

    @system_invariant
    def projection_proposal(self, R: Round) -> BoolRef:
        V = Value("V")
        return self.sys.proposed(R) == Exists(V, self.sys.proposal(R, V))

    # @invariant(leaf=True)
    # #notice that because this talks about r0 it can't be a system_invariant
    # def one_a_received_iff_one_b_max_vote(self, N: Node) -> BoolRef:
    #     R = Round("R")
    #     V = Value("V")
    #     return self.sys.one_a_received(N, self.sys.r0) == Exists(
    #         [R, V], self.sys.one_b_max_vote(N, self.sys.r0, R, V)
    #     )

    # @invariant(leaf=True)
    # #notice that because this talks about r0 it can't be a system_invariant
    # def proposal_received_iff_vote(self, N: Node, V: Value) -> BoolRef:
    #     return self.sys.proposal_received(N, self.sys.r0, V) == self.sys.vote(
    #         N, self.sys.r0, V
    #     )

    @invariant(leaf=True)
    #notice that because this talks about r0 it can't be a system_invariant
    def one_a_received_then_one_b_max_vote(self, N: Node) -> BoolRef:
        R = Round("R")
        V = Value("V")
        return Implies(
            self.sys.one_a_received(N, self.sys.r0),
            Exists(
                [R, V], self.sys.one_b_max_vote(N, self.sys.r0, R, V)
            )
        )
        
    @invariant(leaf=True)
    #notice that because this talks about r0 it can't be a system_invariant
    def proposal_received_then_vote(self, N: Node, V: Value) -> BoolRef:
        return Implies(
            self.sys.proposal_received(N, self.sys.r0, V),
            self.sys.vote(N, self.sys.r0, V)
        )

    def one_a_r0_timer_rank(self) -> Rank:
        return self.timer_rank(self.sys.one_a(self.sys.r0), None, None)

    def proposed_r0_timer_rank(self) -> Rank:
        return self.timer_rank(self.sys.proposed(self.sys.r0), None, None)

    def one_a_received_r0(self, N: Node) -> BoolRef:
        return self.sys.one_a_received(N, self.sys.r0)

    def one_a_received_timer_rank(self) -> Rank:
        return self.timer_rank(self.one_a_received_r0, None, None)

    def one_b_received_r0(self, N: Node) -> BoolRef:
        return self.sys.one_b_received(self.sys.r0, N)

    def one_b_received_timer_rank(self) -> Rank:
        return self.timer_rank(self.one_b_received_r0, None, None)

    def proposal_received(self, N: Node, V: Value) -> BoolRef:
        return self.sys.proposal_received(N, self.sys.r0, V)

    def value_proposed_in_r0(self, N: Node, V: Value) -> BoolRef:
        return self.sys.proposal(self.sys.r0, V)

    def proposal_received_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.proposal_received,
            self.value_proposed_in_r0,
            FiniteLemma(self.value_proposed_in_r0),
        )

    def rank(self) -> Rank:
        return PointwiseRank(
            self.one_a_r0_timer_rank(),
            self.one_a_received_timer_rank(),
            self.one_b_received_timer_rank(),
            LexRank(self.proposed_r0_timer_rank(), self.proposal_received_timer_rank()),
            self.proposal_eventually_proposed_value_timer_rank(),
        )

    # simplifying assumptions for debugging - don't affect final proof.

    # def no_one_a_r0(self) -> BoolRef:
    #     return Not(self.sys.one_a(self.sys.r0))

    # def not_proposed_r0(self) -> BoolRef:
    #     return Not(self.sys.proposed(self.sys.r0))

    # def exists_N_in_q0_not_received_one_a(self) -> BoolRef:
    #     N = Node("N")
    #     return Exists(
    #         N,
    #         And(
    #             self.sys.member(N, self.sys.q0),
    #             Not(self.sys.one_a_received(N, self.sys.r0)),
    #         ),
    #     )

    # def exists_N_in_q0_not_received_one_b(self) -> BoolRef:
    #     N = Node("N")
    #     return Exists(
    #         N,
    #         And(
    #             self.sys.member(N, self.sys.q0),
    #             Not(self.sys.one_b_received(self.sys.r0, N)),
    #         ),
    #     )

    # def exists_N_in_q0_not_received_proposal(self) -> BoolRef:
    #     N = Node("N")
    #     V = Value("V")
    #     return Exists(
    #         [N, V],
    #         And(
    #             self.sys.member(N, self.sys.q0),
    #             self.sys.proposal(self.sys.r0, V),
    #             Not(self.sys.proposal_received(N, self.sys.r0, V)),
    #         ),
    #     )
    
    # we add this temporal witness, which we use to instantiate the negated property.
    @temporal_witness
    @track
    def eventually_proposed_value(self, V: Value) -> BoolRef:
        return F(self.sys.proposal(self.sys.r0, V))

    @temporal_invariant(leaf=True)
    @track
    def eventually_proposed_value_definition(self) -> BoolRef:
        V = Value("V")
        return Implies(
            Exists(V, F(self.sys.proposal(self.sys.r0, V))),
            F(self.sys.proposal(self.sys.r0, self.eventually_proposed_value)),
        )

    @temporal_invariant(leaf=True)
    @track
    def proposal_implies_witness(self) -> BoolRef:
        V = Value("V")
        return Implies(
            Exists(V, self.sys.proposal(self.sys.r0, V)),
            Exists(V, F(self.sys.proposal(self.sys.r0, V))),
        )

    def proposal_eventually_proposed_value_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.sys.proposal(self.sys.r0, self.eventually_proposed_value), None, None
        )

    # we should have this invariant only for some witness value as it introduces a quantifer altenrnation
    # @temporal_invariant(leaf=True)
    # def violation(self) -> BoolRef:
    #     V = Value("V")
    #     Q = Quorum("Q")
    #     N = Node("N")
    #     return ForAll(
    #         [V,Q],
    #         G(Exists(N, And(self.sys.member(N, Q), Not(self.sys.vote(N, self.sys.r0, V)))))
    #     )

    @invariant(leaf=True)
    def violation_instantiated(self) -> BoolRef:
        N = Node("N")
        Q = Quorum("Q")
        V = Value("V")
        return timer_zero(
            self.t(
                G(
                    Exists(
                        N,
                        And(
                            self.sys.member(N, Q), Not(self.sys.vote(N, self.sys.r0, V))
                        ),
                    )
                )
            )(self.sys.q0, self.eventually_proposed_value)
        )

    # works for some of the transtions with the violation temporal invariant
    # def all_nodes_in_q0_proposal_received(self) -> BoolRef:
    #     N = Node("N")
    #     return And(
    #             self.sys.proposal(self.sys.r0, self.eventually_proposed_value),
    #             ForAll(N,
    #                 Implies(
    #                     self.sys.member(N, self.sys.q0),
    #                     self.sys.proposal_received(N, self.sys.r0, self.eventually_proposed_value)
    #                 )
    #             )
    #         )

    # def exists_proposal_not_skolem(self) -> BoolRef:
    #     V = Value("V")
    #     return Exists(V, And(
    #         self.sys.proposal(self.sys.r0, V),
    #         Not(self.sys.proposal(self.sys.r0, self.eventually_proposed_value))
    #     ))


proof = PaxosProof()
proof.check(check_conserved=True)
proof._check_conserved()
proof._check_decreases()
# print("no one_a_r0")
# proof._check_decreases(proof.no_one_a_r0())
# print("not proposed_r0")
# proof._check_decreases(proof.not_proposed_r0())
# print("exists_N_in_q0_not_received_one_a")
# proof._check_decreases(proof.exists_N_in_q0_not_received_one_a())
# print("exists_N_in_q0_not_received_one_b")
# proof._check_decreases(proof.exists_N_in_q0_not_received_one_b())
# print("exists_N_in_q0_not_received_proposal")
# proof._check_decreases(proof.exists_N_in_q0_not_received_proposal()) #fails
# # review this case possibly simplify it or think of the proof manually
# print("all_nodes_in_q0_proposal_received")
# proof._check_decreases(proof.all_nodes_in_q0_proposal_received())
