from prelude import *
from typing import List

# @ status - property and proof structure implemented based on Ivy specification

# Paxos consensus protocol implementation
# Based on the Ivy implementation in ivy_examples/paxos_liveness.ivy


class Node(Expr): ...


class Value(Expr): ...


class Quorum(Expr): ...


class Round(Expr): ...


class PaxosSystem(TransitionSystem):
    # Immutable constants and relations
    none: Immutable[Round]
    le: Immutable[Rel[Round, Round]]  # total order on rounds
    member: Immutable[Rel[Node, Quorum]]  # quorum membership
    r0: Immutable[Round]  # the round after which no ballot must be started
    q0: Immutable[Quorum]  # the quorum that must be responsive

    # Main protocol state variables
    one_a: Rel[Round]  # 1a messages (prepare requests)
    one_b_max_vote: Rel[Node, Round, Round, Value]  # 1b messages (prepare responses)
    proposal: Rel[Round, Value]  # 2a messages (accept requests)
    vote: Rel[Node, Round, Value]  # 2b messages (accept responses)

    # Message tracking relations
    one_a_received: Rel[Node, Round]
    one_b_max_vote_received: Rel[Round, Node, Round, Value]
    proposal_received: Rel[Node, Round, Value]

    # Projection relations for abstraction (from original model)
    proposed: Rel[Round]  # invariant: proposed(R) <-> exists V . proposal(R,V)
    one_b_received: Rel[
        Round, Node
    ]  # invariant: one_b_received(R,N) <-> exists R2,V. one_b_max_vote_received(R,N,R2,V)

    # Fairness variables will be added later

    @axiom
    def total_order_axioms(self, X: Round, Y: Round, Z: Round) -> BoolRef:
        return And(
            # Reflexivity
            self.le(X, X),
            # Transitivity
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            # Anti-symmetry
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            # Totality
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
            # Initialize all protocol relations to false
            Not(self.one_a(R)),
            Not(self.one_b_max_vote(N, R1, R2, V)),
            Not(self.proposal(R, V)),
            Not(self.vote(N, R, V)),
            Not(self.one_a_received(N, R)),
            Not(self.one_b_max_vote_received(R1, N, R2, V)),
            Not(self.proposal_received(N, R, V)),
            Not(self.proposed(R)),
            Not(self.one_b_received(R, N)),
            # Fairness variables remain non-deterministic (no initialization constraints)
        )

    @transition
    def send_1a(self, r: Round) -> BoolRef:
        # A proposer selects a round and sends a message asking nodes to join the round
        return And(
            # guard
            r != self.none,
            Not(self.one_a(r)),
            self.le(r, self.r0),
            # updates
            self.one_a.update({(r,): true}),
            # other relations unchanged
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
            # guard
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
            # other relations unchanged
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
            # guard
            r != self.none,
            self.one_b_max_vote(n, r, maxr, v),
            # updates
            self.one_b_max_vote_received.update({(r, n, maxr, v): true}),
            self.one_b_received.update({(r, n): true}),
            # other relations unchanged
            self.one_a.unchanged(),
            self.one_b_max_vote.unchanged(),
            self.proposal.unchanged(),
            self.vote.unchanged(),
            self.one_a_received.unchanged(),
            self.proposal_received.unchanged(),
            self.proposed.unchanged(),
        )

    # reviewed up to here

    @transition
    def propose(self, r: Round, v: Value, q: Quorum, maxr: Round) -> BoolRef:
        N = Node("N")
        MAXR = Round("MAXR")
        V = Value("V")
        return And(
            # guard
            r != self.none,
            # have received 1b messages from all members of quorum q
            ForAll(
                N,
                Implies(
                    self.member(N, q),
                    Exists([MAXR, V], self.one_b_max_vote_received(r, N, MAXR, V)),
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
                    # updates
                    self.proposal.update({(r, v): true}),
                    self.proposed.update({(r,): true}),
                ),
                And(self.proposal.unchanged(), self.proposed.unchanged()),
            ),
            # other relations unchanged
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
        Q = Quorum("Q")
        N = Node("N")
        return And(
            # guard
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
                    # "from negation of the liveness property"
                    Not(
                        Exists(
                            Q,
                            ForAll(
                                N, Implies(self.member(N, Q), self.vote(N, self.r0, v))
                            ),
                        )
                    ),
                ),
                self.vote.unchanged(),
            ),
            # other relations unchanged
            self.one_a.unchanged(),
            self.one_b_max_vote.unchanged(),
            self.proposal.unchanged(),
            self.one_a_received.unchanged(),
            self.one_b_max_vote_received.unchanged(),
            self.proposed.unchanged(),
            self.one_b_received.unchanged(),
        )


# Property: A quorum of nodes eventually votes for the same value in round r0
# Based on Ivy specification: exists V:value, Q:quorum. F. forall N:node. member(N,Q) -> vote(N,r0,V)
class PaxosProperty(Prop[PaxosSystem]):
    def prop(self) -> BoolRef:
        V = Value("V")
        Q = Quorum("Q")
        N = Node("N")
        R = Round("R")

        # Fairness conditions from the Ivy specification:
        fairness_conditions = And(
            # Fairness 1: F. one_a(r0) - Eventually a phase 1a message is sent in round r0
            F(self.sys.one_a(self.sys.r0)),
            # "Eventually a phase 1a message is sent in round r0 (i.e. the owner of r0 starts round r0)"
            # Fairness 2: forall N:node. member(N,q0) ->
            #   G. one_a(r0) -> F. one_a_received(N,r0)
            #   forall. R,V. G. one_b_max_vote(N,r0,R,V) -> F. one_b_received(r0,N)
            #   forall. V. G proposal(r0,V) -> F. proposal_received(N,r0,V)
            ForAll(
                N,
                Implies(
                    self.sys.member(N, self.sys.q0),
                    And(
                        # G. one_a(r0) -> F. one_a_received(N,r0)
                        G(
                            Implies(
                                self.sys.one_a(self.sys.r0),
                                F(self.sys.one_a_received(N, self.sys.r0)),
                            )
                        ),
                        # forall. R,V. G. one_b_max_vote(N,r0,R,V) -> F. one_b_received(r0,N)
                        ForAll(
                            [R, V],
                            G(
                                Implies(
                                    self.sys.one_b_max_vote(N, self.sys.r0, R, V),
                                    F(self.sys.one_b_received(self.sys.r0, N)),
                                )
                            ),
                        ),
                        # forall. V. G proposal(r0,V) -> F. proposal_received(N,r0,V)
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
            # Fairness 3: F. proposed(r0) - A proposal is eventually made in round r0
            F(self.sys.proposed(self.sys.r0)),
        )

        # The main liveness property: exists V:value, Q:quorum. F. forall N:node. member(N,Q) -> vote(N,r0,V)
        liveness_property = Exists(
            [V, Q],
            F(
                ForAll(
                    N, Implies(self.sys.member(N, Q), self.sys.vote(N, self.sys.r0, V))
                )
            ),
        )

        # The complete property: fairness conditions imply the liveness property
        return Implies(fairness_conditions, liveness_property)


# Proof class will be implemented later - it's more complex than the basic structure
