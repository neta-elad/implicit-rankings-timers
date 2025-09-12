from prelude import *

# Classic mutex in a ring - a token moves around a ring, allowing the holder to enter the critical section
# taken from Fang, Y., Piterman, N., Pnueli, A. and Zuck, L., 2004, January.
# Liveness with invisible ranking.
# In International Workshop on Verification, Model Checking, and Abstract Interpretation (pp. 223-238). Berlin, Heidelberg: Springer Berlin Heidelberg.


class Node(Finite): ...


class Loc(Enum):
    waiting: "Loc"
    critical: "Loc"
    neutral: "Loc"


class MutexRing(TransitionSystem):
    # immutables
    leader: Immutable[Node]
    btw: Immutable[Rel[Node, Node, Node]]
    skolem_node: Immutable[Node]

    # mutables
    token: Rel[Node]
    node_loc: Fun[Node, Loc]
    scheduled: Rel[Node]

    @axiom
    def btw_axioms(self, X: Node, Y: Node, Z: Node, W: Node) -> BoolRef:
        return And(
            # characterising axioms of the btw relation
            Implies(And(self.btw(W, X, Y), self.btw(W, Y, Z)), self.btw(W, X, Z)),
            Implies(self.btw(W, X, Y), Not(self.btw(W, Y, X))),
            Or(self.btw(W, X, Y), self.btw(W, Y, X), W == X, W == Y, X == Y),
            Implies(self.btw(X, Y, Z), self.btw(Y, Z, X)),
        )

    @init
    def initial(self, X: Node) -> BoolRef:
        return And(
            self.token(X) == (X == self.leader),
            self.node_loc(X) == Loc.neutral,
        )

    def succ(self, n: Node, s: Node) -> BoolRef:
        Z = Node("Z")
        return And(
            n != s,
            ForAll(Z, Or(self.btw(n, s, Z), Z == n, Z == s)),
        )

    @transition
    def wakeup(self, n: Node, s: Node) -> BoolRef:
        N = Node("N")
        return And(
            # guard
            self.succ(n, s),
            # fairness
            ForAll(N, self.scheduled(N) == (N == n)),
            # updates
            If(
                self.token(n),
                If(
                    self.node_loc(n) == Loc.neutral,
                    And(
                        self.token.update(
                            lambda old, new, N: new(N)
                            == Or(And(old(N), N != n), N == s)
                        ),
                        self.node_loc.unchanged(),
                    ),
                    If(
                        self.node_loc(n) == Loc.waiting,
                        And(
                            self.token.unchanged(),
                            self.node_loc.update(
                                lambda old, new, N: new(N)
                                == If(N == n, Loc.critical, old(N))
                            ),
                        ),
                        # else loc = critical
                        And(
                            self.token.unchanged(),
                            self.node_loc.update(
                                lambda old, new, N: new(N)
                                == If(N == n, Loc.neutral, old(N))
                            ),
                        ),
                    ),
                ),
                # else - no token
                And(
                    self.token.unchanged(),
                    If(
                        self.node_loc(n) == Loc.neutral,
                        self.node_loc.update(
                            lambda old, new, N: new(N)
                            == If(N == n, Loc.waiting, old(N))
                        ),
                        self.node_loc.unchanged(),
                    ),
                ),
            ),
        )


class MutexRingProp(Prop[MutexRing]):
    def negated_prop(self) -> BoolRef:
        N = Node("N")
        return And(
            ForAll(N, G(F(self.sys.scheduled(N)))),
            F(
                And(
                    self.sys.node_loc(self.sys.skolem_node) == Loc.waiting,
                    G(Not(self.sys.node_loc(self.sys.skolem_node) == Loc.critical)),
                )
            ),
        )


class MutexRingProof(Proof[MutexRing], prop=MutexRingProp):
    # needed?
    @invariant
    def unique_token(self, X: Node, Y: Node) -> BoolRef:
        return Implies(And(self.sys.token(X), self.sys.token(Y)), X == Y)

    @invariant
    def critical_implies_token(self, X: Node) -> BoolRef:
        return Implies(self.sys.node_loc(X) == Loc.critical, self.sys.token(X))

    @invariant
    def exists_token(self) -> BoolRef:
        X = Node("X")
        return Exists(X, self.sys.token(X))

    @temporal_invariant
    def globally_eventually_scheduled(self, N: Node) -> BoolRef:
        return G(F(self.sys.scheduled(N)))

    @temporal_invariant
    def skolem_never_critical(self) -> BoolRef:
        return F(
            And(
                self.sys.node_loc(self.sys.skolem_node) == Loc.waiting,
                G(Not(self.sys.node_loc(self.sys.skolem_node) == Loc.critical)),
            )
        )

    def holds_token(self, N: Node) -> BoolRef:
        return self.sys.token(N)

    def waiting_and_token(self) -> BoolRef:
        N = Node("N")
        return Exists(N, And(self.holds_token(N), self.sys.node_loc(N) == Loc.waiting))

    def critical(self) -> BoolRef:
        N = Node("N")
        return Exists(N, self.sys.node_loc(N) == Loc.critical)

    def local_rank(self) -> Rank:
        return LexRank(BinRank(self.waiting_and_token), BinRank(self.critical))

    def btw_sk_token(self, N: Node) -> BoolRef:
        M = Node("M")
        return Exists(
            M,
            And(
                self.holds_token(M),
                Or(
                    self.sys.btw(M, N, self.sys.skolem_node),
                    And(M != N, N == self.sys.skolem_node),
                ),
            ),
        )

    def ring_distance(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.btw_sk_token), None)

    def locked(self) -> BoolRef:
        return And(
            self.sys.node_loc(self.sys.skolem_node) == Loc.waiting,
            G(Not(self.sys.node_loc(self.sys.skolem_node) == Loc.critical)),
        )

    def locked_rank(self) -> Rank:
        return self.timer_rank(self.locked, None, None)

    def scheduled(self, N: Node) -> BoolRef:
        return self.sys.scheduled(N)

    def scheduling_rank(self) -> Rank:
        return self.timer_rank(self.scheduled, self.holds_token, None)

    def rank(self) -> Rank:
        return LexRank(
            self.locked_rank(),
            self.ring_distance(),
            self.local_rank(),
            self.scheduling_rank(),
        )


MutexRingProof().check()
