"""
Dijkstra's k-state Self-stabilization Protocol

From Implicit Rankings for Verification of Liveness Properties in First-Order Logic / Raz Lotan & Sharon Shoham

Protocol from:
Dijkstra, E.W.: Self-stabilizing systems in spite of distributed control.
Commun. ACM 17(11), 643–644 (nov 1974), https://doi.org/10.1145/361179.361202
"""

# @status - start
# review this because something didn't make sense to me before, it looked too simple.

from prelude import *


class Node(Finite): ...


class Value(Finite): ...


class DijkstraKStateSystem(TransitionSystem):
    # Immutable constants and relations
    skd: Immutable[Node]
    bot: Immutable[Node]
    witness_value: Immutable[Value]
    # node_h: Immutable[Node]
    leq_node: Immutable[Rel[Node, Node]]
    leq_value: Immutable[Rel[Value, Value]]

    # Mutable state variables
    a: Fun[Node, Value]
    prev: Immutable[Fun[Node, Node]]

    def succ_node(self, u: Node, v: Node) -> BoolRef:
        W = Node("W")
        return Or(
            ForAll(W, And(self.leq_node(v, W), self.leq_node(W, u))),
            And(
                u != v,
                self.leq_node(u, v),
                ForAll(W, Or(self.leq_node(v, W), self.leq_node(W, u))),
            ),
        )

    def btw(self, v1: Value, v2: Value, v3: Value) -> BoolRef:
        return And(
            v1 != v2,
            v2 != v3,
            v3 != v1,
            Or(
                And(self.leq_value(v1, v2), self.leq_value(v2, v3)),
                And(self.leq_value(v1, v2), self.leq_value(v3, v1)),
                And(self.leq_value(v2, v3), self.leq_value(v3, v1)),
            ),
        )

    def succ_value(self, u: Value, v: Value) -> BoolRef:
        U = Value("U")
        return Or(
            ForAll(U, And(self.leq_value(v, U), self.leq_value(U, u))),
            And(
                u != v,
                self.leq_value(u, v),
                ForAll(U, Or(self.leq_value(v, U), self.leq_value(U, u))),
            ),
        )

    def priv(self, i: Node) -> BoolRef:
        return Or(
            And(i == self.bot, self.a(i) == self.a(self.prev(i))),
            And(i != self.bot, self.a(i) != self.a(self.prev(i))),
        )

    @axiom
    def leq_node_axioms(self, X: Node, Y: Node, Z: Node) -> BoolRef:
        return And(
            Implies(And(self.leq_node(X, Y), self.leq_node(Y, Z)), self.leq_node(X, Z)),
            Implies(And(self.leq_node(X, Y), self.leq_node(Y, X)), X == Y),
            Or(self.leq_node(X, Y), self.leq_node(Y, X)),
            self.leq_node(self.bot, X),
            self.succ_node(self.prev(X), X),
        )

    @axiom
    def leq_value_axioms(self, S: Value, T: Value, R: Value) -> BoolRef:
        return And(
            Implies(
                And(self.leq_value(S, R), self.leq_value(R, T)),
                self.leq_value(S, T),
            ),
            Implies(And(self.leq_value(S, R), self.leq_value(R, S)), S == R),
            Or(self.leq_value(S, R), self.leq_value(R, S)),
        )

    # this should be with @witness - TODO
    # defining 'witness value' as epsilon(minimal missing value in ring)
    @axiom
    def witness_definition(self, R: Value, X: Node, S: Value) -> BoolRef:
        return Implies(
            Exists(R, ForAll(X, self.a(X) != R)),
            And(
                ForAll(X, self.a(X) != self.witness_value),
                ForAll(
                    S,
                    Implies(
                        ForAll(X, self.a(X) != S),
                        Or(
                            S == self.witness_value,
                            self.btw(self.a(self.bot), self.witness_value, S),
                        ),
                    ),
                ),
            ),
        )

    # Some of our safety premises only hold in finite models, and so we use induction axioms to prove them
    # Our use of induction axioms is based on "Elad, N., Shoham, S.: Axe 'em: Eliminating spurious states with induction axioms."
    @axiom
    def well_founded_axiom(self, X: Node, Y: Node) -> BoolRef:
        return Implies(
            Exists(X, self.a(X) != self.a(self.bot)),
            Exists(
                X,
                And(
                    self.a(X) != self.a(self.bot),
                    ForAll(
                        Y,
                        Implies(self.a(Y) != self.a(self.bot), self.leq_node(X, Y)),
                    ),
                ),
            ),
        )

    # There is an assumption in the protocol that the number of values is larger than the number of nodes
    # This cannot be encoded directly, so we encode the consequence we need of it.
    @axiom
    def more_values_than_nodes_axiom(self, R: Value, X: Node) -> BoolRef:
        return Exists(R, ForAll(X, self.a(X) != R))

    @transition
    def wakeup(self, n: Node) -> BoolRef:
        X = Node("X")
        return And(
            self.skd == n,
            If(
                self.priv(n),
                If(
                    n == self.bot,
                    And(
                        self.succ_value(self.a(self.prev(n)), self.next.a(n)),
                        ForAll(X, Implies(X != n, self.next.a(X) == self.a(X))),
                    ),
                    self.a.update({(n,): self.a(self.prev(n))}),
                ),
                self.a.unchanged(),
            ),
        )


class DijkstraKStateProp(Prop[DijkstraKStateSystem]):
    # as long as privileged nodes are infinitely scheduled then eventually there is a unique privilege
    def prop(self) -> BoolRef:
        X = Node("X")
        Y = Node("Y")
        return Implies(
            G(F(Implies(Exists(X, self.sys.priv(X)), self.sys.priv(self.sys.skd)))),
            F(
                G(
                    ForAll(
                        [X, Y], Implies(And(self.sys.priv(X), self.sys.priv(Y)), X == Y)
                    )
                )
            ),
        )


class DijsktraKStateProof(Proof[DijkstraKStateSystem], prop=DijkstraKStateProp):

    @invariant
    def exists_privilege(self) -> BoolRef:
        N = Node("N")
        return Exists(N, self.sys.priv(N))

    @temporal_invariant
    def scheduling_of_privileged_nodes(self) -> BoolRef:
        X = Node("X")
        return G(F(Implies(Exists(X, self.sys.priv(X)), self.sys.priv(self.sys.skd))))

    def privileged_node_scheduled(self) -> BoolRef:
        X = Node("X")
        return Implies(Exists(X, self.sys.priv(X)), self.sys.priv(self.sys.skd))

    def timer_scheduling(self) -> Rank:
        return self.timer_rank(self.privileged_node_scheduled, None, None)

    def lt_reversed_bot_minimal(self, i1: Node, i2: Node) -> BoolRef:
        return And(
            i1 != i2,
            Or(And(self.sys.leq_node(i2, i1), i2 != self.sys.bot), i1 == self.sys.bot),
        )

    def priv(self, i: Node) -> BoolRef:
        return self.sys.priv(i)

    def lexicographic_privileges(self) -> Rank:
        return DomainLexRank(BinRank(self.priv), self.lt_reversed_bot_minimal, None)

    def value_bot_needs_to_pass(self, v: Value) -> BoolRef:
        return Or(
            And(v == self.sys.a(self.sys.bot), v != self.sys.witness_value),
            self.sys.btw(self.sys.a(self.sys.bot), v, self.sys.witness_value),
        )

    def all_values_bot_needs_to_pass(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.value_bot_needs_to_pass), None)

    # this works but im not sure why? why is it not using the violation of the property
    def rank(self) -> Rank:
        return LexRank(
            self.all_values_bot_needs_to_pass(),
            self.lexicographic_privileges(),
            self.timer_scheduling(),
        )


proof = DijsktraKStateProof()
proof.check()
