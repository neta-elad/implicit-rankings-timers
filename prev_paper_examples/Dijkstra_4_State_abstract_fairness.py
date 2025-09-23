# type: ignore


from z3 import *
from ts import *
import time


def dijkstra4state():

    # This is the abstraction of Dijkstra 4-state concrete
    # In this file we prove the fairness property.
    # In the abstraction, instead of using next and prev to define the privileges we treat
    # the privileges as new relation symbols that are axiomitized to hold the correct values only for relevant  nodes.

    print("Dijkstra 4-state")

    Node = DeclareSort("Node")
    sorts = [Node]
    X = Const("X", Node)
    Y = Const("Y", Node)
    Z = Const("Z", Node)
    W = Const("W", Node)

    PrivType, (above, below) = EnumSort("PrivType", ("above", "below"))

    constant_sym = {
        "skd": Node,
        "next_skd": Node,
        "prev_skd": Node,
        "top": Node,
        "bot": Node,
    }
    relation_sym = {
        "leq_node": [Node, Node],
        "x": [Node],
        "up": [Node],
        "priv_above": [
            Node
        ],  # instrumentation relation that should hold the value priv_above(i) = x(i) = x(i+1) & up(i) & !up(i+1) for all i != top
        "priv_below": [
            Node
        ],  # instrumentation relation that should hold the value priv_below(i) = x(i) != x(i-1) for all i != bot
    }
    function_sym = {
        #'next' : [Node,Node],
        #'prev' : [Node,Node]
    }

    def succ_node(sym, u, v):
        return Or(
            ForAll(W, And(sym["leq_node"](v, W), sym["leq_node"](W, u))),
            And(
                u != v,
                sym["leq_node"](u, v),
                ForAll(W, Or(sym["leq_node"](v, W), sym["leq_node"](W, u))),
            ),
        )

    def axiom_leq_node(sym):
        return ForAll(
            [X, Y, Z],
            And(
                Implies(
                    And(sym["leq_node"](X, Y), sym["leq_node"](Y, Z)),
                    sym["leq_node"](X, Z),
                ),
                Implies(And(sym["leq_node"](X, Y), sym["leq_node"](Y, X)), X == Y),
                Or(sym["leq_node"](X, Y), sym["leq_node"](Y, X)),
                sym["leq_node"](sym["bot"], X),
                sym["leq_node"](X, sym["top"]),
                # succ_node(sym,sym['prev'](X),X),
                # succ_node(sym,X,sym['next'](X)),
                succ_node(sym, sym["skd"], sym["next_skd"]),
                succ_node(sym, sym["prev_skd"], sym["skd"]),
            ),
        )

    def abstraction_axioms(sym):
        # these are axioms we proved on the concrete model we can assume here
        return And(Exists(X, priv(sym, X)), inst_correct_for_skd(sym))

    def axiom(sym):
        return And(
            axiom_leq_node(sym),
            abstraction_axioms(sym),
        )

    def inst_correct_for_skd(sym):
        skd = sym["skd"]
        prev_skd = sym["prev_skd"]
        next_skd = sym["next_skd"]
        return And(
            sym["priv_above"](skd)
            == And(
                sym["x"](skd) == sym["x"](next_skd),
                sym["up"](skd),
                Not(sym["up"](next_skd)),
                skd != sym["top"],
            ),
            sym["priv_above"](prev_skd)
            == And(
                sym["x"](prev_skd) == sym["x"](skd),
                sym["up"](prev_skd),
                Not(sym["up"](skd)),
                prev_skd != sym["top"],
            ),
            sym["priv_below"](skd)
            == And(sym["x"](skd) != sym["x"](prev_skd), skd != sym["bot"]),
            sym["priv_below"](next_skd)
            == And(sym["x"](next_skd) != sym["x"](skd), next_skd != sym["bot"]),
        )

    def init(sym):
        return And(sym["up"](sym["bot"]) == True, sym["up"](sym["top"]) == False)

    # trivial:
    # maybe though using the instrumentations for the transition precondition is problematic
    def priv_below(sym, i):
        return sym["priv_below"](i)

    def priv_above(sym, i):
        return sym["priv_above"](i)

    def priv(sym, i):
        return Or(priv_above(sym, i), priv_below(sym, i))

    # a more simple notion is how to update the instrumentation variables when a transition takes place, we just need to update
    # priv_below for skd,skd+1 and priv_above for skd,skd-1,
    # in some cases we update some things that will certainly not change, but that does no harm
    # it is easily seen that only the following updates can be necessary for any transition:
    def update_instrumentation(sym1, sym2):
        skd = sym1["skd"]
        prev_skd = sym1["prev_skd"]
        next_skd = sym1["next_skd"]
        return And(
            # priv_above(i) = x(i) = x(i+1) & up(i) & !up(i+1)
            sym2["priv_above"](skd)
            == And(
                sym2["x"](skd) == sym2["x"](next_skd),
                sym2["up"](skd),
                Not(sym2["up"](next_skd)),
                skd != sym2["top"],
            ),
            sym2["priv_above"](prev_skd)
            == And(
                sym2["x"](prev_skd) == sym2["x"](skd),
                sym2["up"](prev_skd),
                Not(sym2["up"](skd)),
                prev_skd != sym2["top"],
            ),
            ForAll(
                X,
                Implies(
                    And(X != skd, X != prev_skd),
                    sym2["priv_above"](X) == sym1["priv_above"](X),
                ),
            ),
            # priv_below(i) = x(i) != x(i-1)
            sym2["priv_below"](skd)
            == And(sym2["x"](skd) != sym2["x"](prev_skd), skd != sym2["bot"]),
            sym2["priv_below"](next_skd)
            == And(sym2["x"](next_skd) != sym2["x"](skd), next_skd != sym2["bot"]),
            ForAll(
                X,
                Implies(
                    And(X != skd, X != next_skd),
                    sym2["priv_below"](X) == sym1["priv_below"](X),
                ),
            ),
        )

    def move_below_normal(sym1, sym2):
        skd = sym1["skd"]
        return And(
            sym2["x"](skd) == Not(sym1["x"](skd)),
            sym2["up"](skd) == True,
            ForAll(X, Implies(X != skd, sym2["x"](X) == sym1["x"](X))),
            ForAll(X, Implies(X != skd, sym2["up"](X) == sym1["up"](X))),
        )

    def move_below_top(sym1, sym2):
        skd = sym1["skd"]
        return And(
            sym2["x"](skd) == Not(sym1["x"](skd)),
            sym2["up"](skd) == sym1["up"](skd),
            ForAll(X, Implies(X != skd, sym2["x"](X) == sym1["x"](X))),
            ForAll(X, Implies(X != skd, sym2["up"](X) == sym1["up"](X))),
        )

    def move_below(sym1, sym2):
        skd = sym1["skd"]
        return If(
            skd == sym1["top"],
            move_below_top(sym1, sym2),
            move_below_normal(sym1, sym2),
        )

    def move_above_normal(sym1, sym2):
        skd = sym1["skd"]
        return And(
            sym2["x"](skd) == sym1["x"](skd),
            sym2["up"](skd) == False,
            ForAll(X, Implies(X != skd, sym2["x"](X) == sym1["x"](X))),
            ForAll(X, Implies(X != skd, sym2["up"](X) == sym1["up"](X))),
        )

    def move_above_bot(sym1, sym2):
        skd = sym1["skd"]
        return And(
            sym2["x"](skd) == Not(sym1["x"](skd)),
            sym2["up"](skd) == sym1["up"](skd),
            ForAll(X, Implies(X != skd, sym2["x"](X) == sym1["x"](X))),
            ForAll(X, Implies(X != skd, sym2["up"](X) == sym1["up"](X))),
        )

    def move_above(sym1, sym2):
        skd = sym1["skd"]
        return If(
            skd == sym1["bot"],
            move_above_bot(sym1, sym2),
            move_above_normal(sym1, sym2),
        )

    def move_idle(sym1, sym2):
        return And(
            ForAll(X, sym2["x"](X) == sym1["x"](X)),
            ForAll(X, sym2["up"](X) == sym1["up"](X)),
        )

    param_wakeup = {}

    def tr_wakeup(sym1, sym2, param):
        skd = sym1["skd"]
        return And(
            sym2["top"] == sym1["top"],
            sym2["bot"] == sym1["bot"],
            ForAll([X, Y], sym2["leq_node"](X, Y) == sym1["leq_node"](X, Y)),
            Or(
                And(priv_above(sym1, skd), move_above(sym1, sym2)),
                And(priv_below(sym1, skd), move_below(sym1, sym2)),
                And(Not(priv(sym1, skd)), move_idle(sym1, sym2)),
            ),  # subtle but this is necessarily an exclusive or
            update_instrumentation(sym1, sym2),
        )

    constant_sym_h = constant_sym | {"node_h": Node}  # herbrand const.
    tr_wakeup_with_node_h = lambda sym1, sym2, param: And(
        tr_wakeup(sym1, sym2, param), sym1["node_h"] == sym2["node_h"]
    )
    tr1_with_node_h = ("wakeup", param_wakeup, tr_wakeup_with_node_h)
    ts = TS(
        sorts,
        axiom,
        init,
        [tr1_with_node_h],
        constant_sym_h,
        relation_sym,
        function_sym,
    )

    def basic_inv(sym):
        return And(
            sym["up"](sym["bot"]) == True,
            sym["up"](sym["top"]) == False,
        )

    def stable(sym):
        return ForAll(
            [X, Y],
            And(
                Implies(And(priv(sym, X), priv(sym, Y)), X == Y),
                Not(And(priv_above(sym, X), priv_below(sym, X))),
            ),
        )

    # We prove something slightly stronger than what is stated generally, any  node gets both kinds of privileges infinitely often

    # Property 1 forall n. G (stable & n != bot -> F priv_below(n))

    r = lambda sym, param: Implies(Exists(X, priv(sym, X)), priv(sym, sym["skd"]))
    sort_dict = {}
    p1 = lambda sym: And(stable(sym), sym["node_h"] != sym["bot"])
    q1 = lambda sym: priv_below(sym, sym["node_h"])
    prop1 = LivenessProperty(p1, q1, [r], [sort_dict])

    rho = basic_inv
    phi1 = lambda sym: And(p1(sym), rho(sym), Not(q1(sym)))
    psi = lambda sym, param: BoolVal(True)

    strict_order = lambda sym, param1, param2: And(
        sym["leq_node"](param1["i"], param2["i"]), param1["i"] != param2["i"]
    )
    reverse_order = lambda sym, param1, param2: And(
        sym["leq_node"](param2["i"], param1["i"]), param1["i"] != param2["i"]
    )

    after_h_below = lambda sym, param: And(
        priv_below(sym, param["i"]), sym["leq_node"](sym["node_h"], param["i"])
    )
    before_h_below = lambda sym, param: And(
        priv_below(sym, param["i"]), sym["leq_node"](param["i"], sym["node_h"])
    )
    priv_above_pred = lambda sym, param: priv_above(sym, param["i"])
    priv_below_pred = lambda sym, param: priv_below(sym, param["i"])
    binary_after_below = BinaryFreeRank(after_h_below, {"i": Node})
    binary_above = BinaryFreeRank(priv_above_pred, {"i": Node})
    binary_before_below = BinaryFreeRank(before_h_below, {"i": Node})
    agg_after_below = ParLexFreeRank(binary_after_below, {"i": Node}, strict_order)
    agg_above = ParLexFreeRank(binary_above, {"i": Node}, reverse_order)
    agg_before_below = ParLexFreeRank(binary_before_below, {"i": Node}, strict_order)
    rank1 = LexFreeRank([agg_after_below, agg_above, agg_before_below])

    proof1 = LivenessProof(prop1, rank1, rho, phi1, [psi])
    print("checking P1")
    proof1.check_proof(ts)

    # with lin atlernatively:
    binary_below = BinaryFreeRank(priv_below_pred)
    binary_above = BinaryFreeRank(priv_above_pred)
    rank_below_right = ParLexFreeRank(binary_below, {"i": Node}, strict_order)
    rank_above_left = ParLexFreeRank(binary_above, {"i": Node}, reverse_order)
    cond1 = lambda sym, param: Exists(
        X, And(sym["leq_node"](sym["node_h"], X), priv_below(sym, X))
    )
    cond2 = lambda sym, param: Exists(X, priv_above(sym, X))
    cond3 = lambda sym, param: Exists(
        X, And(sym["leq_node"](X, sym["node_h"]), priv_below(sym, X))
    )
    delta_lin = LinFreeRank(
        [rank_below_right, rank_above_left, rank_below_right], [cond1, cond2, cond3]
    )

    # Property 2 forall n. G (stable & n != top -> F priv_above(n))

    p2 = lambda sym: And(stable(sym), sym["node_h"] != sym["top"])
    q2 = lambda sym: priv_above(sym, sym["node_h"])
    prop2 = LivenessProperty(p2, q2, [r], [sort_dict])
    phi2 = lambda sym: And(p2(sym), rho(sym), Not(q2(sym)))

    after_h_above = lambda sym, param: And(
        priv_above(sym, param["i"]), sym["leq_node"](sym["node_h"], param["i"])
    )
    before_h_above = lambda sym, param: And(
        priv_above(sym, param["i"]), sym["leq_node"](param["i"], sym["node_h"])
    )

    binary_before_above = BinaryFreeRank(before_h_above, {"i": Node})
    binary_below = BinaryFreeRank(priv_below_pred, {"i": Node})
    binary_after_above = BinaryFreeRank(after_h_above, {"i": Node})
    agg_before_above = ParLexFreeRank(binary_before_above, {"i": Node}, reverse_order)
    agg_below = ParLexFreeRank(binary_below, {"i": Node}, strict_order)
    agg_after_above = ParLexFreeRank(binary_after_above, {"i": Node}, reverse_order)
    rank2 = LexFreeRank([agg_before_above, agg_below, agg_after_above])

    proof2 = LivenessProof(prop2, rank2, rho, phi2, [psi])
    print("checking P2")
    proof2.check_proof(ts)


dijkstra4state()
