# type: ignore
from z3 import *
from ts import *


def dpll():

    # simplified DPLL algorithm for sat solving
    # Nieuwenhuis, R., Oliveras, A., Tinelli, C. (2005). Abstract DPLL and Abstract DPLL Modulo Theories.
    # Logic for Programming, Artificial Intelligence, and Reasoning. LPAR 2005. https://doi.org/10.1007/978-3-540-32275-7_3
    # we also allow clause learning

    # The clauses in the formula are those that satisfy in_F (which is immutable)
    # Still some transitions may be taken with clauses that are not in F.

    print("sat_cdcl")

    Variable = DeclareSort("Variable")
    Clause = DeclareSort("Clause")
    Level = DeclareSort("Level")

    X = Const("X", Variable)
    Y = Const("Y", Variable)
    Z = Const("Z", Variable)
    W = Const("W", Variable)
    C = Const("C", Clause)
    D = Const("D", Clause)
    b = Const("b", BoolSort())
    b1 = Const("b1", BoolSort())
    b2 = Const("b2", BoolSort())
    i = Const("i", Level)
    j = Const("j", Level)
    k = Const("k", Level)

    tt = BoolVal(True)
    ff = BoolVal(False)

    sorts = [Variable, Clause, Level]

    constant_sym = {
        "fail": BoolSort(),
        "curr_lvl": Level,  # level one higher than end of M (maybe unnecessary?)
        "min_level": Level,
    }
    relation_sym = {
        "lvl_order": [Level, Level],
        "M_seq": [
            Level,
            Variable,
            BoolSort(),
        ],  # sequence of literals, maybe hold the set of literals as well?
        "decision_lvl": [Level],  # the level is a decision level
        "assign_lvl": [
            Level
        ],  # this level is an assignment level (could be derived as well)
        "appears": [
            Clause,
            Variable,
            BoolSort(),
        ],  # where false stands for the negation
        "in_F": [Clause],
    }
    function_sym = {}

    succ = lambda sym, x, y: And(
        x != y,
        sym["lvl_order"](x, y),
        ForAll(k, Implies(sym["lvl_order"](x, k), Or(k == x, sym["lvl_order"](y, k)))),
    )
    order_axiom = lambda sym: And(
        ForAll(
            [i, j], Implies(And(sym["lvl_order"](i, j), sym["lvl_order"](j, i)), i == j)
        ),
        ForAll(
            [i, j, k],
            Implies(
                And(sym["lvl_order"](i, j), sym["lvl_order"](j, k)),
                sym["lvl_order"](i, k),
            ),
        ),
        ForAll([i, j], Or(sym["lvl_order"](i, j), sym["lvl_order"](j, i))),
        ForAll([i], sym["lvl_order"](sym["min_level"], i)),
    )
    second_order_axiom = lambda sym: And(
        # axiom that models the second-order behavior of clauses - required for totality (which we don't prove but can be proved)
        # we didn't formalize this but you can always add axioms of the form ... exists(C, ForAll([X,b],appears(C,X,b)) as long
        # because any set of literals is a clause
        ForAll(
            i,
            Exists(
                C,
                And(
                    ForAll(
                        [X, b],
                        sym["appears"](C, X, b)
                        == Exists(
                            j,
                            And(
                                sym["lvl_order"](j, i),
                                sym["M_seq"](i, X, Not(b)),
                                sym["decision_lvl"](i),
                            ),
                        ),
                    )
                ),
            ),
        )
    )
    axiom = lambda sym: And(order_axiom(sym), second_order_axiom(sym))

    def undefined(sym, x):
        return ForAll([i, b], Not(sym["M_seq"](i, x, b)))

    def init(sym):
        return And(
            ForAll(X, undefined(sym, X)),
            sym["curr_lvl"] == sym["min_level"],
            ForAll(i, Not(sym["decision_lvl"](i))),
            ForAll(i, Not(sym["assign_lvl"](i))),
            ForAll([i, X, b], Not(sym["M_seq"](i, X, b))),
        )

    def immutable(sym1, sym2):
        return And(
            sym2["min_level"] == sym1["min_level"],
            ForAll([i, j], sym2["lvl_order"](i, j) == sym1["lvl_order"](i, j)),
            ForAll([X, b, C], sym2["appears"](C, X, b) == sym1["appears"](C, X, b)),
        )

    def occurs_in_clause_of_F(sym, x):
        return Exists(
            D,
            And(sym["in_F"](D), Or(sym["appears"](D, x, tt), sym["appears"](D, x, ff))),
        )

    param_unit_prop = {"c": Clause, "x": Variable, "bool": BoolSort()}

    def unit_prop(sym1, sym2, param):
        c = param["c"]
        x = param["x"]
        bool = param["bool"]
        appears = sym1["appears"]
        curr_seq = sym1["M_seq"]
        next_seq = sym2["M_seq"]
        curr_lvl = sym1["curr_lvl"]
        next_level = sym2["curr_lvl"]
        return And(
            sym1["in_F"](c),
            appears(c, x, bool),
            undefined(sym1, x),
            ForAll(
                [X, b],
                Implies(
                    And(appears(c, X, b), Not(And(X == x, b == bool))),
                    Exists(i, curr_seq(i, X, Not(b))),
                ),
            ),  # M models neg c \ l
            immutable(sym1, sym2),
            succ(sym1, curr_lvl, next_level),
            ForAll(
                [i, X, b],
                next_seq(i, X, b)
                == Or(curr_seq(i, X, b), And(i == curr_lvl, X == x, b == bool)),
            ),
            ForAll(i, sym2["decision_lvl"](i) == sym1["decision_lvl"](i)),
            ForAll(
                i, sym2["assign_lvl"](i) == Or(sym1["assign_lvl"](i), i == curr_lvl)
            ),
            sym2["fail"] == sym1["fail"],
            ForAll(C, sym2["in_F"](C) == sym1["in_F"](C)),
        )

    tr1 = ("unit_prop", param_unit_prop, unit_prop)

    param_decide = {"x": Variable, "bool": BoolSort()}

    def decide(sym1, sym2, param):
        x = param["x"]
        bool = param["bool"]
        appears = sym1["appears"]
        curr_seq = sym1["M_seq"]
        next_seq = sym2["M_seq"]
        curr_lvl = sym1["curr_lvl"]
        next_level = sym2["curr_lvl"]
        return And(
            occurs_in_clause_of_F(sym1, x),
            undefined(sym1, x),
            immutable(sym1, sym2),
            succ(sym1, curr_lvl, next_level),
            ForAll(
                [i, X, b],
                next_seq(i, X, b)
                == Or(curr_seq(i, X, b), And(i == curr_lvl, X == x, b == bool)),
            ),
            ForAll(
                i, sym2["decision_lvl"](i) == Or(sym1["decision_lvl"](i), i == curr_lvl)
            ),
            ForAll(
                i, sym2["assign_lvl"](i) == Or(sym1["assign_lvl"](i), i == curr_lvl)
            ),
            sym2["fail"] == sym1["fail"],
            ForAll(C, sym2["in_F"](C) == sym1["in_F"](C)),
        )

    tr2 = ("decide", param_decide, decide)

    param_fail = {"c": Clause}

    def fail(sym1, sym2, param):
        c = param["c"]
        appears = sym1["appears"]
        return And(
            sym1["in_F"](c),
            ForAll(i, Not(sym1["decision_lvl"](i))),
            ForAll(
                [X, b],
                Implies(appears(c, X, b), Exists(i, sym1["M_seq"](i, X, Not(b)))),
            ),  # M models neg c
            immutable(sym1, sym2),
            ForAll(i, sym2["decision_lvl"](i) == sym1["decision_lvl"](i)),
            sym2["curr_lvl"] == sym1["curr_lvl"],
            ForAll([i, X, b], sym2["M_seq"](i, X, b) == sym1["M_seq"](i, X, b)),
            ForAll(i, sym2["assign_lvl"](i) == sym1["assign_lvl"](i)),
            sym2["fail"] == True,
            ForAll(C, sym2["in_F"](C) == sym1["in_F"](C)),
        )

    tr3 = ("fail", param_fail, fail)

    param_backjump = {
        "c_learn": Clause,
        "x_old": Variable,
        "b_old": BoolSort(),
        "x_new": Variable,
        "b_new": BoolSort(),
        "lvl": Level,
        "c_witness": Clause,
    }

    def backjump(sym1, sym2, param):
        c_learn = param["c_learn"]
        x_old = param["x_old"]
        b_old = param["b_old"]
        x_new = param["x_new"]
        b_new = param["b_new"]
        lvl = param["lvl"]
        appears = sym1["appears"]
        curr_seq = sym1["M_seq"]
        next_seq = sym2["M_seq"]
        next_level = sym2["curr_lvl"]
        return And(
            curr_seq(lvl, x_old, b_old),
            sym1["decision_lvl"](lvl),
            appears(c_learn, x_new, b_new),
            # We do not encode the fact that F models c
            ForAll(
                [X, b],
                Implies(
                    And(appears(c_learn, X, b), Not(And(X == x_new, b == b_new))),
                    Exists(i, curr_seq(i, X, Not(b))),
                ),
            ),  # M models neg c \ l_new
            undefined(sym1, x_new),
            occurs_in_clause_of_F(sym1, x_new),
            # transition:
            immutable(sym1, sym2),
            ForAll(
                i,
                sym2["decision_lvl"](i)
                == And(sym1["decision_lvl"](i), sym1["lvl_order"](i, lvl), i != lvl),
            ),
            ForAll(
                i,
                sym2["assign_lvl"](i)
                == And(sym1["assign_lvl"](i), sym1["lvl_order"](i, lvl)),
            ),
            succ(sym1, lvl, next_level),  # pushing back the next level one after lvl
            sym2["fail"] == sym1["fail"],
            ForAll(
                [i, X, b],
                next_seq(i, X, b)
                == Or(
                    And(
                        curr_seq(i, X, b), sym1["lvl_order"](i, lvl), i != lvl
                    ),  # all variable assignments before lvl stay
                    And(i == lvl, X == x_new, b == b_new),  # new variable assignment
                ),
            ),
            ForAll(C, sym2["in_F"](C) == sym1["in_F"](C)),
        )

    tr4 = ("backjump", param_backjump, backjump)

    # in the paper above we have on the four transitions, we add a simple clause learning
    # transition, that is abstracted similarly to tr4 that guarantees termination but not safety.
    param_learn = {"c_learn": Clause}

    def learn(sym1, sym2, param):
        return And(
            Not(sym1["in_F"](param["c_learn"])),
            # Not modeling the fact that c_learn follows from F - not safe
            immutable(sym1, sym2),
            ForAll(i, sym2["decision_lvl"](i) == sym1["decision_lvl"](i)),
            sym2["curr_lvl"] == sym1["curr_lvl"],
            ForAll([i, X, b], sym2["M_seq"](i, X, b) == sym1["M_seq"](i, X, b)),
            ForAll(i, sym2["assign_lvl"](i) == sym1["assign_lvl"](i)),
            sym2["fail"] == sym1["fail"],
            ForAll(C, sym2["in_F"](C) == Or(sym1["in_F"](C), C == param["c_learn"])),
        )

    tr5 = ("learn", param_learn, learn)

    transitions = [tr1, tr2, tr3, tr4, tr5]
    ts = TS(sorts, axiom, init, transitions, constant_sym, relation_sym, function_sym)

    def M_sats_F(sym):
        return ForAll(
            C,
            Implies(
                sym["in_F"](C),
                Exists([i, X, b], And(sym["M_seq"](i, X, b), sym["appears"](C, X, b))),
            ),
        )

    def termination(sym):
        return Or(sym["fail"], M_sats_F(sym))

    def inv(sym):
        M = sym["M_seq"]
        return And(
            ForAll([i, X, b], Implies(M(i, X, b), occurs_in_clause_of_F(sym, X))),
            ForAll(
                [i, j, X, b1, b2],
                Implies(And(M(i, X, b1), M(j, X, b2)), And(i == j, b1 == b2)),
            ),
            # third invariant - seems to be for safety, and maybe lost in abstraction
            # get back to this maybe (Lemma 4)
            # ForAll([i,j],Implies(
            #    sym['lvl_order'](i,j),Implies(
            #        Exists([X,b],M(j,X,b)),
            #        Exists([X,b],M(i,X,b))
            #    ))),
            ForAll(
                i,
                Implies(
                    And(sym["lvl_order"](i, sym["curr_lvl"]), i != sym["curr_lvl"]),
                    sym["assign_lvl"](i),
                ),
            ),
            ForAll(
                [i, j],
                Implies(
                    sym["lvl_order"](i, j),
                    Implies(sym["assign_lvl"](j), sym["assign_lvl"](i)),
                ),
            ),
            ForAll(i, Implies(sym["decision_lvl"](i), sym["assign_lvl"](i))),
            ForAll(i, sym["assign_lvl"](i) == Exists([X, b], M(i, X, b))),
            Not(sym["assign_lvl"](sym["curr_lvl"])),
        )

    ts.check_inductiveness(inv)

    r = true
    p = true
    q = termination
    prop = LivenessProperty(p, q, [r], [{}])

    rho = inv
    phi = lambda sym: And(rho(sym), Not(q(sym)))
    psi = true

    c_clause_dict = {"c": Clause}
    not_in_F = lambda sym, param: Not(sym["in_F"](param["c"]))
    bin_not_in_F = BinaryFreeRank(not_in_F, c_clause_dict)
    num_not_in_F = ParPointwiseFreeRank(bin_not_in_F, c_clause_dict)

    x_var_dict = {"x": Variable}
    undefined_x = lambda sym, param: undefined(sym, param["x"])
    bin_unassigned = BinaryFreeRank(undefined_x, x_var_dict)
    num_unasssigned = ParPointwiseFreeRank(bin_unassigned, x_var_dict)

    i_dict = {"i": Level}
    j_dict = {"j": Level}
    ij_dict = i_dict | j_dict
    strict_order = lambda sym, param1, param2: And(
        sym["lvl_order"](param1["i"], param2["i"]), param1["i"] != param2["i"]
    )

    # the main component of the ranking is a lexicographic tuple of sets sizes
    # that counts for each level i the number of levels above it that have assignments without a decision level
    # for example for the assignment:
    # a a d a d a x x (d denotes a decision, a non-decision assignment and x is non-assinged)
    # the correpsonding ranking is then:
    # 2 1 0 1 0 1 0 0
    # this increases lexicographically so we take a negation.
    # the corresponding ranking is conserved in all transitions and reduced in unitprop and and backjump
    # the other ranking component is reduced for decide (transition fail just reaches eventuality)
    def j_counts_towards_i(sym, param):
        ipar = param["i"]
        jpar = param["j"]
        decision = sym["decision_lvl"]
        assign_lvl = sym["assign_lvl"]
        order = sym["lvl_order"]
        return And(
            assign_lvl(ipar),
            assign_lvl(jpar),
            order(ipar, jpar),
            ForAll(k, Implies(And(order(ipar, k), order(k, jpar)), Not(decision(k)))),
        )

    negated_pred = lambda sym, param: Not(j_counts_towards_i(sym, param))

    binary_ij = BinaryFreeRank(negated_pred, ij_dict)
    sum_j = ParPointwiseFreeRank(binary_ij, j_dict, i_dict)
    rank_lex = ParLexFreeRank(sum_j, i_dict, strict_order)

    rank_total = LexFreeRank([rank_lex, num_unasssigned, num_not_in_F])

    proof = LivenessProof(prop, rank_total, rho, phi, [psi])
    proof.check_proof(ts)


dpll()
