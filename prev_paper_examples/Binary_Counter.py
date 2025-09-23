# type: ignore

from z3 import *
from ts import *


def binary_counter():

    # original modeling of an increasing counter
    # from : Oren Ish-Shalom, Shachar Itzhaky, Noam Rinetzky, and Sharon Shoham. 2022.
    # Runtime Complexity Bounds Using Squeezers.
    # ACM Trans. Program. Lang. Syst. 44, 3, Article 17 (September 2022), 36 pages. https://doi.org/10.1145/3527632

    print("binary_counter_original")

    true = lambda sym: True

    Index = DeclareSort("Index")
    X = Const("X", Index)
    Y = Const("Y", Index)
    Z = Const("Z", Index)

    constant_sym = {
        "zero": Index,
        #'max' : Index,
        "ptr": Index,
    }
    relation_sym = {
        "a": [Index],  # if a holds that means the cell has a 1, otherwise it has a 0
        "le": [Index, Index],
    }
    function_sym = {}

    axiom_le = lambda sym: And(
        ForAll([X, Y], Implies(And(sym["le"](X, Y), sym["le"](Y, X)), X == Y)),
        ForAll(
            [X, Y, Z], Implies(And(sym["le"](X, Y), sym["le"](Y, Z)), sym["le"](X, Z))
        ),
        ForAll([X, Y], Or(sym["le"](X, Y), sym["le"](Y, X))),
        ForAll(X, sym["le"](sym["zero"], X)),
        # ForAll(X,sym['le'](X,sym['max']))
    )
    axiom = lambda sym: And(axiom_le(sym))

    succ = lambda sym, n1, n2: And(
        n1 != n2,
        sym["le"](n1, n2),
        ForAll(Z, Implies(sym["le"](n1, Z), Or(Z == n1, sym["le"](n2, Z)))),
    )

    init = lambda sym: And(ForAll(X, sym["a"](X) == False), sym["ptr"] == sym["zero"])

    def scan1prefix(sym1, sym2):
        return And(
            sym2["a"](sym1["ptr"]) == False,
            ForAll(X, Implies(X != sym1["ptr"], sym2["a"](X) == sym1["a"](X))),
            succ(sym1, sym1["ptr"], sym2["ptr"]),
        )

    def increment(sym1, sym2):
        return And(
            sym2["a"](sym1["ptr"]) == True,
            ForAll(X, Implies(X != sym1["ptr"], sym2["a"](X) == sym1["a"](X))),
            sym2["ptr"] == sym1["zero"],
        )

    tr_param = {}

    def tr_increase(sym1, sym2, param):
        return And(
            sym2["zero"] == sym1["zero"],
            # sym2['max']==sym1['max'],
            ForAll([X, Y], sym2["le"](X, Y) == sym1["le"](X, Y)),
            If(
                sym1["a"](sym1["ptr"]) == True,
                scan1prefix(sym1, sym2),
                increment(sym1, sym2),
            ),
        )

    tr1 = ["increase", tr_param, tr_increase]

    ts = TS([Index], axiom, init, [tr1], constant_sym, relation_sym, function_sym)

    # property and start of proof, default arguments
    p = true
    q = lambda sym: ForAll(X, sym["a"](X))
    r = lambda sym, param: True
    prop = LivenessProperty(p, q, [r], [{}])

    rho = true
    phi = true
    psi = lambda sym, param: True

    # defining rank:
    # first component - the value in the reversed order of ptr
    i_index = {"i": Index}
    reverse_order = lambda sym, param1, param2: And(
        sym["le"](param2["i"], param1["i"]), param1["i"] != param2["i"]
    )
    order_rank = PositionInOrderFreeRank(
        reverse_order, i_index, {"i": lambda sym, param: sym["ptr"]}, {}
    )
    order_rank.print_conserved(ts)

    # second component - the content of the array (at last point where ptr = 0),
    # decreasing lexicographically. Again, here we need the reversed order and negated array elements
    x_was_last_1 = lambda sym, param: Not(
        Or(
            sym["a"](param["i"]),
            And(sym["le"](param["i"], sym["ptr"]), param["i"] != sym["ptr"]),
        )
    )
    free_rank = BinaryFreeRank(x_was_last_1, i_index)
    lex_rank = ParLexFreeRank(free_rank, i_index, reverse_order)

    final_rank = LexFreeRank([lex_rank, order_rank])
    final_rank.print_reduced(ts)

    proof = LivenessProof(prop, final_rank, rho, phi, [psi])
    proof.check_proof(ts)


def binary_counter_rev():

    # how we present in the paper: decreasing counter instead of increasing, and order of msb and lsb flipped.

    print("binary_counter")

    true = lambda sym: True

    Index = DeclareSort("Index")
    X = Const("X", Index)
    Y = Const("Y", Index)
    Z = Const("Z", Index)

    constant_sym = {"max": Index, "ptr": Index}
    relation_sym = {
        "a": [Index],  # if a holds that means the cell has a 1, otherwise it has a 0
        "le": [Index, Index],
    }
    function_sym = {}

    axiom_le = lambda sym: And(
        ForAll([X, Y], Implies(And(sym["le"](X, Y), sym["le"](Y, X)), X == Y)),
        ForAll(
            [X, Y, Z], Implies(And(sym["le"](X, Y), sym["le"](Y, Z)), sym["le"](X, Z))
        ),
        ForAll([X, Y], Or(sym["le"](X, Y), sym["le"](Y, X))),
        ForAll(X, sym["le"](X, sym["max"])),
    )
    axiom = lambda sym: And(axiom_le(sym))

    succ = lambda sym, n1, n2: And(
        n1 != n2,
        sym["le"](n1, n2),
        ForAll(Z, Implies(sym["le"](n1, Z), Or(Z == n1, sym["le"](n2, Z)))),
    )

    init = lambda sym: And(ForAll(X, sym["a"](X) == True), sym["ptr"] == sym["max"])

    def scan0suffix(sym1, sym2):
        return And(
            sym2["a"](sym1["ptr"]) == True,
            ForAll(X, Implies(X != sym1["ptr"], sym2["a"](X) == sym1["a"](X))),
            succ(sym1, sym2["ptr"], sym1["ptr"]),
        )

    def decrement(sym1, sym2):
        return And(
            sym2["a"](sym1["ptr"]) == False,
            ForAll(X, Implies(X != sym1["ptr"], sym2["a"](X) == sym1["a"](X))),
            sym2["ptr"] == sym1["max"],
        )

    tr_param = {}

    def tr_decrease(sym1, sym2, param):
        return And(
            sym2["max"] == sym1["max"],
            ForAll([X, Y], sym2["le"](X, Y) == sym1["le"](X, Y)),
            If(
                sym1["a"](sym1["ptr"]) == False,
                scan0suffix(sym1, sym2),
                decrement(sym1, sym2),
            ),
        )

    tr1 = ["decrease", tr_param, tr_decrease]

    ts = TS([Index], axiom, init, [tr1], constant_sym, relation_sym, function_sym)

    # property and start of proof, default arguments
    p = true
    q = lambda sym: ForAll(X, sym["a"](X))
    r = lambda sym, param: True
    prop = LivenessProperty(p, q, [r], [{}])

    rho = true
    phi = true
    psi = lambda sym, param: True

    # defining rank:
    # first component - the value in the order of ptr
    i_index = {"i": Index}
    index_order = lambda sym, param1, param2: And(
        sym["le"](param1["i"], param2["i"]), param1["i"] != param2["i"]
    )
    order_rank = PositionInOrderFreeRank(
        index_order, i_index, {"i": lambda sym, param: sym["ptr"]}, {}
    )
    # order_rank.print_conserved(ts)

    # second component - the content of the array (at last point where ptr = max),
    x_was_last_1 = lambda sym, param: And(
        sym["a"](param["i"]), sym["le"](param["i"], sym["ptr"])
    )
    free_rank = BinaryFreeRank(x_was_last_1, i_index)
    lex_rank = ParLexFreeRank(free_rank, i_index, index_order)
    # lex_rank.print_reduced(ts)

    final_rank = LexFreeRank([lex_rank, order_rank])
    # final_rank.print_reduced(ts)

    proof = LivenessProof(prop, final_rank, rho, phi, [psi])

    proof.check_proof(ts)


binary_counter_rev()
