from prelude import *


class Index(Expr): ...


class Value(Expr): ...


class DataMsg(Expr): ...


class AckMsg(Expr): ...


class AlternatingBitProtocol(TransitionSystem):
    zero: Immutable[Index]
    le: Immutable[Rel[Index, Index]]
    sender_index: Index
    sender_gen_index: Index
    receiver_index: Index
    skolem_index: Index
    bottom: Immutable[Value]
    le_data_msg: Rel[DataMsg, DataMsg]
    le_ack_msg: Rel[AckMsg, AckMsg]
    dbit: Immutable[Rel[DataMsg]]
    abit: Immutable[Rel[AckMsg]]
    sender_bit: Bool
    receiver_bit: Bool
    d: Immutable[Fun[DataMsg, Value]]
    sender_array: Fun[Index, Value]
    receiver_array: Fun[Index, Value]

    sender_scheduled: Bool
    receiver_scheduled: Bool
    data_sent: Bool
    data_received: Bool
    ack_sent: Bool
    ack_received: Bool

    @axiom
    def order_le(self, X: Index, Y: Index, Z: Index) -> BoolRef:
        return And(
            # transitive, antisymmetric and total, with zero as minimal
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Or(self.le(X, Y), self.le(Y, X)),
            self.le(self.zero, X),
        )

    def succ(self, u: Index, v: Index) -> BoolRef:
        X = Index("X")
        return And(
            self.le(u, v),
            Not(u == v),
            ForAll(X, Implies(self.le(u, X), Or(self.le(v, X), X == u))),
        )

    @init
    def initial(
        self, I: Index, D1: DataMsg, D2: DataMsg, A1: AckMsg, A2: AckMsg
    ) -> BoolRef:
        return And(
            self.sender_array(I) == self.bottom,
            self.receiver_array(I) == self.bottom,
            self.sender_index == self.zero,
            self.sender_gen_index == self.zero,
            self.sender_bit == False,
            self.receiver_bit == False,
        )

    @transition
    def gen_data(self, v: Value) -> BoolRef:
        return And(
            # guard
            v != self.bottom,
            # updates
            self.sender_array.update(
                lambda old, new, I: new(I) == If(I == self.sender_gen_index, v, old(I))
            ),
            self.succ(self.sender_gen_index, self.next.sender_gen_index),
            self.sender_index.unchanged(),
            self.receiver_index.unchanged(),
            self.sender_bit.unchanged(),
            self.receiver_bit.unchanged(),
            self.le_data_msg.unchanged(),
            self.le_ack_msg.unchanged(),
            # fairness
            self.sender_scheduled == False,
            self.receiver_scheduled == False,
            self.data_sent == False,
            self.data_received == False,
            self.ack_sent == False,
            self.ack_received == False,
        )

    @transition
    def sender_send_data(self, m: DataMsg) -> BoolRef:
        return And(
            If(
                self.sender_array(self.sender_index) != self.bottom,
                And(
                    # guard
                    self.d(m) == self.sender_array(self.sender_index),
                    self.dbit(m) == self.sender_bit,
                    # updates
                    self.le_data_msg.update(
                        lambda old, new, D1, D2: new(D1, D2)
                        == Or(
                            old(D1, D2),
                            And(D1 == m, D2 == m),
                            And(D1 == m, old(D2, D2)),
                        )
                    ),
                ),
                self.le_data_msg.unchanged(),
            ),
            self.sender_gen_index.unchanged(),
            self.sender_index.unchanged(),
            self.receiver_index.unchanged(),
            self.sender_bit.unchanged(),
            self.receiver_bit.unchanged(),
            self.sender_array.unchanged(),
            self.receiver_array.unchanged(),
            self.le_ack_msg.unchanged(),
            # fairness
            self.sender_scheduled == True,
            self.receiver_scheduled == False,
            self.data_sent == self.sender_array(self.sender_index) != self.bottom,
            self.data_received == False,
            self.ack_sent == False,
            self.ack_received == False,
        )

    @transition
    def sender_receive_ack(self, a: AckMsg) -> BoolRef:
        A1 = AckMsg("A1")
        A2 = AckMsg("A2")
        return And(
            self.le_ack_msg(a, a),
            ForAll(A1, Implies(self.le_ack_msg(a, A1), a == A1)),
            ForAll(
                [A1, A2],
                self.next.le_ack_msg(A1, A2) == And(self.le_ack_msg(A1, A2), A2 != a),
            ),
            If(
                self.abit(a) == self.sender_bit,
                And(
                    self.next.sender_bit == Not(self.sender_bit),
                    self.succ(self.sender_index, self.next.sender_index),
                ),
                And(
                    self.next.sender_bit == self.sender_bit,
                    self.next.sender_index == self.sender_index,
                ),
            ),
            self.sender_gen_index.unchanged(),
            self.receiver_index.unchanged(),
            self.sender_array.unchanged(),
            self.receiver_array.unchanged(),
            self.le_data_msg.unchanged(),
            self.next.receiver_bit == self.receiver_bit,
            # fairness
            self.sender_scheduled == False,
            self.receiver_scheduled == False,
            self.data_sent == False,
            self.data_received == False,
            self.ack_sent == False,
            self.ack_received == True,
        )

    @transition
    def receiver_receive_data(self, m: DataMsg) -> BoolRef:
        D1 = DataMsg("D1")
        D2 = DataMsg("D2")
        return And(
            self.le_data_msg(m, m),
            ForAll(D1, Implies(self.le_data_msg(m, D1), m == D1)),
            ForAll(
                [D1, D2],
                self.next.le_data_msg(D1, D2) == And(self.le_data_msg(D1, D2), D2 != m),
            ),
            If(
                self.dbit(m) == self.receiver_bit,
                And(
                    self.next.receiver_bit == Not(self.receiver_bit),
                    self.receiver_array.update(
                        lambda old, new, J: new(J)
                        == If(J == self.receiver_index, self.d(m), old(J))
                    ),
                    self.succ(self.receiver_index, self.next.receiver_index),
                ),
                And(
                    self.receiver_bit.unchanged(),
                    self.receiver_array.unchanged(),
                    self.receiver_index.unchanged(),
                ),
            ),
            self.sender_gen_index.unchanged(),
            self.sender_index.unchanged(),
            self.sender_array.unchanged(),
            self.le_ack_msg.unchanged(),
            self.sender_bit.unchanged(),
            # fairness
            self.sender_scheduled == False,
            self.receiver_scheduled == False,
            self.data_sent == False,
            self.data_received == True,
            self.ack_sent == False,
            self.ack_received == False,
        )

    @transition
    def receiver_send_ack(self, a: AckMsg) -> BoolRef:
        A1 = AckMsg("A1")
        A2 = AckMsg("A2")
        return And(
            self.abit(a) == Not(self.receiver_bit),
            Not(self.le_ack_msg(a, a)),
            ForAll(
                [A1, A2],
                self.next.le_ack_msg(A1, A2)
                == Or(
                    self.le_ack_msg(A1, A2),
                    And(A1 == a, A2 == a),
                    And(A1 == a, self.le_ack_msg(A2, A2)),
                ),
            ),
            self.sender_gen_index.unchanged(),
            self.sender_index.unchanged(),
            self.receiver_index.unchanged(),
            self.sender_bit.unchanged(),
            self.receiver_bit.unchanged(),
            self.sender_array.unchanged(),
            self.receiver_array.unchanged(),
            self.le_data_msg.unchanged(),
            # fairness
            self.sender_scheduled == False,
            self.receiver_scheduled == True,
            self.data_sent == False,
            self.data_received == False,
            self.ack_sent == True,
            self.ack_received == False,
        )

    @transition
    def data_msg_drop(self, m: DataMsg) -> BoolRef:
        return And(
            self.le_data_msg.update(
                lambda old, new, D1, D2: new(D1, D2)
                == And(old(D1, D2), D1 != m, D2 != m)
            ),
            self.sender_gen_index.unchanged(),
            self.sender_index.unchanged(),
            self.receiver_index.unchanged(),
            self.sender_bit.unchanged(),
            self.receiver_bit.unchanged(),
            self.sender_array.unchanged(),
            self.receiver_array.unchanged(),
            self.le_ack_msg.unchanged(),
            # fairness
            self.sender_scheduled == False,
            self.receiver_scheduled == False,
            self.data_sent == False,
            self.data_received == False,
            self.ack_sent == False,
            self.ack_received == False,
        )

    @transition
    def ack_msg_drop(self, a: AckMsg) -> BoolRef:
        return And(
            self.le_ack_msg.update(
                lambda old, new, A1, A2: new(A1, A2)
                == And(old(A1, A2), A1 != a, A2 != a)
            ),
            self.sender_gen_index.unchanged(),
            self.sender_index.unchanged(),
            self.receiver_index.unchanged(),
            self.sender_bit.unchanged(),
            self.receiver_bit.unchanged(),
            self.sender_array.unchanged(),
            self.receiver_array.unchanged(),
            self.le_data_msg.unchanged(),
            # fairness
            self.sender_scheduled == False,
            self.receiver_scheduled == False,
            self.data_sent == False,
            self.data_received == False,
            self.ack_sent == False,
            self.ack_received == False,
        )


class AlternatingBitProtocolProof(Proof[AlternatingBitProtocol]):
    """
    ForAll([M1, M2, M3], Implies(And(sym['le_data_msg'](M1, M2), sym['le_data_msg'](M2, M3)), sym['le_data_msg'](M1, M3))),
    ForAll([M1, M2], Implies(And(sym['le_data_msg'](M1, M2), sym['le_data_msg'](M2, M1)), M1 == M2)),
    ForAll([M1, M2], Implies(sym['le_data_msg'](M1, M2), And(sym['le_data_msg'](M1, M1), sym['le_data_msg'](M2, M2)))),
    ForAll([M1, M2], Implies(And(sym['le_data_msg'](M1, M1), sym['le_data_msg'](M2, M2)), Or(sym['le_data_msg'](M1, M2), sym['le_data_msg'](M2, M1)))),

    ForAll([A1, A2, A3], Implies(And(sym['le_ack_msg'](A1, A2), sym['le_ack_msg'](A2, A3)), sym['le_ack_msg'](A1, A3))),
    ForAll([A1, A2], Implies(And(sym['le_ack_msg'](A1, A2), sym['le_ack_msg'](A2, A1)), A1 == A2)),
    ForAll([A1, A2], Implies(sym['le_ack_msg'](A1, A2), And(sym['le_ack_msg'](A1, A1), sym['le_ack_msg'](A2, A2)))),
    ForAll([A1, A2], Implies(And(sym['le_ack_msg'](A1, A1), sym['le_ack_msg'](A2, A2)), Or(sym['le_ack_msg'](A1, A2), sym['le_ack_msg'](A2, A1)))),
    ForAll(I, sym['le_index'](sym['sender_gen_i'], I) == (sym['sender_array'](I) == sym['bot'])),
    ForAll(I, sym['le_index'](sym['receiver_i'], I) == (sym['receiver_array'](I) == sym['bot'])),
    sym['le_index'](sym['sender_i'], sym['sender_gen_i']),
    ForAll(A, Implies(And(Not(sym['sender_bit']), Not(sym['receiver_bit']), sym['le_ack_msg'](A, A)), sym['abit'](A))),
    ForAll([M1, M2], Implies(
        And(Not(sym['sender_bit']), Not(sym['receiver_bit']), sym['le_data_msg'](M1, M2)),
        Not(And(sym['dbit'](M1), Not(sym['dbit'](M2))))
    )),
    ForAll(A, Implies(And(sym['sender_bit'], sym['receiver_bit'], sym['le_ack_msg'](A, A)), Not(sym['abit'](A)))),
    ForAll([M1, M2], Implies(
        And(sym['sender_bit'], sym['receiver_bit'], sym['le_data_msg'](M1, M2)),
        Not(And(Not(sym['dbit'](M1)), sym['dbit'](M2)))
    )),
    ForAll(M, Implies(And(Not(sym['sender_bit']), sym['receiver_bit'], sym['le_data_msg'](M, M)), Not(sym['dbit'](M)))),
    ForAll([A1, A2], Implies(And(Not(sym['sender_bit']), sym['receiver_bit'], sym['le_ack_msg'](A1, A2)), Not(And(sym['abit'](A1), Not(sym['abit'](A2)))))),
    ForAll(M, Implies(And(sym['sender_bit'], Not(sym['receiver_bit']), sym['le_data_msg'](M, M)), sym['dbit'](M))),
    ForAll([A1, A2], Implies(And(sym['sender_bit'], Not(sym['receiver_bit']), sym['le_ack_msg'](A1, A2)), Not(And(Not(sym['abit'](A1)), sym['abit'](A2))))),
    Implies(sym['sender_bit'] == sym['receiver_bit'], sym['sender_i'] == sym['receiver_i']),
    Implies(sym['sender_bit'] != sym['receiver_bit'], And(
        Not(sym['le_index'](sym['receiver_i'], sym['sender_i'])),
        ForAll(I, Implies(Not(sym['le_index'](I, sym['sender_i'])), sym['le_index'](sym['receiver_i'], I)))
    )),
    ForAll(M, Implies(And(sym['le_data_msg'](M, M), sym['dbit'](M) == sym['sender_bit']), Not(sym['le_index'](sym['sender_gen_i'], sym['sender_i'])))),
    ForAll(M, Implies(And(sym['le_data_msg'](M, M), sym['dbit'](M) == sym['sender_bit']), sym['d'](M) == sym['sender_array'](sym['sender_i']))),
    ForAll(M, Implies(sym['le_data_msg'](M, M), sym['d'](M) != sym['bot'])),
    ForAll(A, Implies(And(sym['le_ack_msg'](A, A), sym['abit'](A) == sym['sender_bit']), Not(sym['le_index'](sym['receiver_i'], sym['sender_i'])))),
    ForAll(A, Implies(And(sym['le_ack_msg'](A, A), sym['abit'](A) == sym['sender_bit']), sym['receiver_array'](sym['sender_i']) == sym['sender_array'](sym['sender_i']))),
    ForAll(A, Implies(And(sym['le_ack_msg'](A, A), sym['abit'](A) == sym['sender_bit']), sym['receiver_array'](sym['sender_i']) != sym['bot'])),
    ForAll(I, Implies(sym['receiver_array'](I) != sym['bot'], sym['receiver_array'](I) == sym['sender_array'](I))),
    )
    """

    @invariant
    def system_invariant(
        self,
        D1: DataMsg,
        D2: DataMsg,
        D3: DataMsg,
        A1: AckMsg,
        A2: AckMsg,
        A3: AckMsg,
        I: Index,
        D: DataMsg,
        A: AckMsg,
    ) -> BoolRef:
        return And(
            Implies(
                And(self.sys.le_data_msg(D1, D2), self.sys.le_data_msg(D2, D3)),
                self.sys.le_data_msg(D1, D3),
            ),
            Implies(
                And(self.sys.le_data_msg(D1, D2), self.sys.le_data_msg(D2, D1)),
                D1 == D2,
            ),
            Implies(
                self.sys.le_data_msg(D1, D2),
                And(self.sys.le_data_msg(D1, D1), self.sys.le_data_msg(D2, D2)),
            ),
            Implies(
                And(self.sys.le_data_msg(D1, D1), self.sys.le_data_msg(D2, D2)),
                Or(self.sys.le_data_msg(D1, D2), self.sys.le_data_msg(D2, D1)),
            ),
            Implies(
                And(self.sys.le_ack_msg(A1, A2), self.sys.le_ack_msg(A2, A3)),
                self.sys.le_ack_msg(A1, A3),
            ),
            Implies(
                And(self.sys.le_ack_msg(A1, A2), self.sys.le_ack_msg(A2, A1)),
                A1 == A2,
            ),
            Implies(
                self.sys.le_ack_msg(A1, A2),
                And(self.sys.le_ack_msg(A1, A1), self.sys.le_ack_msg(A2, A2)),
            ),
            Implies(
                And(self.sys.le_ack_msg(A1, A1), self.sys.le_ack_msg(A2, A2)),
                Or(self.sys.le_ack_msg(A1, A2), self.sys.le_ack_msg(A2, A1)),
            ),
            self.sys.le(self.sys.sender_gen_index, I)
            == (self.sys.sender_array(I) == self.sys.bottom),
            self.sys.le(self.sys.receiver_index, I)
            == (self.sys.receiver_array(I) == self.sys.bottom),
            self.sys.le(self.sys.sender_index, self.sys.sender_gen_index),
            Implies(
                And(
                    Not(self.sys.sender_bit),
                    Not(self.sys.receiver_bit),
                    self.sys.le_ack_msg(A, A),
                ),
                self.sys.abit(A),
            ),
            Implies(
                And(
                    Not(self.sys.sender_bit),
                    Not(self.sys.receiver_bit),
                    self.sys.le_data_msg(D1, D2),
                ),
                Not(And(self.sys.dbit(D1), Not(self.sys.dbit(D2)))),
            ),
            Implies(
                And(
                    self.sys.sender_bit,
                    self.sys.receiver_bit,
                    self.sys.le_ack_msg(A, A),
                ),
                Not(self.sys.abit(A)),
            ),
            Implies(
                And(
                    self.sys.sender_bit,
                    self.sys.receiver_bit,
                    self.sys.le_data_msg(D1, D2),
                ),
                Not(And(Not(self.sys.dbit(D1)), self.sys.dbit(D2))),
            ),
            Implies(
                And(
                    Not(self.sys.sender_bit),
                    self.sys.receiver_bit,
                    self.sys.le_data_msg(D, D),
                ),
                Not(self.sys.dbit(D)),
            ),
            Implies(
                And(
                    Not(self.sys.sender_bit),
                    self.sys.receiver_bit,
                    self.sys.le_ack_msg(A1, A2),
                ),
                Not(And(self.sys.abit(A1), Not(self.sys.abit(A2)))),
            ),
            Implies(
                And(
                    self.sys.sender_bit,
                    Not(self.sys.receiver_bit),
                    self.sys.le_data_msg(D, D),
                ),
                self.sys.dbit(D),
            ),
            Implies(
                And(
                    self.sys.sender_bit,
                    Not(self.sys.receiver_bit),
                    self.sys.le_ack_msg(A1, A2),
                ),
                Not(And(Not(self.sys.abit(A1)), self.sys.abit(A2))),
            ),
            Implies(
                self.sys.sender_bit == self.sys.receiver_bit,
                self.sys.sender_index == self.sys.receiver_index,
            ),
            Implies(
                self.sys.sender_bit != self.sys.receiver_bit,
                And(
                    Not(self.sys.le(self.sys.receiver_index, self.sys.sender_index)),
                    Implies(
                        Not(self.sys.le(I, self.sys.sender_index)),
                        self.sys.le(self.sys.receiver_index, I),
                    ),
                ),
            ),
            Implies(
                And(
                    self.sys.le_data_msg(D, D), self.sys.dbit(D) == self.sys.sender_bit
                ),
                Not(self.sys.le(self.sys.sender_gen_index, self.sys.sender_index)),
            ),
            Implies(
                And(
                    self.sys.le_data_msg(D, D), self.sys.dbit(D) == self.sys.sender_bit
                ),
                self.sys.d(D) == self.sys.sender_array(self.sys.sender_index),
            ),
            Implies(
                self.sys.le_data_msg(D, D),
                self.sys.d(D) != self.sys.bottom,
            ),
            Implies(
                And(self.sys.le_ack_msg(A, A), self.sys.abit(A) == self.sys.sender_bit),
                Not(self.sys.le(self.sys.receiver_index, self.sys.sender_index)),
            ),
            Implies(
                And(self.sys.le_ack_msg(A, A), self.sys.abit(A) == self.sys.sender_bit),
                self.sys.receiver_array(self.sys.sender_index)
                == self.sys.sender_array(self.sys.sender_index),
            ),
            Implies(
                And(self.sys.le_ack_msg(A, A), self.sys.abit(A) == self.sys.sender_bit),
                self.sys.receiver_array(self.sys.sender_index) != self.sys.bottom,
            ),
            Implies(
                self.sys.receiver_array(I) != self.sys.bottom,
                self.sys.receiver_array(I) == self.sys.sender_array(I),
            ),
        )

    def negated_prop(self) -> BoolRef:
        return self.sys.sender_bit

    def rank(self) -> Rank:
        return LexRank()


AlternatingBitProtocolProof().check()
