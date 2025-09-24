from prelude import *

# @status - done


# Notice we assume finitely many indices - a bit different from original modeling, we can modify later.
class Index(Finite): ...


class Value(Expr): ...


class DataMsg(Expr): ...


class AckMsg(Expr): ...


class AlternatingBitProtocol(TransitionSystem):
    zero: Immutable[Index]
    le: Immutable[Rel[Index, Index]]
    sender_index: Index
    sender_gen_index: Index
    receiver_index: Index
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
            self.receiver_index == self.zero,
            self.sender_bit == False,
            self.receiver_bit == False,
            self.le_ack_msg(A1, A2) == False,
            self.le_data_msg(D1, D2) == False,
        )

    @transition
    def gen_data(self, v: Value) -> BoolRef:
        return And(
            # guard
            v != self.bottom,
            # updates
            self.sender_array.update({(self.sender_gen_index,): v}),
            self.succ(self.sender_gen_index, self.next.sender_gen_index),
            self.receiver_array.unchanged(),
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
                    Not(self.le_data_msg(m, m)),
                    # updates
                    self.le_data_msg.forall(
                        lambda D1, D2: (
                            self.next.le_data_msg(D1, D2)
                            == Or(
                                self.le_data_msg(D1, D2),
                                And(D1 == m, D2 == m),
                                And(D1 == m, self.le_data_msg(D2, D2)),
                            )
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
            self.data_sent == (self.sender_array(self.sender_index) != self.bottom),
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
                    self.receiver_array.update({(self.receiver_index,): self.d(m)}),
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
            self.le_data_msg.forall(
                lambda D1, D2: (
                    self.next.le_data_msg(D1, D2)
                    == And(self.le_data_msg(D1, D2), D1 != m, D2 != m)
                )
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
            self.le_ack_msg.forall(
                lambda A1, A2: (
                    self.next.le_ack_msg(A1, A2)
                    == And(self.le_ack_msg(A1, A2), A1 != a, A2 != a)
                )
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


class AlternatingBitProtocolProp(Prop[AlternatingBitProtocol]):
    def prop(self) -> BoolRef:
        I = Index("I")
        return Implies(
            And(
                G(F(self.sys.sender_scheduled)),
                G(F(self.sys.receiver_scheduled)),
                Implies(G(F(self.sys.data_sent)), G(F(self.sys.data_received))),
                Implies(G(F(self.sys.ack_sent)), G(F(self.sys.ack_received))),
            ),
            ForAll(
                I,
                Implies(
                    F(self.sys.sender_array(I) != self.sys.bottom),
                    F(self.sys.receiver_array(I) != self.sys.bottom),
                ),
            ),
        )


class AlternatingBitProtocolProof(
    Proof[AlternatingBitProtocol], prop=AlternatingBitProtocolProp
):
    @temporal_witness
    def skolem_index(self, I: Index) -> BoolRef:
        return Not(
            Implies(
                F(self.sys.sender_array(I) != self.sys.bottom),
                F(self.sys.receiver_array(I) != self.sys.bottom),
            )
        )

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

    @temporal_invariant
    def timer_invariant(self) -> BoolRef:
        return And(
            G(F(self.sys.sender_scheduled)),
            G(F(self.sys.receiver_scheduled)),
            Or(
                F(Not(F(self.sys.data_sent))),
                G(F(self.sys.data_received)),
            ),
            Or(
                F(Not(F(self.sys.ack_sent))),
                G(F(self.sys.ack_received)),
            ),
            F(self.sys.bottom != self.sys.sender_array(self.skolem_index)),
            G(self.sys.bottom == self.sys.receiver_array(self.skolem_index)),
        )

    # main rank part - differences between the current index for generation, sender and receiver and the skolem index, and the time until we write to skolem index

    def write_to_skolem(self) -> BoolRef:
        return self.sys.bottom != self.sys.sender_array(self.skolem_index)

    def btw_gen_skolem(self, i: Index) -> BoolRef:
        return And(
            self.sys.le(i, self.skolem_index),
            self.sys.le(self.sys.sender_gen_index, i),
        )

    # sk_index - sender_gen_i
    def gen_minus_sk(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.btw_gen_skolem), None)

    def btw_sender_skolem(self, i: Index) -> BoolRef:
        return And(
            self.sys.le(i, self.skolem_index),
            self.sys.le(self.sys.sender_index, i),
        )

    # sk_index - sender_i
    def sender_minus_sk(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.btw_sender_skolem), None)

    def btw_receiver_skolem(self, i: Index) -> BoolRef:
        return And(
            self.sys.le(i, self.skolem_index),
            self.sys.le(self.sys.receiver_index, i),
        )

    # sk_index - receiver_i
    def receiver_minus_sk(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.btw_receiver_skolem), None)

    # should be PWRank instead of LexRank
    def primary_rank(self) -> Rank:
        return LexRank(
            self.timer_rank(self.write_to_skolem, None, None),
            self.gen_minus_sk(),
            self.sender_minus_sk(),
            self.receiver_minus_sk(),
        )

    # helper booleans that characterise when the sender is outdated or up-to-date, characterised by the difference between sender and receiver bits.

    def sender_outdated(self) -> BoolRef:
        return self.sys.sender_bit != self.sys.receiver_bit

    def sender_up_to_date(self) -> BoolRef:
        return Not(self.sender_outdated())

    # helpers booleans that characterise fairness

    def ack_fairness_established(self) -> BoolRef:
        return timer_zero(self.t(G(F(self.sys.ack_received)))())

    def no_ack_fairness(self) -> BoolRef:
        return timer_nonzero(self.t(G(F(self.sys.ack_received)))())

    def data_fairness_established(self) -> BoolRef:
        return timer_zero(self.t(G(F(self.sys.data_received)))())

    def no_data_fairness(self) -> BoolRef:
        return timer_nonzero(self.t(G(F(self.sys.data_received)))())

    # When the sender is up to date we wait for them to send new data or for the receiver to receive

    def in_data_queue(self, d: DataMsg) -> BoolRef:
        return self.sys.le_data_msg(d, d)

    def bad_data(self, d: DataMsg) -> BoolRef:
        return self.sys.dbit(d) != self.sys.receiver_bit

    def no_good_data(self) -> BoolRef:
        D = DataMsg("D")
        return ForAll(D, Implies(self.in_data_queue(D), self.bad_data(D)))

    def bin_no_good_data(self) -> Rank:
        return BinRank(self.no_good_data)

    def bad_in_data_queue(self, d: DataMsg) -> BoolRef:
        return And(self.in_data_queue(d), self.bad_data(d))

    def total_bad_data(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.bad_in_data_queue),
            FiniteLemma(self.in_data_queue),
        )

    def data_to_send(self) -> BoolRef:
        return self.sys.sender_array(self.sys.sender_index) != self.sys.bottom

    def sender_scheduling_is_helpful(self) -> BoolRef:
        return And(self.no_good_data(), self.data_to_send())

    def until_sender_scheduled(self) -> Rank:
        return self.timer_rank(
            self.sys.sender_scheduled,
            self.sender_scheduling_is_helpful,
            None,
        )

    def until_data_received(self) -> Rank:
        return self.timer_rank(self.sys.data_received, None, None)

    def rank_sender_uptodate(self) -> Rank:
        return CondRank(
            LexRank(
                self.total_bad_data(),
                self.until_data_received(),
                self.bin_no_good_data(),
                self.until_sender_scheduled(),
            ),
            self.sender_up_to_date,
        )

    # this is relevant only when the data channel is fair

    def rank_data_fairness(self) -> Rank:
        return CondRank(self.rank_sender_uptodate(), self.data_fairness_established)

    # When the sender is outdated we are waiting for them to be scheduled or for the receiver to send a good ack

    def in_ack_queue(self, a: AckMsg) -> BoolRef:
        return self.sys.le_ack_msg(a, a)

    def bad_ack(self, a: AckMsg) -> BoolRef:
        return self.sys.abit(a) != self.sys.sender_bit

    def no_good_ack(self) -> BoolRef:
        A = AckMsg("A")
        return ForAll(A, Implies(self.in_ack_queue(A), self.bad_ack(A)))

    def bin_no_good_ack(self) -> Rank:
        return BinRank(self.no_good_ack)

    def bad_in_ack_queue(self, a: AckMsg) -> BoolRef:
        return And(self.in_ack_queue(a), self.bad_ack(a))

    def total_bad_ack(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.bad_in_ack_queue),
            FiniteLemma(self.in_ack_queue),
        )

    def until_receiver_scheduled(self) -> Rank:
        return self.timer_rank(self.sys.receiver_scheduled, self.no_good_ack, None)

    def until_ack_received(self) -> Rank:
        return self.timer_rank(self.sys.ack_received, None, None)

    def rank_sender_outdated(self) -> Rank:
        return CondRank(
            LexRank(
                self.total_bad_ack(),
                self.until_ack_received(),
                self.bin_no_good_ack(),
                self.until_receiver_scheduled(),
            ),
            self.sender_outdated,
        )

    # this is relevant only when the ack channel is fair

    def rank_ack_fairness(self) -> Rank:
        return CondRank(self.rank_sender_outdated(), self.ack_fairness_established)

    # If the data channel or ack channel are not fair, we wait for the final messages to be sent, and achieve contradiction with fair scheduling.

    def no_future_acks(self) -> BoolRef:
        return Not(F(self.sys.ack_sent))

    def rank_no_ack_fairness(self) -> Rank:
        return CondRank(
            LexRank(
                self.timer_rank(self.no_future_acks, None, None),
                self.timer_rank(self.sys.receiver_scheduled, None, None),
            ),
            self.no_ack_fairness,
        )

    def no_future_data(self) -> BoolRef:
        return Not(F(self.sys.data_sent))

    def rank_no_data_fairness(self) -> Rank:
        return CondRank(
            LexRank(
                self.timer_rank(
                    self.no_future_data,
                    # self.no_future_data,
                    # lambda sys: Not(F(sys.data_sent)),
                    # Not(F(self.sys.data_sent)),
                    # lambda sys, d=DataMsg():
                    None,
                    None,
                ),
                self.timer_rank(
                    self.sys.sender_scheduled,
                    # lambda sys: sys.sender_scheduled
                    # self.sys.sender_scheduled,
                    # lambda sys: sys.sender_array(sys.sender_index) != sys.bottom
                    # self.sys.sender_array(self.sys.sender_index) != self.sys.bottom
                    self.data_to_send,
                    None,
                ),
            ),
            self.no_data_fairness,
        )

    # we compose all these rankings lexicographically

    # it shouldn't really be Lex, could be PW mostly (?) primary rank should be a different component.
    def rank(self) -> Rank:
        return LexRank(
            self.primary_rank(),
            self.rank_ack_fairness(),
            self.rank_data_fairness(),
            self.rank_no_ack_fairness(),
            self.rank_no_data_fairness(),
        )


AlternatingBitProtocolProof().check()
