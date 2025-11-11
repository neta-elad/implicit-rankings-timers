# message queue with a sender and a receiver and a middleman example 2 from towards liveness proofs.
# see @exampl4.ivy

# @status - done

from prelude import *


class SignalTime(Expr): ...


class CascadingQueue(TransitionSystem):
    time_lt: Immutable[WFRel[SignalTime]]
    zero: Immutable[SignalTime]

    # state
    pending1: Rel[SignalTime]
    pending2: Rel[SignalTime]
    latest_sent1: SignalTime
    latest_sent2: SignalTime

    # fairness
    sender_value: SignalTime
    receiver_value: SignalTime

    sender_now: Bool
    poll1_now: Bool
    receiver_now: Bool
    try_receive2_now: Bool

    @axiom
    def time_lt_axioms(self, X: SignalTime, Y: SignalTime, Z: SignalTime) -> BoolRef:
        return And(
            Implies(And(self.time_lt(X, Y), self.time_lt(Y, Z)), self.time_lt(X, Z)),
            Not(And(self.time_lt(X, Y), self.time_lt(Y, X))),
            Or(self.time_lt(X, Y), self.time_lt(Y, X), X == Y),
            Not(self.time_lt(X, X)),
            Or(self.time_lt(self.zero, X), X == self.zero),
        )

    @init
    def initial1(self, X: SignalTime) -> BoolRef:
        return And(
            self.pending1(X) == False,
            self.latest_sent1 == self.zero,
        )

    @init
    def initial2(self, X: SignalTime) -> BoolRef:
        return And(
            self.pending2(X) == False,
            self.latest_sent2 == self.zero,
        )

    @transition
    def send1(self, x: SignalTime) -> BoolRef:
        return And(
            self.time_lt(self.latest_sent1, x),
            self.pending1.update({(x,): true}),
            self.sender_value == x,
            self.sender_now == True,
            self.latest_sent1.update(x),
            self.latest_sent2.unchanged(),
            self.pending2.unchanged(),
            self.poll1_now == False,
            self.receiver_now == False,
            self.try_receive2_now == False,
        )

    # split the recv transition into recv_some and recv_none, this is not necessary but nice.
    @transition
    def recv2_some(self, y: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            self.pending2(y),
            ForAll(
                T,
                Implies(
                    self.pending2(T),
                    Or(self.time_lt(y, T), y == T),
                ),
            ),
            self.pending2.update({(y,): false}),
            self.receiver_value == y,
            self.latest_sent1.unchanged(),
            self.latest_sent2.unchanged(),
            self.pending1.unchanged(),
            self.receiver_now == True,
            self.sender_now == False,
            self.poll1_now == True,
            self.try_receive2_now == True,
        )

    @transition
    def recv2_none(self) -> BoolRef:
        T = SignalTime("T")
        return And(
            Not(Exists(T, self.pending2(T))),
            self.pending2.unchanged(),
            self.latest_sent1.unchanged(),
            self.latest_sent2.unchanged(),
            self.pending1.unchanged(),
            self.receiver_now == False,
            self.sender_now == False,
            self.poll1_now == False,
            self.try_receive2_now == True,
        )

    @transition
    def poll1_some(self, x: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            self.pending1(x),
            ForAll(T, Implies(self.pending1(T), Or(self.time_lt(x, T), x == T))),
            self.pending1.update({(x,): false}),
            self.pending2.update({(x,): true}),
            self.time_lt(x, self.latest_sent2),  # follows from invariants
            self.latest_sent2.update(x),
            self.poll1_now == True,
            self.latest_sent1.unchanged(),
            self.sender_now == False,
            self.receiver_now == False,
            self.try_receive2_now == False,
        )

    @transition
    def poll1_none(self) -> BoolRef:
        T = SignalTime("T")
        return And(
            Not(Exists(T, self.pending1(T))),
            self.pending1.unchanged(),
            self.pending2.unchanged(),
            self.latest_sent1.unchanged(),
            self.latest_sent2.unchanged(),
            self.poll1_now == True,
            self.sender_now == False,
            self.receiver_now == False,
            self.try_receive2_now == False,
        )


class CascadingQueueLiveness(Prop[CascadingQueue]):
    def prop(self) -> BoolRef:
        X = SignalTime("X")
        return Implies(
            And(
                G(F(self.sys.try_receive2_now)),
                G(F(self.sys.poll1_now)),
            ),
            ForAll(
                X,
                G(
                    Implies(
                        And(self.sys.sender_now, self.sys.sender_value == X),
                        F(And(self.sys.receiver_now, self.sys.receiver_value == X)),
                    )
                ),
            ),
        )


class CascadingQueueProof(Proof[CascadingQueue], prop=CascadingQueueLiveness):

    @temporal_invariant
    def infinitely_trying(self) -> BoolRef:
        return G(F(self.sys.try_receive2_now))

    @temporal_invariant
    def infinitely_polling(self) -> BoolRef:
        return G(F(self.sys.poll1_now))

    @temporal_witness
    def skolem_time(self, X: SignalTime) -> BoolRef:
        return F(
            And(
                And(self.sys.sender_now, self.sys.sender_value == X),
                G(Or(Not(self.sys.receiver_now), self.sys.receiver_value != X)),
            ),
        )

    def never_receive_skolem(self) -> BoolRef:
        return G(
            Or(Not(self.sys.receiver_now), self.sys.receiver_value != self.skolem_time)
        )

    def send_skolem_never_receive(self) -> BoolRef:
        return And(
            And(
                self.sys.sender_now,
                self.sys.sender_value == self.skolem_time,
            ),
            self.never_receive_skolem(),
        )

    @temporal_invariant
    @track
    def violation_skolem(self) -> BoolRef:
        return Or(
            F(self.send_skolem_never_receive()),
            And(
                self.never_receive_skolem(),
                Or(
                    self.sys.pending1(self.skolem_time),
                    self.sys.pending2(self.skolem_time),
                ),
            ),
        )

    @invariant
    def pending1_greater_than_latest_sent2(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending1(X),
            self.sys.time_lt(self.sys.latest_sent2, X),
        )

    @invariant
    def latest_sent2_lesser_than_latest_sent1(self) -> BoolRef:
        return Or(
            self.sys.time_lt(self.sys.latest_sent2, self.sys.latest_sent1),
            self.sys.latest_sent2 == self.sys.latest_sent1,
        )

    @invariant
    def pending_less_than_latest_sent1(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending1(X),
            Or(self.sys.time_lt(X, self.sys.latest_sent1), X == self.sys.latest_sent1),
        )

    @invariant
    def pending_less_than_latest_sent2(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending2(X),
            Or(self.sys.time_lt(X, self.sys.latest_sent2), X == self.sys.latest_sent2),
        )

    def pending_skolem_never_receive_timer_rank(self) -> Rank:
        return self.timer_rank(
            And(
                self.never_receive_skolem(),
                Or(
                    self.sys.pending1(self.skolem_time),
                    self.sys.pending2(self.skolem_time),
                ),
            ),
            None,
            None,
        )

    def send_skolem_never_receive_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.send_skolem_never_receive(),
            None,
            None,
        )

    def pending1_less_or_equal_skolem(self, x: SignalTime) -> BoolRef:
        return And(
            self.sys.pending1(x),
            Or(self.sys.time_lt(x, self.skolem_time), x == self.skolem_time),
        )

    def set_of_pending1(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.pending1_less_or_equal_skolem),
            FiniteLemma(self.pending1_less_or_equal_skolem),
        )

    def pending2_less_or_equal_skolem(self, x: SignalTime) -> BoolRef:
        return And(
            self.sys.pending2(x),
            Or(self.sys.time_lt(x, self.skolem_time), x == self.skolem_time),
        )

    def set_of_pending2(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.pending2_less_or_equal_skolem),
            FiniteLemma(self.pending2_less_or_equal_skolem),
        )

    def poll1_timer_rank(self) -> Rank:
        T = SignalTime("T")
        return self.timer_rank(
            self.sys.poll1_now,
            Exists(T, self.pending1_less_or_equal_skolem(T)),
            None,
        )

    def trying_timer_rank(self) -> Rank:
        T = SignalTime("T")
        return self.timer_rank(
            self.sys.try_receive2_now,
            Exists(T, self.pending2_less_or_equal_skolem(T)),
            None,
        )

    def rank(self) -> Rank:
        return LexRank(
            self.pending_skolem_never_receive_timer_rank(),
            self.send_skolem_never_receive_timer_rank(),
            self.set_of_pending1(),
            self.set_of_pending2(),
            self.poll1_timer_rank(),
            self.trying_timer_rank(),
        )


proof = CascadingQueueProof()
proof.check(check_conserved=True)
