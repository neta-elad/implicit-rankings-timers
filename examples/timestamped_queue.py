# timestamped queue with a sender and a receiver, example 1 from towards liveness proofs.
# see @exampl1.ivy

# @status - works, but I had a bunch of normalization issues in the progress, discuss.

from prelude import *


class SignalTime(Expr): ...


class TimestampedQueue(TransitionSystem):
    time_lt: Immutable[WFRel[SignalTime]]

    sender_value: SignalTime
    receiver_value: SignalTime
    pending: Rel[SignalTime]
    sender_now: Bool
    receiver_now: Bool
    trying_now: Bool

    @axiom
    def time_lt_axioms(self, X: SignalTime, Y: SignalTime, Z: SignalTime) -> BoolRef:
        return And(
            Implies(And(self.time_lt(X, Y), self.time_lt(Y, Z)), self.time_lt(X, Z)),
            Not(And(self.time_lt(X, Y), self.time_lt(Y, X))),
            Or(self.time_lt(X, Y), self.time_lt(Y, X), X == Y),
            Not(self.time_lt(X, X)),
        )

    @init
    def initial(self, X: SignalTime) -> BoolRef:
        return And(
            self.pending(X) == False,
        )

    # note that receiver_value and sender_value are sometimes unconstrained.
    @transition
    def send(self, x: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            ForAll(
                T,
                Implies(
                    self.pending(T),
                    self.time_lt(T, x),
                ),
            ),
            self.pending.update({(x,): true}),
            # raise action
            self.sender_value == x,
            self.sender_now == True,
            self.receiver_now == False,
            self.trying_now == False,
        )

    # split the recv transition into recv_some and recv_none, this is not necessary but nice.
    @transition
    def recv_some(self, y: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            self.pending(y),
            ForAll(
                T,
                Implies(
                    self.pending(T),
                    Or(self.time_lt(y, T), y == T),
                ),
            ),
            self.pending.update({(y,): false}),
            # raise action
            self.receiver_value == y,
            self.receiver_now == True,
            self.sender_now == False,
            self.trying_now == True,
        )

    @transition
    def recv_none(self) -> BoolRef:
        T = SignalTime("T")
        return And(
            Not(Exists(T, self.pending(T))),
            self.pending.unchanged(),
            self.receiver_now == False,
            self.sender_now == False,
            self.trying_now == True,
        )


class TimestampedQueueLiveness(Prop[TimestampedQueue]):
    def prop(self) -> BoolRef:
        X = SignalTime("X")
        return Implies(
            G(F(self.sys.trying_now)),
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


class TimestampedQueueProof(Proof[TimestampedQueue], prop=TimestampedQueueLiveness):

    @temporal_invariant
    def infinitely_trying(self) -> BoolRef:
        return G(F(self.sys.trying_now))

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
            And(self.sys.pending(self.skolem_time), self.never_receive_skolem()),
        )

    def pending_skolem_never_receive_timer_rank(self) -> Rank:
        return self.timer_rank(
            And(self.sys.pending(self.skolem_time), self.never_receive_skolem()),
            None,
            None,
        )

    def send_skolem_never_receive_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.send_skolem_never_receive(),
            None,
            None,
        )

    def trying_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.sys.trying_now,
            None,
            None,
        )

    def pending_less_than_skolem(self, x: SignalTime) -> BoolRef:
        return And(
            self.sys.pending(x),
            self.sys.time_lt(x, self.skolem_time),
        )

    def set_of_pending(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.pending_less_than_skolem),
            FiniteLemma(self.pending_less_than_skolem),
        )

    # Note: this rank is a little more complex than it could be because of imprceise semantics of timers.
    def rank(self) -> Rank:
        return LexRank(
            self.pending_skolem_never_receive_timer_rank(),
            self.send_skolem_never_receive_timer_rank(),
            self.set_of_pending(),
            self.trying_timer_rank(),
        )


proof = TimestampedQueueProof()
proof.check(check_conserved=True)
