# message queue with a sender and a receiver, example 1 from towards liveness proofs.
# see @exampl.ivy

from prelude import *
import temporal

# the system is modeled with a signal for the sender and the receiver, and the queue itself


class SignalTime(Expr): ...


class MessageQueue(TransitionSystem):
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
            self.receiver_now == False,
            self.sender_now == False,
            self.trying_now == True,
        )


class MessageQueueLiveness(Prop[MessageQueue]):
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


class MessageQueueProof(Proof[MessageQueue], prop=MessageQueueLiveness):

    @temporal_invariant
    def infinitely_trying(self) -> BoolRef:
        return G(F(self.sys.trying_now))

    @temporal_witness
    def skolem_time(self, X: SignalTime) -> BoolRef:
        return Not(
            G(
                Implies(
                    And(self.sys.sender_now, self.sys.sender_value == X),
                    F(And(self.sys.receiver_now, self.sys.receiver_value == X)),
                )
            ),
        )

    # interesting case of imprecise semantics
    @track
    @temporal_invariant
    def eventually_sender_value_skolem_time(self) -> BoolRef:
        return F(self.sys.sender_value == self.skolem_time)

    def rank(self) -> Rank:
        return BinRank(true)


proof = MessageQueueProof()
proof.check(check_conserved=True)
