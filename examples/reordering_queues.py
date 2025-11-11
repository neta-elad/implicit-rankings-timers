# two sending queues that merge into an arrival queue, where messages on each queue may bypass each other.
# see @exampl5.ivy
# removed the "latest" variables, they seemed to have just been left by mistake (the clock replaces them)

# @status - done

from prelude import *


class SignalTime(Expr): ...


class ArrivalTime(Expr): ...


class ReorderingQueue(TransitionSystem):
    time_lt: Immutable[WFRel[SignalTime]]
    arrival_time_lt: Immutable[WFRel[ArrivalTime]]
    zero: Immutable[SignalTime]
    zero_arrival: Immutable[ArrivalTime]

    # state
    clock: SignalTime
    arrival_clock: ArrivalTime
    done: ArrivalTime
    arrival_times: Fun[SignalTime, ArrivalTime]

    # queue1 and queue2 merge into queue3
    pending1: Rel[SignalTime]
    pending2: Rel[SignalTime]
    pending3: Rel[SignalTime]

    # fairness
    sender1_value: SignalTime
    sender2_value: SignalTime
    receiver_value: SignalTime
    sender1_now: Bool
    sender2_now: Bool
    poll1_now: Bool
    poll2_now: Bool
    try_receive_now: Bool
    receiver_now: Bool

    @axiom
    def time_lt_axioms(self, X: SignalTime, Y: SignalTime, Z: SignalTime) -> BoolRef:
        return And(
            Implies(And(self.time_lt(X, Y), self.time_lt(Y, Z)), self.time_lt(X, Z)),
            Not(And(self.time_lt(X, Y), self.time_lt(Y, X))),
            Or(self.time_lt(X, Y), self.time_lt(Y, X), X == Y),
            Not(self.time_lt(X, X)),
            Or(self.time_lt(self.zero, X), X == self.zero),
        )

    @axiom
    def arrival_time_lt_axioms(
        self, X: ArrivalTime, Y: ArrivalTime, Z: ArrivalTime
    ) -> BoolRef:
        return And(
            Implies(
                And(self.arrival_time_lt(X, Y), self.arrival_time_lt(Y, Z)),
                self.arrival_time_lt(X, Z),
            ),
            Not(And(self.arrival_time_lt(X, Y), self.arrival_time_lt(Y, X))),
            Or(self.arrival_time_lt(X, Y), self.arrival_time_lt(Y, X), X == Y),
            Not(self.arrival_time_lt(X, X)),
            Or(self.arrival_time_lt(self.zero_arrival, X), X == self.zero_arrival),
        )

    def arrival_time_successor(self, x: ArrivalTime, y: ArrivalTime) -> BoolRef:
        Z = ArrivalTime("Z")
        return And(
            self.arrival_time_lt(x, y),
            ForAll(
                Z,
                Implies(
                    self.arrival_time_lt(x, Z), Or(Z == y, self.arrival_time_lt(y, Z))
                ),
            ),
        )

    @init
    def initial(self, X: SignalTime) -> BoolRef:
        return And(
            self.pending1(X) == False,
            self.pending2(X) == False,
            self.pending3(X) == False,
            self.arrival_times(X) == self.zero_arrival,
            self.clock == self.zero,
            self.arrival_clock == self.zero_arrival,
            self.done == self.zero_arrival,
        )

    @transition
    def send1(self, x: SignalTime) -> BoolRef:
        return And(
            self.time_lt(self.clock, x),
            self.clock.update(x),
            self.pending1.update({(x,): true}),
            self.sender1_value == x,
            self.sender1_now == True,
            self.pending2.unchanged(),
            self.pending3.unchanged(),
            self.arrival_times.unchanged(),
            self.arrival_clock.unchanged(),
            self.done.unchanged(),
            self.sender2_now == False,
            self.poll1_now == False,
            self.poll2_now == False,
            self.receiver_now == False,
            self.try_receive_now == False,
        )

    @transition
    def send2(self, x: SignalTime) -> BoolRef:
        return And(
            self.time_lt(self.clock, x),
            self.clock.update(x),
            self.pending2.update({(x,): true}),
            self.sender2_value == x,
            self.sender2_now == True,
            self.pending1.unchanged(),
            self.pending3.unchanged(),
            self.arrival_times.unchanged(),
            self.arrival_clock.unchanged(),
            self.done.unchanged(),
            self.sender1_now == False,
            self.poll1_now == False,
            self.poll2_now == False,
            self.receiver_now == False,
            self.try_receive_now == False,
        )

    @transition
    def poll1_some(self, x: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            self.pending1(x),
            ForAll(T, Implies(self.pending1(T), Or(self.time_lt(x, T), x == T))),
            self.pending1.update({(x,): false}),
            self.pending3.update({(x,): true}),
            ForAll(T, self.next.arrival_times(T) == If(
                T == x,
                self.arrival_clock,
                self.arrival_times(T),
            )),
            # self.arrival_times.update({(x,): self.arrival_clock}), #potentially buggy?
            self.arrival_time_successor(self.arrival_clock, self.next.arrival_clock),
            self.done.unchanged(),
            self.clock.unchanged(),
            self.pending2.unchanged(),
            self.poll1_now == True,
            self.poll2_now == False,
            self.sender1_now == False,
            self.sender2_now == False,
            self.receiver_now == False,
            self.try_receive_now == False,
        )

    @transition
    def poll1_none(self) -> BoolRef:
        T = SignalTime("T")
        return And(
            Not(Exists(T, self.pending1(T))),
            self.pending1.unchanged(),
            self.pending2.unchanged(),
            self.pending3.unchanged(),
            self.arrival_times.unchanged(),
            self.arrival_clock.unchanged(),
            self.done.unchanged(),
            self.clock.unchanged(),
            self.poll1_now == True,
            self.poll2_now == False,
            self.sender1_now == False,
            self.sender2_now == False,
            self.receiver_now == False,
            self.try_receive_now == False,
        )

    @transition
    def poll2_some(self, x: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            self.pending2(x),
            ForAll(T, Implies(self.pending2(T), Or(self.time_lt(x, T), x == T))),
            self.pending2.update({(x,): false}),
            self.pending3.update({(x,): true}),
            self.arrival_times.update({(x,): self.arrival_clock}),
            self.arrival_time_successor(self.arrival_clock, self.next.arrival_clock),
            self.done.unchanged(),
            self.clock.unchanged(),
            self.pending1.unchanged(),
            self.poll1_now == False,
            self.poll2_now == True,
            self.sender1_now == False,
            self.sender2_now == False,
            self.receiver_now == False,
            self.try_receive_now == False,
        )

    @transition
    def poll2_none(self) -> BoolRef:
        T = SignalTime("T")
        return And(
            Not(Exists(T, self.pending2(T))),
            self.pending1.unchanged(),
            self.pending2.unchanged(),
            self.pending3.unchanged(),
            self.arrival_times.unchanged(),
            self.arrival_clock.unchanged(),
            self.done.unchanged(),
            self.clock.unchanged(),
            self.poll1_now == False,
            self.poll2_now == True,
            self.sender1_now == False,
            self.sender2_now == False,
            self.receiver_now == False,
            self.try_receive_now == False,
        )

    @transition
    def receive_some(self, y: SignalTime) -> BoolRef:
        T = SignalTime("T")
        return And(
            self.pending3(y),
            # y has minimal arrival_times(y)
            ForAll(
                T,
                Implies(
                    self.pending3(T),
                    Or(
                        self.arrival_times(T) == self.arrival_times(y),
                        self.arrival_time_lt(
                            self.arrival_times(y), self.arrival_times(T)
                        ),
                    ),
                ),
            ),
            self.pending3.update({(y,): false}),
            self.arrival_time_successor(self.done, self.next.done),
            self.pending1.unchanged(),
            self.pending2.unchanged(),
            self.clock.unchanged(),
            self.arrival_clock.unchanged(),
            self.arrival_times.unchanged(),
            self.receiver_value == y,
            self.receiver_now == True,
            self.try_receive_now == True,
            self.sender1_now == False,
            self.sender2_now == False,
            self.poll1_now == False,
            self.poll2_now == False,
        )

    @transition
    def receive_none(self) -> BoolRef:
        T = SignalTime("T")
        return And(
            Not(Exists(T, self.pending3(T))),
            self.pending1.unchanged(),
            self.pending2.unchanged(),
            self.pending3.unchanged(),
            self.arrival_times.unchanged(),
            self.arrival_clock.unchanged(),
            self.done.unchanged(),
            self.clock.unchanged(),
            self.receiver_now == False,
            self.try_receive_now == True,
            self.sender1_now == False,
            self.sender2_now == False,
            self.poll1_now == False,
            self.poll2_now == False,
        )


class ReorderingQueueLiveness(Prop[ReorderingQueue]):
    def prop(self) -> BoolRef:
        X = SignalTime("X")
        return Implies(
            And(
                G(F(self.sys.poll1_now)),
                G(F(self.sys.try_receive_now)),
            ),
            ForAll(
                X,
                G(
                    Implies(
                        And(self.sys.sender1_now, self.sys.sender1_value == X),
                        F(And(self.sys.receiver_now, self.sys.receiver_value == X)),
                    )
                ),
            ),
        )


class ReorderingQueueProof(Proof[ReorderingQueue], prop=ReorderingQueueLiveness):


    @invariant
    def pending1_greater_than_clock(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending1(X),
            Or(self.sys.time_lt(X, self.sys.clock), X == self.sys.clock),
        )

    @invariant
    def pending2_greater_than_clock(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending2(X),
            Or(self.sys.time_lt(X, self.sys.clock), X == self.sys.clock),
        )

    # invariants about queue3

    @invariant
    def pending3_less_arrived_before_arrival_clock(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending3(X),
            self.sys.arrival_time_lt(self.sys.arrival_times(X), self.sys.arrival_clock),
        )

    # note: the following three invariants depend on each other.
    @invariant
    def arrival_clock_more_than_done(self) -> BoolRef:
        return Or(
            self.sys.done == self.sys.arrival_clock,
            self.sys.arrival_time_lt(self.sys.done, self.sys.arrival_clock),
        )

    @invariant
    def pending3_less_arrived_after_done(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending3(X),
            Or(
                self.sys.done == self.sys.arrival_times(X),
                self.sys.arrival_time_lt(self.sys.done, self.sys.arrival_times(X)),
            ),
        )

    @invariant
    def different_arrival_times(self, X: SignalTime, Y: SignalTime) -> BoolRef:
        return Implies(
            And(self.sys.pending3(X), self.sys.pending3(Y), X != Y),
            self.sys.arrival_times(X) != self.sys.arrival_times(Y),
        )

    @invariant
    def pending3_greater_than_clock(self, X: SignalTime) -> BoolRef:
        return Implies(
            self.sys.pending3(X),
            Or(self.sys.time_lt(X, self.sys.clock), X == self.sys.clock),
        )

    # invariants connecting the queues

    @invariant
    def no_time_is_pending_on_two_queues(self, X: SignalTime) -> BoolRef:
        return Not(
            Or(
                And(self.sys.pending1(X), self.sys.pending2(X)),
                And(self.sys.pending1(X), self.sys.pending3(X)),
                And(self.sys.pending2(X), self.sys.pending3(X)),
            )
        )

    # temporal invariants

    @temporal_invariant
    def infinitely_trying(self) -> BoolRef:
        return G(F(self.sys.try_receive_now))

    @temporal_invariant
    def infinitely_polling(self) -> BoolRef:
        return G(F(self.sys.poll1_now))

    @temporal_witness
    def skolem_time(self, X: SignalTime) -> BoolRef:
        return F(
            And(
                And(self.sys.sender1_now, self.sys.sender1_value == X),
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
                self.sys.sender1_now,
                self.sys.sender1_value == self.skolem_time,
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
                    self.sys.pending3(self.skolem_time),
                ),
            ),
        )

    # timer ranks

    def pending_skolem_never_receive_timer_rank(self) -> Rank:
        return self.timer_rank(
            And(
                self.never_receive_skolem(),
                Or(
                    self.sys.pending1(self.skolem_time),
                    self.sys.pending3(self.skolem_time),
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

    def poll1_timer_rank(self) -> Rank:
        T = SignalTime("T")
        return self.timer_rank(
            self.sys.poll1_now,
            Exists(T, self.pending1_less_or_equal_skolem(T)),
            None,
        )

    def pending3_arrival_time_less_or_equal_skolem(self, x: SignalTime) -> BoolRef:
        return And(
            self.sys.pending3(x),
            Or(
                self.sys.arrival_time_lt(
                    self.sys.arrival_times(x),
                    self.sys.arrival_times(self.skolem_time),
                ),
                self.sys.arrival_times(x) == self.sys.arrival_times(self.skolem_time),
            ),
        )

    def finiteness_lemma_pending3(self, x: SignalTime) -> BoolRef:
        return self.sys.pending3(x)

    def set_of_pending3(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.pending3_arrival_time_less_or_equal_skolem),
            FiniteLemma(self.finiteness_lemma_pending3),
        )

    def try_receive_timer_rank(self) -> Rank:
        return self.timer_rank(
            self.sys.try_receive_now,
            self.sys.pending3(self.skolem_time),
            None,
        )

    def rank(self) -> Rank:
        return LexRank(
            self.pending_skolem_never_receive_timer_rank(),
            self.send_skolem_never_receive_timer_rank(),
            self.set_of_pending1(),
            self.poll1_timer_rank(),
            self.set_of_pending3(),
            self.try_receive_timer_rank(),
        )


    # currently doesn't work.
    # phantom state: 
    # skolem is sent over queue2 

proof = ReorderingQueueProof()
proof.check()
