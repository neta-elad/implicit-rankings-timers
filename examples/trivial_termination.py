from prelude import *

# @status - done


class Thread(Finite): ...


class TrivialTerminationSystem(TransitionSystem):
    on: Rel[Thread]
    scheduled: Rel[Thread]

    @init
    def initial(self, T: Thread) -> BoolRef:
        return And(
            self.on(T),
        )

    @transition
    def turn_off(self, t: Thread) -> BoolRef:
        T = Thread("T")
        return And(
            # updates
            self.on.update({(t,): false}),
            # fairness
            ForAll(T, self.scheduled(T) == (T == t)),
        )


class TrivialTerminationProp(Prop[TrivialTerminationSystem]):
    # The property we want to prove -- under fair scheduling, eventually all threads are off, together.
    def prop(self) -> BoolRef:
        T = Thread("T")
        return Implies(
            ForAll(T, G(F(self.sys.scheduled(T)))), F(ForAll(T, Not(self.sys.on(T))))
        )


class TrivialTerminationProof(
    Proof[TrivialTerminationSystem], prop=TrivialTerminationProp
):
    @temporal_invariant
    def fair_scheduling(self, T: Thread) -> BoolRef:
        return G(F(self.sys.scheduled(T)))

    @temporal_invariant
    def timer_invariant(self) -> BoolRef:
        T = Thread("T")
        return G(Exists(T, self.sys.on(T)))

    def on(self, T: Thread) -> BoolRef:
        return self.sys.on(T)

    def system_rank(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.on), None)

    def scheduled(self, T: Thread) -> BoolRef:
        return self.sys.scheduled(T)

    def scheduled_timer_rank(self) -> Rank:
        return self.timer_rank(self.scheduled, self.on, None)

    def rank(self) -> Rank:
        return LexRank(self.system_rank(), self.scheduled_timer_rank())


TrivialTerminationProof().check()
