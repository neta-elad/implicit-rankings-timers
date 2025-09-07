from prelude import *


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
            self.on.update(lambda old, new, T: new(T) == And(old(T), T != t)),
            # fairness
            ForAll(T, self.scheduled(T) == (T == t)),
        )


class TrivialTerminationProp(Prop[TrivialTerminationSystem]):
    # The property we want to prove -- under fair scheduling, eventually all threads are off, together.
    def negated_prop(self) -> BoolRef:
        T = Thread("T")
        return And(ForAll(T, G(F(self.sys.scheduled(T)))), G(Exists(T, self.sys.on(T))))
        # unnegated prop: Implies(ForAll(T, G(F(self.scheduled(T)))), F(ForAll(T), Not(self.on(T))) non-negated prop


class TrivialTerminationProof(
    Proof[TrivialTerminationSystem], prop=TrivialTerminationProp
):
    @invariant
    def timer_invariant(self) -> BoolRef:
        return And(
            timer_zero(self.t("t_<ForAll(T, G(F(scheduled(T))))>")()),
            # temporal invariant: ForAll(T, G(F(scheduled(T)))
            timer_zero(self.t("t_<G(Exists(T, on(T)))>")()),
        )

    def on(self, t: Thread) -> BoolRef:
        return self.sys.on(t)

    def system_rank(self) -> Rank:
        return DomainPointwiseRank.close(BinRank(self.on), None)

    def scheduled(self, t: Thread) -> Time:
        return self.t("t_<scheduled(T)>")(t)

    def timer_rank(self) -> Rank:
        return timer_rank(None, self.scheduled, self.on)

    def rank(self) -> Rank:
        return LexRank(self.system_rank(), self.timer_rank())


TrivialTerminationProof().check()
