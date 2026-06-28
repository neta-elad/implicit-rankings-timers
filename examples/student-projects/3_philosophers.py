"""
Project of Ron Vulkan, Emile Mosseri 
Verification of a solution to the dining philosophers problem with 3 philosophers.
"""

from prelude import *

class Philosopher (Finite): ...
class Chopstick (Expr): ...
class Id (Expr): ...


class DiningSystem(TransitionSystem):
    p0: Immutable[Philosopher]
    p1: Immutable[Philosopher]
    p2: Immutable[Philosopher]

    c0: Immutable[Chopstick]
    c1: Immutable[Chopstick]
    c2: Immutable[Chopstick]

    max: Immutable[Philosopher]

    right: Immutable[Rel[Philosopher, Chopstick]]
    left: Immutable[Rel[Philosopher, Chopstick]]

    btw: Immutable[Rel[Philosopher, Philosopher, Philosopher]] # between
    le: Immutable[Rel[Id, Id]] # <= relation
    phil_chop: Immutable[Fun[Philosopher, Chopstick]]
    succ_phil: Immutable[Fun[Philosopher, Philosopher]]
    chop_le: Immutable[Rel[Chopstick, Chopstick]]

    thinking: Rel[Philosopher]
    grabbing: Rel[Philosopher]
    eating: Rel[Philosopher]
    holding: Rel[Philosopher, Chopstick]
    scheduled: Rel[Philosopher]

    @axiom
    def btw_axioms(self, X: Philosopher, Y: Philosopher, Z: Philosopher, W: Philosopher) -> BoolRef:
        return And(
            # characterizing axioms of the btw relation
            Implies(And(self.btw(W, X, Y), self.btw(W, Y, Z)), self.btw(W, X, Z)),
            Implies(self.btw(W, X, Y), Not(self.btw(W, Y, X))),
            Or(self.btw(W, X, Y), self.btw(W, Y, X), W == X, W == Y, X == Y),
            Implies(self.btw(X, Y, Z), self.btw(Y, Z, X)),
        )

    @axiom
    def le_axioms(self, A: Id, B: Id, C: Id) -> BoolRef:
        return And(
            Implies(And(self.le(A, B), self.le(B, A)), A == B),
            Implies(And(self.le(A, B), self.le(B, C)), self.le(A, C)),
            Or(self.le(A, B), self.le(B, A)),
        )

    @axiom
    def exactly_three_philosophers(self, p: Philosopher) -> BoolRef:
        return Or(p == self.p0, p == self.p1, p == self.p2)

    @axiom
    def exactly_three_chopsticks(self, c: Chopstick) -> BoolRef:
        return Or(c == self.c0, c == self.c1, c == self.c2)

    @axiom
    def philosophers_distinct(self) -> BoolRef:
        return And(
            self.p0 != self.p1,
            self.p0 != self.p2,
            self.p1 != self.p2,
        )

    @axiom
    def chopsticks_distinct(self) -> BoolRef:
        return And(
            self.c0 != self.c1,
            self.c0 != self.c2,
            self.c1 != self.c2,
        )

    @axiom
    def phil_chop_def(self) -> BoolRef:
        return And(
            self.phil_chop(self.p0) == self.c0,
            self.phil_chop(self.p1) == self.c1,
            self.phil_chop(self.p2) == self.c2,
        )

    @axiom
    def max_def(self) -> BoolRef:
        return self.max == self.p2

    def is_max(self, p: Philosopher) -> BoolRef:
        return p == self.max

    @axiom
    def right_def(self, phil: Philosopher, c: Chopstick) -> BoolRef:
        return self.right(phil, c) == (c == self.phil_chop(phil))

    @axiom
    def left_def(self, phil: Philosopher, c: Chopstick) -> BoolRef:
        return self.left(phil, c) == (c == self.phil_chop(self.succ_phil(phil)))

    @axiom
    def succ_is_successor(self, X: Philosopher) -> BoolRef:
        return self.succ(X, self.succ_phil(X))

    @axiom
    def chop_le_def(self) -> BoolRef:
        return And(
            self.chop_le(self.c0, self.c0),
            self.chop_le(self.c0, self.c1),
            self.chop_le(self.c0, self.c2),
            self.chop_le(self.c1, self.c1),
            self.chop_le(self.c1, self.c2),
            self.chop_le(self.c2, self.c2),
        )

    def succ(self, X: Philosopher, Y: Philosopher) -> BoolRef:
        phil = Philosopher('phil')
        return ForAll(
            phil, Implies(
                And(
                    Not(phil == X), Not(phil == Y)
                ),
                self.btw (X,Y, phil)
            )
        )

    def taken(self, s: Chopstick) -> BoolRef:
        p = Philosopher('p')
        return Exists([p], self.holding(p, s))

    def first_chopstick(self, p: Philosopher, s: Chopstick) -> BoolRef:
        return Or(
            And(self.is_max(p), self.right(p, s)),
            And(Not(self.is_max(p)), self.left(p, s)),
        )

    def second_chopstick(self, p: Philosopher, s: Chopstick) -> BoolRef:
        return Or(
            And(self.is_max(p), self.left(p, s)),
            And(Not(self.is_max(p)), self.right(p, s)),
        )

    @init
    def initial(self, phil: Philosopher, chop: Chopstick) -> BoolRef:
        return And(
            self.thinking(phil),
            Not(self.grabbing(phil)),
            Not(self.eating(phil)),
            Not(self.holding(phil, chop))
        )


    @transition
    def thinking_to_thinking(self, phil: Philosopher) -> BoolRef:
        s = Chopstick("s")
        p = Philosopher("p")

        return And(
            self.thinking(phil),

            Exists([s], And(
                self.first_chopstick(phil, s),
                self.taken(s),
            )),

            self.thinking.unchanged(),
            self.grabbing.unchanged(),
            self.eating.unchanged(),
            self.holding.unchanged(),

            ForAll([p], self.scheduled(p) == (p == phil)),
        )

    @transition
    def step_thinking_to_grabbing(self, phil: Philosopher) -> BoolRef:
        p = Philosopher('p')
        s = Chopstick('s')

        return And(
            self.thinking(phil),

            Exists([s], And(
                self.first_chopstick(phil, s),
                Not(self.taken(s)),
            )),

            ForAll(
                [p, s],
                self.next.holding(p, s) ==
                If(
                    p == phil,
                    And(
                        self.first_chopstick(phil, s),
                        Not(self.taken(s)),
                    ),
                    self.holding(p, s)
                )
            ),

            self.thinking.update({(phil,): false}),
            self.grabbing.update({(phil,): true}),
            self.eating.unchanged(),

            ForAll(p, self.scheduled(p) == (p == phil))
        )

    @transition
    def grabbing_to_grabbing(self, phil: Philosopher) -> BoolRef:
        s = Chopstick('s')
        p = Philosopher('p')

        return And(
            self.grabbing(phil),

            Exists([s], And(
                self.second_chopstick(phil, s),
                self.taken(s),
            )),

            self.thinking.unchanged(),
            self.grabbing.unchanged(),
            self.eating.unchanged(),
            self.holding.unchanged(),

            ForAll(p, self.scheduled(p) == (p == phil))
        )

    @transition
    def grabbing_to_eating(self, phil: Philosopher) -> BoolRef:
        p = Philosopher('p')
        s = Chopstick('s')

        return And(
            self.grabbing(phil),

            Exists([s], And(
                self.second_chopstick(phil, s),
                Not(self.taken(s)),
            )),

            ForAll(
                [p, s],
                self.next.holding(p, s) ==
                If(
                    p == phil,
                    Or(
                        self.holding(p, s),
                        And(
                            self.second_chopstick(phil, s),
                            Not(self.taken(s)),
                        )
                    ),
                    self.holding(p, s)
                )
            ),

            self.thinking.unchanged(),
            self.grabbing.update({(phil,): false}),
            self.eating.update({(phil,): true}),

            ForAll(p, self.scheduled(p) == (p == phil))
        )

    @transition
    def eating_to_thinking(self, phil: Philosopher) -> BoolRef:
        p = Philosopher('p')
        s = Chopstick('s')

        return And(
            self.eating(phil),

            ForAll(
                [p, s],
                self.next.holding(p, s) ==
                If(
                    p == phil,
                    false,
                    self.holding(p, s)
                )
            ),

            self.thinking.update({(phil,): true}),
            self.grabbing.unchanged(),
            self.eating.update({(phil,): false}),

            ForAll(p, self.scheduled(p) == (p == phil))
        )

    def holding_first_chopstick(self, p: Philosopher) -> BoolRef:
        s = Chopstick("s")
        return Exists([s], And(
            self.first_chopstick(p, s),
            self.holding(p, s)
        ))

    def can_eat(self, p: Philosopher) -> BoolRef:
        s = Chopstick("s")
        return And(
            self.grabbing(p),
            self.holding_first_chopstick(p),
            Exists([s], And(
                self.second_chopstick(p, s),
                Not(self.taken(s))
            ))
        )

class PhilosopherProp(Prop[DiningSystem]):
    def prop(self) -> BoolRef:
        p = Philosopher('p')
        return Implies(
            ForAll([p], G(F(self.sys.scheduled(p)))),
            G(F(Exists([p], self.sys.eating(p))))
        )

class DinnerProof(Proof[DiningSystem], prop=PhilosopherProp):


    @system_invariant
    def states_are_disjoint(self, p: Philosopher) -> BoolRef:
        return And(
            Or(self.sys.thinking(p), self.sys.grabbing(p), self.sys.eating(p)),
            Not(And(self.sys.thinking(p), self.sys.grabbing(p))),
            Not(And(self.sys.thinking(p), self.sys.eating(p))),
            Not(And(self.sys.grabbing(p), self.sys.eating(p))),
        )

    @invariant
    def at_most_one_holds_chopstick(self,p1: Philosopher, p2: Philosopher, s:Chopstick) -> BoolRef:
        return Implies(And(self.sys.holding(p1,s),self.sys.holding(p2,s)), p1 == p2 )

    @invariant
    def thinking_is_not_holding(self, p: Philosopher, s: Chopstick) -> BoolRef:
        return Implies(
            self.sys.thinking(p),
            Not(self.sys.holding(p,s))
        )



    @invariant
    def grabbing_holds_only_first_chopstick(self, p: Philosopher, s: Chopstick) -> BoolRef:
        return Implies(
            self.sys.grabbing(p),
            self.sys.holding(p, s) == self.sys.first_chopstick(p, s)
        )

    @invariant
    def eating_is_holding_two_chopsticks(self, p: Philosopher, s: Chopstick) -> BoolRef:
        return Implies(
            self.sys.eating(p),
            self.sys.holding(p,s) == Or(self.sys.first_chopstick(p,s), self.sys.second_chopstick(p,s))
        )

    @invariant
    def can_hold_only_two_chopsticks(self, p: Philosopher, s: Chopstick) -> BoolRef:
        return Implies(self.sys.holding(p,s), Or(self.sys.first_chopstick(p,s), self.sys.second_chopstick(p,s)) )

    def rk1(self) -> Rank:
        return self.timer_rank(
            self.no_one_eating_forever(),
            None,
            None
        )

    @temporal_invariant
    @track
    def violation(self) -> BoolRef:
        p = Philosopher("p")
        return F(
            G(
                ForAll([p], Not(self.sys.eating(p)))
            )
        )

    @temporal_invariant
    def fairness(self) -> BoolRef:
        p = Philosopher("p")
        return ForAll([p], G(F(self.sys.scheduled(p))))

    @track
    def no_one_eating_forever(self) -> BoolRef:
        p = Philosopher("p")
        return G(
            ForAll([p], Not(self.sys.eating(p)))
        )

    def can_eat(self, p: Philosopher) -> BoolRef:
        return self.sys.can_eat(p)


    def scheduled(self, p: Philosopher) -> BoolRef:
        return self.sys.scheduled(p)

    def rk_can_eat(self) -> Rank:
        return self.timer_rank(
            self.scheduled,
            self.can_eat,
            None
        )

    def thinking_body(self, p: Philosopher) -> BoolRef:
        return self.sys.thinking(p)

    def thinking_counter(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.thinking_body),
            None
        )

    def rank(self) -> Rank:
        return LexRank(
            self.rk1(),
            self.thinking_counter(),
            self.rk_can_eat(),
        )


DinnerProof().check()