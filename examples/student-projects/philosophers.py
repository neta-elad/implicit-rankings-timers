"""
Project of Ron Vulkan, Emile Mosseri 
Verification of a solution to the dining philosophers problem with arbitrary number of philosophers.
"""

from prelude import *

class Philosopher (Finite): ...
class Chopstick (Finite): ...
class Id (Finite): ...

class DiningSystem (TransitionSystem):
    le: Immutable[Rel[Id, Id]] # <= relation
    btw: Immutable[Rel[Philosopher, Philosopher, Philosopher]] # between
    phil_id: Immutable[Fun[Philosopher, Id]] # numbering the philosophers
    chop_id: Immutable[Fun[Chopstick, Id]] # numbering chopsticks
    max: Immutable[Philosopher] # the maximum
    right: Immutable[Rel[Philosopher, Chopstick]]
    left: Immutable[Rel[Philosopher, Chopstick]]
    succ_phil: Immutable[Fun[Philosopher, Philosopher]]
    phil_chop: Immutable[Fun[Philosopher, Chopstick]]


    thinking: Rel[Philosopher] # The philosophers are thinking
    grabbing: Rel[Philosopher] # The philosophers took 1 chopstick
    eating: Rel[Philosopher] # The philosophers are using both chopsticks
    holding: Rel[Philosopher, Chopstick]
    scheduled: Rel[Philosopher] # Fairness

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
    def max_phil(self, X: Philosopher) -> BoolRef:
        return self.le(self.phil_id(X), self.phil_id(self.max))

    @axiom
    def unique_phil_ids(self, X: Philosopher, Y: Philosopher) -> BoolRef:
        return Implies(self.phil_id(X) == self.phil_id(Y), X == Y)

    @axiom
    def unique_chop_ids(self, X: Chopstick, Y: Chopstick) -> BoolRef:
        return Implies(self.chop_id(X) == self.chop_id(Y), X == Y)

    @axiom
    def le_axioms(self, A: Id, B: Id, C: Id) -> BoolRef:
        return And(
            Implies(And(self.le(A, B), self.le(B, A)), A == B),
            Implies(And(self.le(A, B), self.le(B, C)), self.le(A, C)),
            Or(self.le(A, B), self.le(B, A)),
        )

    @axiom
    def phil_chop_has_same_id(self, phil: Philosopher) -> BoolRef:
        return self.chop_id(self.phil_chop(phil)) == self.phil_id(phil)

    @axiom
    def right_def(self, phil: Philosopher, c: Chopstick) -> BoolRef:
        return self.right(phil, c) == (c == self.phil_chop(phil))

    @axiom
    def left_def(self, phil: Philosopher, c: Chopstick) -> BoolRef:
        return self.left(phil, c) == (c == self.phil_chop(self.succ_phil(phil)))

    @axiom
    def at_least_2_philosophers(self, phil: Philosopher) -> BoolRef:
        p = Philosopher('p')
        return Exists([p], p != phil)

    @axiom
    def at_least_2_chopsticks(self, s: Chopstick) -> BoolRef:
        s2 = Chopstick('s2')
        return Exists([s2], s != s2)

    @axiom
    def succ_is_successor(self, X: Philosopher) -> BoolRef:
        return self.succ(X, self.succ_phil(X))

    def succ(self, X: Philosopher, Y: Philosopher) -> BoolRef:
        phil = Philosopher('phil')
        return And(
            X != Y,
            ForAll(phil, Or(self.btw(X,Y,phil), phil == X, phil == Y))
        )

    def taken(self, s: Chopstick) -> BoolRef:
        p = Philosopher('phil')
        return Exists(
            [p], self.holding(p,s)
        )

    def is_max(self, X: Philosopher) -> BoolRef:
        return X == self.max

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

    # A philosopher tries to move to grabbing state. If his assigned chopstick (the left one
    # for all philosophers but Max) is unavailable, the philosopher remains thinking

    """------------ NOTE: THE SOLVER WAS NOT ABLE TO PROVE DECREASION ON THIS TRANSITION------------"""
    # @transition
    # def thinking_to_thinking(self, phil: Philosopher) -> BoolRef:
    #     s = Chopstick("s")
    #     p = Philosopher("p")
    #
    #     return And(
    #         self.thinking(phil),
    #
    #         Exists([s], And(
    #             self.first_chopstick(phil, s),
    #             self.taken(s),
    #         )),
    #
    #         self.thinking.unchanged(),
    #         self.grabbing.unchanged(),
    #         self.eating.unchanged(),
    #         self.holding.unchanged(),
    #
    #         ForAll([p], self.scheduled(p) == (p == phil)),
    #     )




    # To move from thinking to grabbing, a philosopher takes a chopstick, passing from thinking state to grabbing state.
    # This transition requires:
    # - The philosoper to be thinking
    # - For every philosopher other than max, pick up the left chopstick
    # - Max should pick up the chopstick to his right
    # - A chopstick can be grabbed only if it is not held by anothe philosopher
    @transition
    def step_thinking_to_grabbing(self, phil: Philosopher) -> BoolRef:
        p = Philosopher('p')
        s = Chopstick('s')
        return And(
            self.thinking(phil), # Make sure phil is thinking
            # If phil is Max, make him pick up the chopstick to his right, otherwise to his left. also make sure
            # the stick is not alreadt taken.

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

    # A philosopher in the grabbing state already holds a chopstick and he waits for
    # the other chopstick to become available. This transition is for when the other chopstick is unavailable
    """------------ NOTE: THE SOLVER WAS NOT ABLE TO PROVE DECREASION ON THIS TRANSITION------------"""
    # @transition
    # def grabbing_to_grabbing(self, phil: Philosopher) -> BoolRef:
    #     s = Chopstick('s')
    #     p = Philosopher('p')
    #
    #     return And(
    #         self.grabbing(phil),
    #
    #         Exists([s], And(
    #             self.second_chopstick(phil, s),
    #             self.taken(s),
    #         )),
    #
    #         self.thinking.unchanged(),
    #         self.grabbing.unchanged(),
    #         self.eating.unchanged(),
    #         self.holding.unchanged(),
    #
    #         ForAll(p, self.scheduled(p) == (p == phil))
    #     )



    # A philosopher moves from the grabbing state to the eating state if these conditions hold:
    # - phil is in the grabbing state
    # - The other chopstick is available
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


    # Every philosopher that finishes eating goes back to thinking immediatly.
    # He also releases both his chopsticks
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


    @invariant
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