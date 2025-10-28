
## Ticket protocol example
Running example from
"*Verifying First-Order Temporal Properties
of Infinite States Systems via Timers and Rankings*"
paper (Sec. 2),
a variant of Lamport's bakery algorithm.

From liveness to safety:
Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., Shoham, S.: Reducing liveness to safety in first-order logic.
Proc. ACM Program. Lang. 2(POPL), 26:1–26:33 (2018). https://doi.org/10.1145/3158114

We start by importing all symbols from the `prelude` module:
```python
from prelude import *  
```

We declare the Thread and Ticket sorts of the system
(both of which might be infinite).
Instances of the class represent constants in the signature of the transition system,
or variables of the sort.
```python
class Thread(Expr): ...


class Ticket(Expr): ...  
```

The transition system of the protocol.
The signature (constants, functions and relations) of the system
is defined by annotated fields in the class.
Constants are annotated by their sort,
functions and relations use the `Fun[...]` and `Rel[...]` annotations respectively.
Any symbol can be marked immutable by wrapping it with `Immutable[...]`.
```python
class TicketSystem(TransitionSystem):
    zero: Immutable[Ticket]  # Immutable, first ticket
    service: Ticket  # Mutable, currently serviced ticket
    next_ticket: Ticket  # Mutable, next available ticket

    le: Immutable[Rel[Ticket, Ticket]]
    # An immutable relation, representing the total order over tickets.
    # Its semantics are defined in the `order_le` axiom below.

    # Mutable relations:
    pc1: Rel[Thread]
    pc2: Rel[Thread]
    pc3: Rel[Thread]
    m: Rel[Thread, Ticket]
    scheduled: Rel[Thread]
    
```

We define axioms as methods on the transition-system class,
annotated by `@axiom`.
The signature of the transition system is available through `self`.
All parameters are implicitly universally quantified.
```python
    @axiom
    def order_le(self, X: Ticket, Y: Ticket, Z: Ticket) -> BoolRef:
        return And(
            # transitive, antisymmetric and total, with zero as minimal
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Or(self.le(X, Y), self.le(Y, X)),
            self.le(self.zero, X),
        )  
```

We define the initial state by methods annotated with `@init`.
Parameters are universally quantified.
The initial state is given by the conjunction of all `@init` methods.
```python
    @init
    def initial(self, T: Thread, X: Ticket) -> BoolRef:
        return And(
            self.pc1(T),
            Not(self.pc2(T)),
            Not(self.pc3(T)),
            self.service == self.zero,
            self.next_ticket == self.zero,
            self.m(T, X) == (X == self.zero),
        )  
```

Since the transition system is just a Python class,
we can define helper methods that automatically have access
to the signature.
This helper method is used in several transitions (below).
```python
    def succ(self, u: Ticket, v: Ticket) -> BoolRef:
        X = Ticket("X")
        return And(
            self.le(u, v),
            Not(u == v),
            ForAll(X, Implies(self.le(u, X), Or(self.le(v, X), X == u))),
        )  
```

Transitions are defined with the `@transition` decorator.
Parameters are implicitly existentially quantified.
The double signature of the system is represented by two copies of the class:
`self` (pre-state) and `self.next` (post-state).
In their core, transitions are just formulas over the double signature,
that relate the pre-state and the post-state.
These formulas can be completely expressed using just `self` and `self.next`.
However, we provide some syntactic sugar for common kinds of updates.
```python
    @transition
    def step12(self, t: Thread) -> BoolRef:
        T = Thread("T")
        X = Ticket("X")
        return And(
            # guard
            self.pc1(t),
            # updates
            # A universal quantifier that relates pre-state `self.m`
            # with post-state `self.next.m`,
            # using the pre-state `self.next_ticket`.
            ForAll(
                [T, X],
                self.next.m(T, X) == If(T == t, X == self.next_ticket, self.m(T, X)),
            ),
            # A helper method to change a function or relation
            # for specific elements:
            self.pc1.update({(t,): false}),
            self.pc2.update({(t,): true}),
            # A helper method to make pre- and post-state identical:
            self.pc3.unchanged(),
            self.service.unchanged(),
            # Using the helper method `self.succ` to explicitly relate
            # pre-state `self.next_ticket` and post-state `self.next.next_ticket`
            self.succ(self.next_ticket, self.next.next_ticket),
            # fairness
            ForAll(T, self.scheduled(T) == (T == t)),
        )

    @transition
    def step22(self, t: Thread, k: Ticket) -> BoolRef:
        T = Thread("T")
        return And(
            # guard
            self.pc2(t),
            self.m(t, k),
            Not(self.le(k, self.service)),
            # updates
            self.pc1.unchanged(),
            self.pc2.unchanged(),
            self.pc3.unchanged(),
            self.m.unchanged(),
            self.service.unchanged(),
            self.next_ticket.unchanged(),
            # fairness
            ForAll(T, self.scheduled(T) == (T == t)),
        )

    @transition
    def step23(self, t: Thread, k: Ticket) -> BoolRef:
        T = Thread("T")
        return And(
            # guard
            self.pc2(t),
            self.m(t, k),
            self.le(k, self.service),
            # updates
            self.pc1.unchanged(),
            self.pc2.update({(t,): false}),
            self.pc3.update({(t,): true}),
            self.m.unchanged(),
            self.service.unchanged(),
            self.next_ticket.unchanged(),
            # fairness
            ForAll(T, self.scheduled(T) == (T == t)),
        )

    @transition
    def step31(self, t: Thread) -> BoolRef:
        T = Thread("T")
        return And(
            # guard
            self.pc3(t),
            # updates
            self.pc1.update({(t,): true}),
            self.pc2.unchanged(),
            self.pc3.update({(t,): false}),
            self.m.unchanged(),
            self.succ(self.service, self.next.service),
            self.next_ticket.unchanged(),
            # fairness
            ForAll(T, self.scheduled(T) == (T == t)),
        )  
```

Once the system is defined, we can write temporal properties for it
by extending the `Prop` class.
The temporal property is given by the `prop` method.
Within the temporal property,
we can freely use the temporal operators `G` and `F`.
```python
class TicketProp(Prop[TicketSystem]):
    def prop(self) -> BoolRef:
        T = Thread("T")
        return Implies(
            ForAll(T, G(F(self.sys.scheduled(T)))),
            ForAll(
                T,
                G(
                    Implies(
                        self.sys.pc2(T),
                        F(self.sys.pc3(T)),
                    )
                ),
            ),
        )


class TicketProof(Proof[TicketSystem], prop=TicketProp):
    @temporal_witness
    def skolem_thread(self, T: Thread) -> BoolRef:
        return Not(
            G(
                Implies(
                    self.sys.pc2(T),
                    F(self.sys.pc3(T)),
                )
            )
        )

    @temporal_invariant
    @track
    def skolem_thread_scheduled_infinitely_often(self) -> BoolRef:
        return G(F(self.sys.scheduled(self.skolem_thread)))

    @system_invariant
    def pc_at_least_one(self, T: Thread) -> BoolRef:
        return Or(self.sys.pc1(T), self.sys.pc2(T), self.sys.pc3(T))

    @system_invariant
    def pc_at_most_one(self, T: Thread) -> BoolRef:
        return And(
            Or(Not(self.sys.pc1(T)), Not(self.sys.pc2(T))),
            Or(Not(self.sys.pc1(T)), Not(self.sys.pc3(T))),
            Or(Not(self.sys.pc2(T)), Not(self.sys.pc3(T))),
        )

    @invariant
    def one_ticket_per_thread(self, T: Thread, K1: Ticket, K2: Ticket) -> BoolRef:
        return Implies(And(self.sys.m(T, K1), self.sys.m(T, K2)), K1 == K2)

    @invariant
    def safety(self, T1: Thread, T2: Thread) -> BoolRef:
        return Implies(And(self.sys.pc3(T1), self.sys.pc3(T2)), T1 == T2)

    @invariant
    def next_ticket_zero_then_all_zero(self, T: Thread) -> BoolRef:
        return Implies(
            self.sys.next_ticket == self.sys.zero, self.sys.m(T, self.sys.zero)
        )

    @invariant
    def next_ticket_maximal(self, T: Thread, K: Ticket) -> BoolRef:
        return Implies(
            And(self.sys.next_ticket != self.sys.zero, self.sys.m(T, K)),
            Not(self.sys.le(self.sys.next_ticket, K)),
        )

    @invariant
    def pc2_or_pc3_next_ticket_nonzero(self, T: Thread) -> BoolRef:
        return Implies(
            Or(self.sys.pc2(T), self.sys.pc3(T)), self.sys.next_ticket != self.sys.zero
        )

    @invariant
    def one_nonzero_ticket_per_thread(
        self, T1: Thread, T2: Thread, K: Ticket
    ) -> BoolRef:
        return Implies(
            And(self.sys.m(T1, K), self.sys.m(T2, K), K != self.sys.zero), T1 == T2
        )

    @invariant
    def pc2_ticket_larger_than_service(self, T: Thread, K: Ticket) -> BoolRef:
        return Implies(
            And(self.sys.pc2(T), self.sys.m(T, K)), self.sys.le(self.sys.service, K)
        )

    @invariant
    def pc3_then_service(self, T: Thread) -> BoolRef:
        return Implies(self.sys.pc3(T), self.sys.m(T, self.sys.service))

    @invariant
    def service_before_next(self) -> BoolRef:
        return self.sys.le(self.sys.service, self.sys.next_ticket)

    @invariant
    def unique_nonzero_tickets_for_non_pc1(self, T1: Thread, T2: Thread) -> BoolRef:
        return Not(
            And(
                Not(self.sys.pc1(T1)),
                Not(self.sys.pc1(T2)),
                self.sys.m(T1, self.sys.zero),
                self.sys.m(T2, self.sys.zero),
                T1 != T2,
            )
        )

    @invariant
    def nonzero_pc1_ticket_already_serviced(self, T: Thread, K: Ticket) -> BoolRef:
        return Implies(
            And(self.sys.pc1(T), self.sys.m(T, K), K != self.sys.zero),
            Not(self.sys.le(self.sys.service, K)),
        )

    @invariant
    def ticket_between_service_and_next_not_pc1(self, T: Thread, K: Ticket) -> BoolRef:
        return Implies(
            And(
                Not(self.sys.le(self.sys.next_ticket, K)),
                self.sys.le(self.sys.service, K),
            ),
            Exists(T, And(self.sys.m(T, K), Not(self.sys.pc1(T)))),
        )

    @invariant
    def skolem_has_ticket(self) -> BoolRef:
        X = Ticket("X")
        return Exists(X, self.sys.m(self.skolem_thread, X))

    @temporal_invariant
    def globally_eventually_scheduled(self, T: Thread) -> BoolRef:
        return G(F(self.sys.scheduled(T)))

    @temporal_invariant
    @track
    def timer_invariant(self, K: Ticket) -> BoolRef:
        return Or(
            F(
                self.starved(),
            ),
            And(
                G(Not(self.sys.pc3(self.skolem_thread))),
                self.sys.pc2(self.skolem_thread),
                Implies(
                    self.sys.m(self.skolem_thread, K),
                    self.sys.le(self.sys.service, K),
                ),
            ),
        )

    def starved(self) -> BoolRef:
        return And(
            self.sys.pc2(self.skolem_thread),
            G(Not(self.sys.pc3(self.skolem_thread))),
        )

    def rk1(self) -> Rank:
        return self.timer_rank(
            self.starved(),
            None,
            None,
        )

    def rk2_body(self, k: Ticket) -> BoolRef:
        X = Ticket("X")
        return And(
            self.sys.le(self.sys.service, k),
            Exists(X, And(self.sys.m(self.skolem_thread, X), self.sys.le(k, X))),
        )

    def rk2_finite_lemma(self, k: Ticket) -> BoolRef:
        return self.sys.le(k, self.sys.next_ticket)

    def rk2(self) -> Rank:
        return DomainPointwiseRank.close(
            BinRank(self.rk2_body),
            FiniteLemma(self.rk2_finite_lemma),
        )

    def rk3_body(self) -> BoolRef:
        T = Thread("T")
        return Not(Exists(T, self.sys.pc3(T)))

    def rk3(self) -> Rank:
        return BinRank(self.rk3_body)

    def scheduled(self, T: Thread) -> BoolRef:
        return self.sys.scheduled(T)

    def non_pc1_serviced(self, T: Thread) -> BoolRef:
        return And(self.sys.m(T, self.sys.service), Not(self.sys.pc1(T)))

    def rk4_finite_lemma(self, T: Thread) -> BoolRef:
        return Not(self.sys.pc1(T))

    def rk4(self) -> Rank:
        return self.timer_rank(
            self.scheduled,
            self.non_pc1_serviced,
            FiniteLemma(self.rk4_finite_lemma),
        )

    def rank(self) -> Rank:
        return LexRank(self.rk1(), self.rk2(), self.rk3(), self.rk4())


TicketProof().check()
```
