"""
# <>!
## Ticket protocol example
Running example from
"*Verifying First-Order Temporal Properties
of Infinite States Systems via Timers and Rankings*"
paper (Sec. 2),
a variant of Lamport's bakery algorithm.

From liveness to safety:
Padon, O., Hoenicke, J., Losa, G., Podelski, A., Sagiv, M., Shoham, S.: Reducing liveness to safety in first-order logic.
Proc. ACM Program. Lang. 2(POPL), 26:1–26:33 (2018). https://doi.org/10.1145/3158114
# </>
"""

# @status - done

# <>
# | We start by importing all symbols from the `prelude` module:
from prelude import *  # </>


# <>
# | ### Sorts
# | We declare the Thread and Ticket sorts of the system
# | (both of which might be infinite).
# | Instances of these classes
# | represent constants in the signature of the transition system,
# | or variables of the sort
# | (see [`Expr`](typed_z3.html#Expr)).
class Thread(Expr): ...


class Ticket(Expr): ...


# | ### The Transition System of the Protocol
# | The signature (constants, functions and relations) of the system
# | is defined by annotated fields in the class.
# | Constants are annotated by their sort,
# | functions and relations use the `Fun[...]` and `Rel[...]` annotations respectively.
# | Any symbol can be marked immutable by wrapping it with `Immutable[...]`.
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
    # </>

    # <>
    # | We define axioms as methods on the transition-system class,
    # | annotated by `@axiom`.
    # | The signature of the transition system is available through `self`.
    # | All parameters are implicitly universally quantified.
    @axiom
    def order_le(self, X: Ticket, Y: Ticket, Z: Ticket) -> BoolRef:
        return And(
            # transitive, antisymmetric and total, with zero as minimal
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Or(self.le(X, Y), self.le(Y, X)),
            self.le(self.zero, X),
        )  # </>

    # <>
    # | We define the initial state by methods annotated with `@init`.
    # | Parameters are universally quantified.
    # | The initial state is given by the conjunction of all `@init` methods.
    @init
    def initial(self, T: Thread, X: Ticket) -> BoolRef:
        return And(
            self.pc1(T),
            Not(self.pc2(T)),
            Not(self.pc3(T)),
            self.service == self.zero,
            self.next_ticket == self.zero,
            self.m(T, X) == (X == self.zero),
        )  # </>

    # <>
    # | Since the transition system is just a Python class,
    # | we can define helper methods that automatically have access
    # | to the signature.
    # | This helper method is used in several transitions (below).
    def succ(self, u: Ticket, v: Ticket) -> BoolRef:
        X = Ticket("X")
        return And(
            self.le(u, v),
            Not(u == v),
            ForAll(X, Implies(self.le(u, X), Or(self.le(v, X), X == u))),
        )  # </>

    # <>
    # | Transitions are defined with the `@transition` decorator.
    # | Parameters are implicitly existentially quantified.
    # | The double signature of the system is represented by two copies of the class:
    # | `self` (pre-state) and `self.next` (post-state).
    # | In their core, transitions are just formulas over the double signature,
    # | that relate the pre-state and the post-state.
    # | These formulas can be completely expressed using just `self` and `self.next`.
    # | However, we provide some syntactic sugar for common kinds of updates.
    # |
    # | Transition `step12`: a thread in pc1 takes a ticket and moves to pc2.
    # | This transition:
    # | - Requires the thread `t` to be in pc1 (initial state)
    # | - Assigns `next_ticket` as the thread's ticket in the `m` relation
    # | - Advances `next_ticket` to the next available ticket using `succ`
    # | - Updates the program counter: pc1 becomes false, pc2 becomes true
    # | - Includes a fairness constraint ensuring `t` is scheduled
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
        )  # </>

    # <>
    # | Transition `step22`: a thread waits in pc2 when its ticket is not ready.
    # | The thread remains in pc2, checking if its ticket `k` is ready to be serviced.
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
        )  # </>

    # <>
    # | Transition `step23`: a thread moves from pc2 to pc3 when its ticket is ready.
    # | This happens when the thread's ticket `k` is less than or equal to the current service.
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
        )  # </>

    # <>
    # | Transition `step31`: a thread completes service and returns to pc1.
    # | The service counter advances to the next ticket.
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
        )  # </>


# <>
# | ### Temporal Property
# | Once the system is defined, we can write temporal properties for it
# | by extending the `Prop` class.
# | The temporal property is given by the `prop` method.
# | Within the temporal property,
# | we can freely use the temporal operators `G` and `F`.
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
        )  # </>


# <>
# | ### Proof
# | The proof class defines invariants and a ranking function to prove the temporal property.
# | We use various types of invariants:
# | - `@system_invariant`: invariants over the original system (without timers)
# | - `@invariant`: invariants over the intersection system (with timers)
# | - `@temporal_invariant`: temporal invariants expressing properties about timers
# | We also use witnesses to provide existential witnesses for formulas.
class TicketProof(Proof[TicketSystem], prop=TicketProp):
    # <>
    # | We use a temporal witness to provide a witness thread that violates the property.
    # | This witness thread will be used throughout the proof.
    @temporal_witness
    def skolem_thread(self, T: Thread) -> BoolRef:
        return Not(
            G(
                Implies(
                    self.sys.pc2(T),
                    F(self.sys.pc3(T)),
                )
            )
        )  # </>

    # <>
    # | Temporal invariants and tracked formulas for the proof.
    @temporal_invariant
    @track
    def skolem_thread_scheduled_infinitely_often(self) -> BoolRef:
        return G(F(self.sys.scheduled(self.skolem_thread)))  # </>

    # <>
    # | System invariants: properties that hold over the original system.
    # | These establish basic correctness properties of the protocol.
    @system_invariant
    def pc_at_least_one(self, T: Thread) -> BoolRef:
        return Or(self.sys.pc1(T), self.sys.pc2(T), self.sys.pc3(T))

    @system_invariant
    def pc_at_most_one(self, T: Thread) -> BoolRef:
        return And(
            Or(Not(self.sys.pc1(T)), Not(self.sys.pc2(T))),
            Or(Not(self.sys.pc1(T)), Not(self.sys.pc3(T))),
            Or(Not(self.sys.pc2(T)), Not(self.sys.pc3(T))),
        )  # </>

    # <>
    # | Invariants over the intersection system: these can reference both the system state
    # | and timers. They establish relationships between the protocol state and the temporal
    # | properties we're tracking.
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
        return Exists(X, self.sys.m(self.skolem_thread, X))  # </>

    # <>
    # | Additional temporal invariants for the proof.
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
        )  # </>

    # <>
    # | Helper formulas used in the ranking function.
    def starved(self) -> BoolRef:
        return And(
            self.sys.pc2(self.skolem_thread),
            G(Not(self.sys.pc3(self.skolem_thread))),
        )  # </>

    # <>
    # | ### Ranking Function
    # | The ranking function is a lexicographic combination of multiple ranks.
    # | Each rank component handles a different aspect of the proof.
    # |
    # | `rk1`: Timer rank for the starved condition.
    def rk1(self) -> Rank:
        return self.timer_rank(
            self.starved(),
            None,
            None,
        )  # </>

    # <>
    # | `rk2`: Domain-pointwise rank over tickets between service and next_ticket.
    # | Uses a finite lemma to bound the number of such tickets.
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
        )  # </>

    # <>
    # | `rk3`: Binary rank checking if any thread is in pc3.
    def rk3_body(self) -> BoolRef:
        T = Thread("T")
        return Not(Exists(T, self.sys.pc3(T)))

    def rk3(self) -> Rank:
        return BinRank(self.rk3_body)  # </>

    # <>
    # | `rk4`: Conditional timer rank that tracks scheduling of non-pc1 threads.
    # | The condition ensures we only track threads that need service.
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
        )  # </>

    # <>
    # | The final ranking function combines all ranks lexicographically.
    # | The rank decreases when:
    # | - `rk1` decreases (timer for starvation decreases), or
    # | - `rk1` is conserved and rk2 decreases (tickets between service and next decrease), or
    # | - `rk1` and `rk2` are conserved and `rk3` decreases (no thread in `pc3`), or
    # | - `rk1`, `rk2`, and `rk3` are conserved and `rk4` decreases (scheduling timer decreases).
    def rank(self) -> Rank:
        return LexRank(self.rk1(), self.rk2(), self.rk3(), self.rk4())  # </>

    def l2s_ivy_file(self) -> str | None:
        return "ticket"


# <>
# | Finally, we run the proof check to verify all obligations.
TicketProof().check()  # </>
