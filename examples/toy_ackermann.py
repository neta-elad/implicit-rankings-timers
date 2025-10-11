from inspect import stack
from prelude import *
import temporal

# A simple program 
# n := *
# c[0,...,n-1] := *
# while(exists i. c[i] > 0): 
#   i := *
#   assume c[i] > 0
#   c[i] := c[i] - 1
#   c[i-1] := *
# Showing termination of this program requires a ranking to omega^omega


class Index(Expr): ...

class Value(Expr): ... 


class ToyAckermannSystem(TransitionSystem):
    # Immutable constants and relations
    zero_index: Immutable[Index]
    zero_value: Immutable[Value]
    lt_index: Immutable[WFRel[Index]]
    lt_value: Immutable[WFRel[Value]]

    # Mutable state variables
    c: Fun[Index,Value]
    n: Index
    n_done : Bool #increasing n until setting n_done_to_true

    @axiom
    def lt_index_axioms(self, X: Index, Y: Index, Z: Index) -> BoolRef:
        return And(
            Implies(And(self.lt_index(X, Y), self.lt_index(Y, Z)), self.lt_index(X, Z)),
            Implies(And(self.lt_index(X, Y), self.lt_index(Y, X)), false),
            Or(self.lt_index(X, Y), self.lt_index(Y, X), X == Y),
            Or(self.lt_index(self.zero_index, X), X == self.zero_index),
        )

    @axiom
    def lt_value_axioms(self, X: Value, Y: Value, Z: Value) -> BoolRef:
        return And(
            Implies(And(self.lt_value(X, Y), self.lt_value(Y, Z)), self.lt_value(X, Z)),
            Implies(And(self.lt_value(X, Y), self.lt_value(Y, X)), false),
            Or(self.lt_value(X, Y), self.lt_value(Y, X), X == Y),
            Or(self.lt_value(self.zero_value, X), X == self.zero_value),
        )

    def succ_index(self, n1: Index, n2: Index) -> BoolRef:
        Z = Index("Z")
        return And(
            self.lt_index(n1, n2),
            ForAll(Z, Implies(self.lt_index(n1, Z), Or(Z == n2, self.lt_index(n2, Z)))),
        )
    
    def succ_value(self, n1: Value, n2: Value) -> BoolRef:
        Z = Value("Z")
        return And(
            self.lt_value(n1, n2),
            ForAll(Z, Implies(self.lt_value(n1, Z), Or(Z == n2, self.lt_value(n2, Z)))),
        )

    @init
    def initial(self, X: Index) -> BoolRef:
        return And(
            self.c(X) == self.zero_value,
            self.n == self.zero_index,
            self.n_done == false
        )

    @transition
    def increase_n(self) -> BoolRef:
        return And(
            Not(self.n_done),
            self.succ_index(self.n,self.next.n),
            self.c.unchanged(),
            # n_done is updated arbitrarily
        )

    @transition
    def modify_c(self, i: Index, prev_i: Index) -> BoolRef:
        I = Index('I')
        return And(
            self.n_done,
            self.succ_index(prev_i,i),
            self.n.unchanged(),
            self.n_done.unchanged(),
            self.succ_value(self.next.c(i),self.c(i)),
            ForAll(I,Implies(
                And(I != i, I != prev_i),
                self.next.c(I) == self.c(I)
                # c(prev_i) is updated arbitrarily
            ))
        )


class ToyAckermannProp(Prop[ToyAckermannSystem]):
    # fairness: n is set to some finite value
    # property: termination (false)
    def prop(self) -> BoolRef:
        return Implies(F(self.sys.n_done),false)


class ToyAckermannProof(Proof[ToyAckermannSystem], prop=ToyAckermannProp):

    @temporal_invariant
    def eventually_n_done(self) -> BoolRef:
        return F(self.sys.n_done)

    def timer_n_done(self) -> Rank:
        return self.timer_rank(self.sys.n_done,None,None)

    @ts_term
    def value_of_i(self, i:Index) -> TSTerm:
        return self.sys.c(i)

    def pos_value_of_i(self) -> Rank:
        return PosInOrderRank(self.value_of_i,self.sys.lt_value)

    def lexicographic_rank(self) -> Rank:
        return DomainLexRank(
            self.pos_value_of_i(),
            self.sys.lt_index,
            None
        )

    def rank(self) -> Rank:
        return PointwiseRank(
            self.timer_n_done(),
            self.lexicographic_rank()
        )


ToyAckermannProof().check()
