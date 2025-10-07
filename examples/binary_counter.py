from prelude import *

# @status - done


class Index(Finite): ...


class BinaryCounter(TransitionSystem):
    # Immutable constants and relations
    max: Immutable[Index]
    lt: Immutable[Rel[Index, Index]]

    # Mutable state
    ptr: Index
    a: Rel[Index]  # a(i) == True means bit i is 1

    @axiom
    def order_axioms(self, X: Index, Y: Index, Z: Index) -> BoolRef:
        return And(
            Implies(And(self.lt(X, Y), self.lt(Y, X)), false),
            Implies(And(self.lt(X, Y), self.lt(Y, Z)), self.lt(X, Z)),
            Or(self.lt(X, Y), self.lt(Y, X), X == Y),
            Or(self.lt(X, self.max), X == self.max),
        )

    def succ(self, smaller: Index, bigger: Index) -> BoolRef:
        Z = Index("Z")
        return And(
            self.lt(smaller, bigger),
            ForAll(
                Z, Implies(self.lt(smaller, Z), Or(Z == bigger, self.lt(bigger, Z)))
            ),
        )

    @init
    def initial(self, I: Index) -> BoolRef:
        return And(
            self.a(I) == True,
            self.ptr == self.max,
        )

    @transition
    def decrease(self) -> BoolRef:
        # If current bit at ptr is 0, flip it to 1 and move ptr one step down.
        # Otherwise, flip it to 0 and reset ptr to max.
        return And(
            If(
                Not(self.a(self.ptr)),
                And(
                    self.a.update({(self.ptr,): true}),
                    self.succ(self.next.ptr, self.ptr),
                ),
                And(
                    self.a.update({(self.ptr,): false}),
                    self.next.ptr == self.max,
                ),
            ),
        )


class BinaryCounterProp(Prop[BinaryCounter]):
    def prop(self) -> BoolRef:
        return false


class BinaryCounterProof(Proof[BinaryCounter], prop=BinaryCounterProp):
    def position_of_ptr(self) -> Rank:
        return PosInOrderRank(self.sys.ptr, self.sys.lt)

    def x_was_last_1(self, i: Index) -> BoolRef:
        return And(self.sys.a(i), Or(self.sys.lt(i, self.sys.ptr), i == self.sys.ptr))

    def gt(self, i1: Index, i2: Index) -> BoolRef:
        return self.sys.lt(i2, i1)

    def ghost_array_lex(self) -> Rank:
        return DomainLexRank(BinRank(self.x_was_last_1), self.gt, None)

    def rank(self) -> Rank:
        return LexRank(self.ghost_array_lex(), self.position_of_ptr())


BinaryCounterProof().check()
