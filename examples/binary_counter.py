from prelude import *


class Index(Finite): ...


class BinaryCounter(TransitionSystem):
    # Immutable constants and relations
    max: Immutable[Index]
    le: Immutable[Rel[Index, Index]]

    # Mutable state
    ptr: Index
    a: Rel[Index]  # a(i) == True means bit i is 1

    @axiom
    def order_axioms(self, X: Index, Y: Index, Z: Index) -> BoolRef:
        return And(
            Implies(And(self.le(X, Y), self.le(Y, X)), X == Y),
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Or(self.le(X, Y), self.le(Y, X)),
            self.le(X, self.max),
        )

    def succ(self, smaller: Index, bigger: Index) -> BoolRef:
        Z = Index("Z")
        return And(
            smaller != bigger,
            self.le(smaller, bigger),
            ForAll(Z, Implies(self.le(smaller, Z), Or(Z == smaller, self.le(bigger, Z)))),
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
        I = Index("I")
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
        return False


class BinaryCounterProof(Proof[BinaryCounter], prop=BinaryCounterProp):
    # A minimal proof skeleton with a trivial rank; can be refined later.

    def dummy(self) -> BoolRef:
        return true

    def rank(self) -> Rank:
        return BinRank(self.dummy)


BinaryCounterProof().check()


