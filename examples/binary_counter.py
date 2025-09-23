from prelude import *


class Index(Finite): ...


class BinaryCounter(TransitionSystem):
    # Immutable constants and relations
    max: Immutable[Index]
    le: Immutable[Rel[Index, Index]]
    le_reversed : Immutable[Rel[Index,Index]]

    # Mutable state
    ptr: Index
    a: Rel[Index]  # a(i) == True means bit i is 1

    @axiom
    def order_axioms(self, X: Index, Y: Index, Z: Index) -> BoolRef:
        return And(
            Implies(And(self.le(X, Y), self.le(Y, X)), false),
            Implies(And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            Or(self.le(X, Y), self.le(Y, X),X==Y),
            Or(self.le(X, self.max),X==self.max),
            self.le_reversed(X,Y) == self.le(Y,X)
        )

    def succ(self, smaller: Index, bigger: Index) -> BoolRef:
        Z = Index("Z")
        return And(
            self.le(smaller, bigger),
            ForAll(
                Z, Implies(self.le(smaller, Z), Or(Z == bigger, self.le(bigger, Z)))
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
        return false


class BinaryCounterProof(Proof[BinaryCounter], prop=BinaryCounterProp):

    def position_of_ptr(self) -> Rank:
        def le_rel(self: BinaryCounterProof) -> Rel[Index, Index]:
            return self.sys.le
        
        def ptr_term(self: BinaryCounterProof) -> Index:
            return self.sys.ptr
            
        return PosInOrderRank(ts_rel(le_rel), ts_term(ptr_term))
        
    def x_was_last_1(self,i:Index) -> BoolRef:
        return And(
            self.sys.a(i), 
            self.sys.le(i,self.sys.ptr)
        )

    def ghost_array_lex(self) -> Rank:
        def le_rel(self: BinaryCounterProof) -> Rel[Index, Index]:
            return self.sys.le

        return DomainLexRank(
            BinRank(
                self.x_was_last_1
            ),
            ts_rel(le_rel),
            ('i',Index),
            None
        )

    def rank(self) -> Rank:
        return LexRank(
            self.ghost_array_lex(),
            # self.position_of_ptr()
        )



BinaryCounterProof().check()
