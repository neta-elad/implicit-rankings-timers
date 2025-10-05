from prelude import *


class Element(Expr): ...


class Example(TransitionSystem):
    p: Rel[Element, Element]
    c: Element

    @init
    def initial(self) -> BoolRef:
        return true

    @transition
    def do_nothing(self) -> BoolRef:
        return self.p.unchanged()


class ExampleProp(Prop[Example]):
    def prop(self) -> BoolRef:
        X = Element("X")
        Y = Element("Y")
        return Implies(
            ForAll([X, Y], G(self.sys.p(X, Y))), ForAll(Y, G(self.sys.p(self.sys.c, Y)))
        )


class ExampleProof(Proof[Example], prop=ExampleProp):
    @temporal_invariant
    @track
    def p_c(self) -> BoolRef:
        Y = Element("Y")
        return ForAll(Y, G(self.sys.p(self.sys.c, Y)))

    @invariant
    def false_inv(self) -> BoolRef:
        return false

    def rank(self) -> Rank:
        return BinRank(true)  # unimportant


ExampleProof().check()
