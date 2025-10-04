from prelude import *



class Node(Finite): ...


class TestSystem(TransitionSystem):

    node1: Immutable[Node]
    node2: Immutable[Node]
    node3: Immutable[Node]
    token: Rel[Node]

    @init
    def initial(self) -> BoolRef:
        N = Node("N")
        return Exists(N, self.token(N))

    @transition
    def wakeup(self, n: Node, m:Node ) -> BoolRef:
        N = Node("N")
        return And(
            self.token(n),
            # self.token.update({(n,):false,(m,):true})
            self.token.unchanged()
        )


class TestProperty(Prop[TestSystem]):
    def prop(self) -> BoolRef:
        return F(self.sys.token(self.sys.node1)) 



class TestProof(
    Proof[TestSystem], prop=TestProperty
):

    def token_pred(self, i: Node) -> BoolRef:
        return self.sys.token(i)

    def binary_token(self) -> Rank:
        return BinRank(self.token_pred)

    def dom_perm_token(self) -> Rank:
        conserved_hints = [
            (
                [{"i": self.sys.node1}],
                [{"i": self.sys.node1}],
            )
        ]
        decrease_hints = [
            (
                [{"i": self.sys.node1}],
                [{"i": self.sys.node2}],
                {"i": self.sys.node3},
            )
        ]
        return DomainPermutedRank(
            self.binary_token(),
            ParamSpec(i=Node),
            1,
            None,
            conserved_hints,
            # decrease_hints
        )


    def rank(self) -> Rank:
        return self.dom_perm_token()

TestProof().check()