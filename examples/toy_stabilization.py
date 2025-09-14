from prelude import *


class Node(Finite): ...


class ToyStabilizationSystem(TransitionSystem):
    top: Immutable[Node]
    leq: Immutable[Rel[Node,Node]]
    next_node: Immutable[Fun[Node,Node]]
    
    token: Rel[Node]
    scheduled: Rel[Node]

    def succ_node(self,u: Node,v: Node) -> BoolRef:
        #ring successor
        W = Node('W')
        return Or(
            ForAll(W,And(self.leq(v,W),self.leq(W,u))),
            And(u!=v,
                self.leq(u,v),
                ForAll(W,Or(self.leq(v,W),self.leq(W,u))))
        )
    
    @axiom
    def axiom_leq_node(self, X: Node, Y: Node, Z: Node) -> BoolRef:
        return And(
            Implies(And(self.leq(X,Y),self.leq(Y,Z)),self.leq(X,Z)),
            Implies(And(self.leq(X,Y),self.leq(Y,X)),X==Y),
            Or(self.leq(X,Y),self.leq(Y,X)),
            self.leq(X,self.top),
            self.succ_node(X,self.next_node(X)),
        )
    
    @init
    def initial(self) -> BoolRef:
        N = Node('N')
        return Exists(N,self.token(N))
    
    @transition
    def wakeup(self, n: Node) -> BoolRef:
        N = Node('N')
        return And(
            ForAll(N,self.scheduled(N) == (N==n)),
            If(self.token(n),
               And(
                   self.token.update(
                       lambda old,new,M: new(M) == And(
                           Or(old(M),M==self.next_node(n)),M!=n
                       )
                   )
               ),
               And(
                   self.token.unchanged()
               )
            )
        )


class ToyStabilizationProperty(Prop[ToyStabilizationSystem]):
    # The property we want to prove -- if infinitely often a node with a token moves then eventually top moves
    def negated_prop(self) -> BoolRef:
        X = Node("X")
        return And(
            G(F(Implies(
                Exists(X,self.sys.token(X)),
                Implies(self.sys.scheduled(X),self.sys.token(X))
            ))),
            G(Not(self.sys.scheduled(self.sys.top)))
        )

class TrivialTerminationProof(
    Proof[ToyStabilizationSystem], prop=ToyStabilizationProperty
):
    @temporal_invariant
    def token_scheduling(self) -> BoolRef:
        X = Node("X")
        return G(F(Implies(
                Exists(X,self.sys.token(X)),
                Implies(self.sys.scheduled(X),self.sys.token(X))
            )))
    
    @temporal_invariant
    def top_unscheduled(self) -> BoolRef:
        return G(Not(self.sys.scheduled(self.sys.top)))

    def holds_token(self, N: Node) -> BoolRef:
        return self.sys.token(N)
    
    def j_counts_towards_i(self, i: Node, j:Node) -> BoolRef:
        return And(
            self.sys.token(i),
            self.sys.leq(i,j)
        )
    
    def binary_rank_ij(self,i:Node,j:Node) -> Rank:
        return BinRank(self.j_counts_towards_i(i,j))

    # hint should be j=i (not sure)
    def sum_over_j(self, i: Node) -> Rank:
        return DomainPointwiseRank(self.binary_rank_ij(i,j),j,None)

    # hint should be i = sched (not sure)
    def sum_over_i(self) -> Rank:
        return DomainPermutedRank(self.sum_over_j(),i,1,None)

    def scheduled(self, N:Node) -> BoolRef:
        return self.sys.scheduled(N)

    def scheduled_timer_rank(self) -> Rank:
        return self.timer_rank(self.scheduled, self.holds_token, None)

    def rank(self) -> Rank:
        return LexRank(
            self.sum_over_i(),
            self.scheduled_timer_rank()
        )


TrivialTerminationProof().check()
