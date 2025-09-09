from prelude import *

#Classic mutex in a ring - a token moves around a ring, allowing the holder to enter the critical section
#taken from Fang, Y., Piterman, N., Pnueli, A. and Zuck, L., 2004, January.
#Liveness with invisible ranking. 
#In International Workshop on Verification, Model Checking, and Abstract Interpretation (pp. 223-238). Berlin, Heidelberg: Springer Berlin Heidelberg.

class Node(Finite): ...


Loc, (waiting,critical,neutral) = EnumSort('Loc',('waiting','critical','neutral'))



class MutexRing(TransitionSystem):
    #immutables
    leader: Immutable[Node]
    btw: Immutable[Rel[Node,Node,Node]]
    skolem_node : Immutable[Node]

    #mutables
    token : Rel[Node]
    node_loc : Fun[Node,Loc]
    scheduled: Rel[Node]

    @axiom
    def btw_axioms(self, X: Node, Y: Node, Z: Node,W:Node) -> BoolRef:
        return And(
            #characterising axioms of the btw relation
            Implies(And(self.btw(W,X,Y),self.btw(W,Y,Z)),self.btw(W,X,Z)),
            Implies(self.btw(W,X,Y),Not(self.btw(W,Y,X))),
            Or(self.btw(W,X,Y),self.btw(W,Y,X),W==X,W==Y,X==Y),
            Implies(self.btw(X,Y,Z),self.btw(Y,Z,X)),
        )

    @init
    def initial(self, X: Node) -> BoolRef:
        return And(
            self.token(X) == (X==self.leader),
            self.node_loc(X) == neutral,
        )

    def succ(self, n: Node, s: Node) -> BoolRef:
        Z = Node('Z')
        return And(
            n!=s,ForAll(Z,Or(self.btw(n,s,Z),Z==n,Z==s)),
        )

    @transition
    def wakeup(self, n: Node, s: Node) -> BoolRef:
        N = Node('N')
        return And(
            # guard
            self.succ(n,s),
            # fairness 
            ForAll(N,self.scheduled(N) == (N==n)),
            # updates
            If(self.token(n),
                If(self.node_loc(n)==neutral,
                    And(
                        self.token.update(lambda old,new,N: new(N) == Or(And(old(N), N!=n),N==s)),
                        self.node_loc.unchanged()
                    ),
                    If(self.node_loc(n)==waiting,
                        And(
                            self.token.unchanged(),
                            self.node_loc.update(lambda old,new,N: new(N) == If(N==n,critical,old(N)))
                        )),
                        # else loc = critical
                        And(
                            self.token.unchanged(),
                            self.node_loc.update(lambda old,new,N: new(N) == If(N==n,neutral,old(N)))
                        )),
                    # else - no token 
                    And(self.token.unchanged(),
                        If(self.node_loc(n)==neutral,
                            self.node_loc.update(lambda old,new,N: new(N) == If(N==n,waiting,old(N))),
                            self.node.unchanged()
                        )
                    )
            )
        )

class MutexRingProp(Prop[MutexRing]):
    def negated_prop(self) -> BoolRef:
        N = Node("N")
        return And(
            ForAll(N, G(F(self.sys.scheduled(N)))),
            F(
                And(
                    self.sys.waiting(self.sys.skolem_node),
                    G(Not(self.sys.critical(self.sys.skolem_node))),
                )
            ),
        )


class MutexRingProof(Proof[MutexRing], prop=MutexRingProp):
    # needed?
    @invariant
    def unique_token(self,X:Node,Y:Node) -> BoolRef:
        return Implies(And(self.sys.token(X),self.sys.token(Y)),X==Y)

    @invariant
    def exists_token(self) -> BoolRef:
        X = Node('X')
        return Exists(X, self.sys.token(X))
    
    @temporal_invariant
    def globally_eventually_scheduled(self, N: Node) -> BoolRef:
        return G(F(self.sys.scheduled(N)))

    def scheduled(self, N:Node) -> BoolRef:
        return self.sys.scheduled(N)
    
    def holds_token(self, N:Node) -> BoolRef:
        return self.sys.token(N)

    ## add system ranks

    def scheduling_rank(self) -> Rank:
        self.timer_rank(
            self.scheduled,
            self.holds_token,
            None
        )

    def rank(self) -> Rank:
        return LexRank(
            self.scheduling_rank()
        )

MutexRingProof().check()

# rank in prev paper. 
# n_node = {'n':Node}
# pred_waiting_token = lambda sym,param: And(sym['node_loc'](n)==waiting,sym['token'](n))
# delta0_free = BinaryFreeRank(pred_waiting_token,n_node)
# pred_critical_token = lambda sym,param: And(sym['node_loc'](n)==critical,sym['token'](n))
# delta1_free = BinaryFreeRank(pred_critical_token,n_node)
# pred_neutral_token = lambda sym,param: And(sym['node_loc'](n)==neutral,sym['token'](n))
# delta2_free = BinaryFreeRank(pred_neutral_token,n_node)
# delta_free = LexFreeRank([delta0_free,delta1_free,delta2_free],n_node)

# less_btw_her_last = lambda sym,param1,param2: Or(self.btw(sym['node_her1'],param1['n'],param2['n']),And(param2['n']==sym['node_her1'],param1['n']!=sym['node_her1'])) 

# rank_lex = ParLexFreeRank(delta_free,n_node,less_btw_her_last,{})

# rank_lex.print_reduced(ts)

# rho = lambda sym: And(Exists(X,sym['token'](X)),
#                             inv(sym) #safety invariant - needed for proof with rank_lin
#                             )
# phi = lambda sym: And(rho(sym),
#                         p(sym),
#                         Not(q(sym))) 
# psi = lambda sym,param: sym['token'](n)

