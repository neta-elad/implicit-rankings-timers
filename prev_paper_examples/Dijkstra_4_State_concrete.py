from z3 import *
from ts import *

def dijkstra4state():

    #Dijkstra's 4-state self-stabilization protocol
    #Dijkstra, E.W.: Self-stabilizing systems in spite of distributed control. 
    #Commun. ACM 17(11), 643–644 (nov 1974), https://doi.org/10.1145/361179.361202

    #To prove the properties of this protocol we make an abstraction that simplifies
    #the quantifier structure, we prove a few simple safety properties on the concrete system
    #and then assume them in the abstract system.

    print('Dijkstra 4-state')

    Node = DeclareSort('Node')
    sorts = [Node]

    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)

    constant_sym = { 'skd' : Node,
                     'top' : Node,
                     'bot' : Node,
                     'node_h' : Node
                     }
    relation_sym = {'leq_node' : [Node,Node],
                    'x' : [Node],
                    'up' : [Node]               
    }
    function_sym = {'next' : [Node,Node],
                    'prev' : [Node,Node], }
    
    def init(sym):
        return And(
            sym['up'](sym['bot'])==True,
            sym['up'](sym['top'])==False,
        )

    def succ_node(sym,u,v):
        return Or(
        ForAll(W,And(sym['leq_node'](v,W),sym['leq_node'](W,u))),
        And(u!=v,
            sym['leq_node'](u,v),
            ForAll(W,Or(sym['leq_node'](v,W),sym['leq_node'](W,u))))
        )

    def axiom_leq_node(sym):
        return ForAll([X,Y,Z],And(
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,Z)),sym['leq_node'](X,Z)),
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),X==Y),
        Or(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),
        sym['leq_node'](sym['bot'],X),
        sym['leq_node'](X,sym['top']),
        succ_node(sym,sym['prev'](X),X),
        succ_node(sym,X,sym['next'](X)),
        ))
    
    #Some of our safety premises only hold in finite models, and so we use induction axioms to prove them
    #Our use of induction axioms is based on "Elad, N., Shoham, S.: Axe ’em: Eliminating spurious states with induction axioms."

    def induction_axiom(sym):
        return Implies(
            Exists(Y,sym['up'](Y)==False),
            Exists(Z,And(sym['up'](Z)==False,ForAll(Y,Implies(sym['up'](Y)==False,sym['leq_node'](Z,Y)))))
        )

    def axiom(sym):
        return And(axiom_leq_node(sym),
                   induction_axiom(sym)) 

    def priv_below(sym,i):
        return And(sym['x'](i) != sym['x'](sym['prev'](i)),i!=sym['bot'])

    def move_below_normal(sym1,sym2,i):
        return And(
            sym2['x'](i)==Not(sym1['x'](i)),
            sym2['up'](i)==True,
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_below_top(sym1,sym2,i):
        return And(
            sym2['x'](i)==Not(sym1['x'](i)),
            sym2['up'](i)==sym1['up'](i),
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_below(sym1,sym2,i):
        return If(i==sym1['top'],
            move_below_top(sym1,sym2,i),
            move_below_normal(sym1,sym2,i))
            
    def priv_above(sym,i):
        return And(sym['x'](i)==sym['x'](sym['next'](i)),sym['up'](i),Not(sym['up'](sym['next'](i))),i!=sym['top'])
    
    def move_above_normal(sym1,sym2,i):
        return And(
            sym2['x'](i)==sym1['x'](i),
            sym2['up'](i)==False,
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_above_bot(sym1,sym2,i):
        return And(
            sym2['x'](i)==Not(sym1['x'](i)),
            sym2['up'](i)==sym1['up'](i),
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_above(sym1,sym2,i):
        return If(i==sym1['bot'],
            move_above_bot(sym1,sym2,i),
            move_above_normal(sym1,sym2,i))
    
    def any_priv(sym,i):
        return Or(priv_above(sym,i),priv_below(sym,i))

    def move_idle(sym1,sym2,i):
        return And(
            ForAll(X,sym2['x'](X)==sym1['x'](X)),
            ForAll(X,sym2['up'](X)==sym1['up'](X)),
        ) 

    param_wakeup = {'n' : Node}
    def tr_wakeup(sym1,sym2,param):
        return And(
        sym1['skd']==param['n'],
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        sym2['node_h']==sym1['node_h'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        Or(
            And(priv_above(sym1,param['n']),move_above(sym1,sym2,param['n'])),
            And(priv_below(sym1,param['n']),move_below(sym1,sym2,param['n'])),
            And(Not(any_priv(sym1,param['n'])),move_idle(sym1,sym2,param['n'])),
        ))
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    def no_deadlock(sym):
        return Exists(X,any_priv(sym,X))

    def inv(sym):
        return And(no_deadlock(sym),init(sym))

    ts.check_inductiveness(inv)

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(any_priv(sym,X),any_priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))

    def inv_stable(sym):
        return And(stable(sym),init(sym))
    
    ts.check_tr_maintains_inv(inv_stable)


dijkstra4state()
