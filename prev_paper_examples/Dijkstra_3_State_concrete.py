from z3 import *
from ts import *

def dijsktra3state():

    #Dijkstra's 4-state self-stabilization protocol
    #Dijkstra, E.W.: Self-stabilizing systems in spite of distributed control. 
    #Commun. ACM 17(11), 643–644 (nov 1974), https://doi.org/10.1145/361179.361202

    #To prove the properties of this protocol we make an abstraction that simplifies
    #the quantifier structure, we prove a few simple safety properties on the concrete system
    #and then assume them in the abstract system.

    print('dijkstra3')

    Node = DeclareSort('Node')
    Value, (zero, one, two) = EnumSort('Value',('zero','one','two'))
    sorts = [Node]

    def plus1mod3(x):
        return If(x==zero,one,
                  If(x==one,two,
                     zero))
    def plus2mod3(x):
        return If(x==zero,two,
                  If(x==one,zero,
                     one))
    
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)

    constant_sym = { 'skd' : Node,
                     'top' : Node,
                     'bot' : Node,
                     'node_h' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node],
    }
    function_sym = {'next' : [Node,Node],
                    'prev' : [Node,Node],
                    'a' : [Node,Value] }
    
    def init(sym):
        return BoolVal(True)

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
    
    def axiom_3_machines(sym):
        return Exists(X,And(X!=sym['top'],X!=sym['bot']))

    def induction_axiom1(sym):
        #needed for deadlock freedom - there is a minimal node that holds a value different from bot
        return Implies(
            Exists(Y,sym['a'](Y)!=sym['a'](sym['bot'])),
            Exists(Z,And(sym['a'](Z)!=sym['a'](sym['bot']),ForAll(Y,Implies(sym['a'](Y)!=sym['a'](sym['bot']),sym['leq_node'](Z,Y)))))
        )
    
    def induction_axiom2(sym):
        #needed for stability - there is a minimal node that holds a[bot]+2
        return Implies(
            Exists(Y,sym['a'](Y)==plus2mod3(sym['a'](sym['bot']))),
            Exists(Z,And(sym['a'](Z)==plus2mod3(sym['a'](sym['bot'])),ForAll(Y,Implies(sym['a'](Y)==plus2mod3(sym['a'](sym['bot'])),sym['leq_node'](Z,Y)))))
        )
    
    def induction_axiom3(sym):
        #needed for fairness proof2 - there is a minimal node that holds != a[bot]+1
        return Implies(
            Exists(Y,And(Y!=sym['bot'],sym['a'](Y)!=plus1mod3(sym['a'](sym['bot'])))),
            Exists(Z,And(Z!=sym['bot'],sym['a'](Z)!=plus1mod3(sym['a'](sym['bot'])),ForAll(Y,Implies(And(Y!=sym['bot'],sym['a'](Y)!=plus1mod3(sym['a'](sym['bot']))),sym['leq_node'](Z,Y)))))
        )
        
    def axiom(sym):
        return And(axiom_leq_node(sym),
                   axiom_3_machines(sym),
                   induction_axiom1(sym),
                   induction_axiom2(sym),
                   induction_axiom3(sym),
                   ) 

    def priv_above(sym,i):
        return And(plus1mod3(sym['a'](i))==sym['a'](sym['next'](i)),i!=sym['top'])
            
    def priv_below(sym,i):
        return And(plus1mod3(sym['a'](i))==sym['a'](sym['prev'](i)),i!=sym['bot'])
                         
    def priv_bot(sym,i):
        return priv_above(sym,i)
    
    def move_bot(sym1,sym2,i): 
        return And(
            plus2mod3(sym1['a'](i))==sym2['a'](i),
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )

    def priv_normal(sym,i):
        return Or(
            priv_above(sym,i),
            priv_below(sym,i)
        )
    
    def move_normal(sym1,sym2,i):
        return And(
            plus1mod3(sym1['a'](i))==sym2['a'](i),
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )
    
    def priv_top(sym,i):
        return And(
            sym['a'](sym['prev'](i))==sym['a'](sym['bot']),
            sym['a'](i)!=plus1mod3(sym['a'](sym['bot'])),
        )
    
    def move_top(sym1,sym2,i):
        return And(
            plus1mod3(sym1['a'](sym1['bot']))==sym2['a'](i),
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )
    
    def priv(sym,i):
        return Or(
            And(i==sym['bot'],priv_bot(sym,i)),
            And(i==sym['top'],priv_top(sym,i)),
            And(i!=sym['bot'],i!=sym['top'],priv_normal(sym,i)),
        )
    
    def move(sym1,sym2,i):
        return Or(
            And(i==sym1['bot'],move_bot(sym1,sym2,i)),
            And(i==sym1['top'],move_top(sym1,sym2,i)),
            And(i!=sym1['bot'],i!=sym1['top'],move_normal(sym1,sym2,i)),
        )

    def move_idle(sym1,sym2,i):
        return ForAll(X,sym2['a'](X)==sym1['a'](X))

    param_wakeup = {'n' : Node}
    def tr_wakeup(sym1,sym2,param):
        return And(
        sym2['skd']==param['n'],
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        sym2['node_h']==sym1['node_h'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        If(priv(sym1,param['n']),
           move(sym1,sym2,param['n']),
           move_idle(sym1,sym2,param['n'])
           )    
        )
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    #ts.bounded_check([true,true])

    def no_deadlock(sym):
        return Exists(X,priv(sym,X))
    
    #ts.check_inductiveness(no_deadlock) #works with ind. axiom

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(priv(sym,X),priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))
    
    #ts.check_tr_maintains_inv(stable) #takes a super long time    

    
    #these are axioms we add to the abstract system, you can check that these
    #follow from the axioms here in the concrete system.
    def case10_axiom(sym):
        return Implies(
            And(plus1mod3(sym['a'](sym['top']))==sym['a'](sym['bot']),
                plus1mod3(sym['a'](sym['top']))==sym['a'](sym['prev'](sym['top']))),
            Or(stable(sym),
               Exists(X,And(
                   X!=sym['top'],
                   Not(succ_node(sym,X,sym['top'])),
                   sym['a'](X)!=sym['a'](sym['next'](X))
                   )))
        )

    def stability_bot_axiom(sym):
        return Implies(
            And(stable(sym),priv(sym,sym['bot'])),
            ForAll(X,Implies(And(X!=sym['bot'],X!=sym['top']),
                             sym['a'](X)==plus1mod3(sym['a'](sym['bot'])) ))
        )
    
    def stability_prev_top_axiom(sym):
        return Implies(
            And(stable(sym),priv_above(sym,sym['prev'](sym['top']))),
            ForAll(X,Implies(X!=sym['top'],
                             sym['a'](X)==sym['a'](sym['bot'])))
        )
    
    
dijsktra3state()