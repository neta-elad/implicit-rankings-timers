from z3 import *
from ts import *

def ghosh():

    #Ghosh's 4-state self-stabilization protocol
    #Sukumar Ghosh. 1993. An alternative solution to a problem on self-stabilization. 
    #ACM Trans. Program. Lang. Syst. 15, 4 (Sept. 1993), 735–742. https://doi.org/10.1145/155183.155228

    #To prove the properties of this protocol we make an abstraction that simplifies
    #the quantifier structure, we prove a few simple safety properties on the concrete system
    #and then assume them in the abstract system.

    print('ghosh')

    Node = DeclareSort('Node')
    sorts = [Node]

    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)

    constant_sym = { 'skd' : Node,
                     'top' : Node,
                     'bot' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node]}
    function_sym = {'next' : [Node,Node],
                    'prev' : [Node,Node],
                     'a' : [Node,BitVecSort(2)] }
    
    def init(sym):
        return And(
            Or(sym['a'](sym['bot'])==1,sym['a'](sym['bot'])==3),
            Or(sym['a'](sym['top'])==2,sym['a'](sym['top'])==4),
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

    def holds_2_or_4(sym,x):
        return Or(sym['a'](x)==2,sym['a'](x)==4)
    
    def induction_axiom(sym):
        return Implies(
            Exists(X,holds_2_or_4(sym,X)),
            Exists(X,And(holds_2_or_4(sym,X),
                         ForAll(Y,Implies(And(sym['leq_node'](Y,X),Y!=X),Not(holds_2_or_4(sym,Y))))))
        )
    
    def axiom(sym):
        return And(axiom_leq_node(sym),
                   induction_axiom(sym))
    
    def priv_above(sym,i):
        return And(sym['a'](i)+1==sym['a'](sym['next'](i)),i!=sym['top'])
            
    def priv_below(sym,i):
        return And(sym['a'](i)+1==sym['a'](sym['prev'](i)),i!=sym['bot'])
    
    def priv_bot(sym,i):
        return priv_above(sym,i)

    def priv_top(sym,i):
        return priv_below(sym,i)

    def priv_normal(sym,i):
        return Or(
            priv_above(sym,i),
            priv_below(sym,i)
        )

    def priv(sym,i):
        return Or(
            And(i==sym['bot'],priv_bot(sym,i)),
            And(i==sym['top'],priv_top(sym,i)),
            And(i!=sym['bot'],i!=sym['top'],priv_normal(sym,i))            
        )
    
    def move_bot_top(sym1,sym2,i):
        return And(
            sym2['a'](i)==sym1['a'](i)+2,
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )
    
    def move_normal(sym1,sym2,i):
        return And(
            sym2['a'](i)==sym1['a'](i)+1,
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )
    
    def move(sym1,sym2,i):
        return If(Or(i==sym1['bot'],i==sym1['top']),
                  move_bot_top(sym1,sym2,i),
                  move_normal(sym1,sym2,i))
    
    def move_idle(sym1,sym2,i):
        return ForAll(X,sym2['a'](X)==sym1['a'](X))

    param_wakeup = {'n' : Node}
    def tr_wakeup(sym1,sym2,param):
        n = param['n']
        return And(
        sym1['skd']==n,
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        Or(
            If(priv(sym1,n),
               move(sym1,sym2,n),
               move_idle(sym1,sym2,n))
        ))
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    #ts.bounded_check([lambda sym: priv(sym,sym['skd']),true])

    def no_deadlock(sym):
        return Exists(X,priv(sym,X))

    def inv(sym):
        return And(no_deadlock(sym),init(sym))

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(priv(sym,X),priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))

    ts.check_inductiveness(inv)
    ts.check_tr_maintains_inv(stable) #stability is inductive on its own

   
ghosh()