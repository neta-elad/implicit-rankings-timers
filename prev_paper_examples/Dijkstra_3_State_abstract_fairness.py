from z3 import *
from ts import *

def dijsktra3():

    #This is the abstraction of Dijkstra 3-state concrete
    #In this file we prove the fairness property.
    #In the abstraction, instead of using next and prev to define the privileges we treat
    #the values of neighbors as new function symbols that are axiomitized to hold the correct values only for relevant  nodes.
    #Additionally we add as axioms some necessary properties
    #Different axioms are needed here from what was needed for stabilization, but same ranking as in Dijkstra 4-state fairness

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
                     'next_skd' : Node,
                     'prev_skd' : Node,
                     'prev_top' : Node, 
                     #'next_bot' : Node,
                     'top' : Node,
                     'bot' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node],
    }
    function_sym = {'a' : [Node,Value],
                    #instrumentation variables, recording the values for a for the previous and next nodes
                    'a_next' : [Node,Value], 
                    'a_prev' : [Node,Value]
        #'next' : [Node,Node],
        #'prev' : [Node,Node],
    }
    
    def init(sym):
        return z3.BoolVal(True)

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
        succ_node(sym,sym['skd'],sym['next_skd']),
        succ_node(sym,sym['prev_skd'],sym['skd']),

        #succ_node(sym,sym['prev_top'],sym['top']),
        #succ_node(sym,sym['bot'],sym['next_bot']),
        ))
    
    def axiom_3_machines(sym):
        return Exists(X,And(X!=sym['top'],X!=sym['bot']))

    def inst_correct_around_skd(sym):
        #we guarantee only that the values for a_next are correct for
        #skd, skd_prev, and that a_prev is correct for skd,  skd_next
        skd = sym['skd']
        next_skd = sym['next_skd']
        prev_skd = sym['prev_skd']
        top = sym['top']
        bot = sym['bot']
        return And(
            sym['a_next'](skd)==sym['a'](next_skd),
            sym['a_next'](prev_skd)==sym['a'](skd),
            sym['a_prev'](skd)==sym['a'](prev_skd),
            sym['a_prev'](next_skd)==sym['a'](skd),

            ##We may also assume the instrumentation is correct for top/bottom
            #I thought adding these would be helpful but doesnt seem so
            sym['a_next'](top) == sym['a'](bot),
            sym['a_prev'](bot) == sym['a'](top),
            #sym['a_next'](bot) == sym['a'](sym['next_bot']),
            sym['a_prev'](top) == sym['a'](sym['prev_top']),
            #sym['a_prev'](sym['next_bot']) == sym['a'](bot),
            sym['a_next'](sym['prev_top']) == sym['a'](top)
        )
    
    def update_instrumentation(sym1,sym2):
        skd = sym1['skd']
        prev_skd = sym1['prev_skd']
        next_skd = sym1['next_skd']
        return And(
            sym2['a_next'](skd)==sym2['a'](next_skd),
            sym2['a_next'](prev_skd)==sym2['a'](skd),
            ForAll(X,Implies(And(X!=skd,X!=prev_skd),sym2['a_next'](X)==sym1['a_next'](X))),
            sym2['a_prev'](skd)==sym2['a'](prev_skd),
            sym2['a_prev'](next_skd)==sym2['a'](skd),
            ForAll(X,Implies(And(X!=skd,X!=next_skd),sym2['a_prev'](X)==sym1['a_prev'](X))),
        )
    
    def case10_axiom(sym):
        return Implies(
            And(plus1mod3(sym['a'](sym['top']))==sym['a'](sym['bot']),
                plus1mod3(sym['a'](sym['top']))==sym['a_prev'](sym['top'])),
            Or(stable(sym),
               Exists(X,And(
                   X!=sym['top'],
                   Not(succ_node(sym,X,sym['top'])),
                   sym['a'](X)!=sym['a_next'](X)
                   )))
        )

    #these help capture some properties of the original system
    #that are otherwise lost in abstraction and are required
    #in order to show that stability
    def stability_abstraction_axioms(sym):
        return And(
            Implies(
                And(stable(sym),priv(sym,sym['bot'])),
                ForAll(X,Implies(And(X!=sym['bot'],X!=sym['top']),
                                sym['a'](X)==plus1mod3(sym['a'](sym['bot']))))),
            Implies(
                And(stable(sym),priv_above(sym,sym['prev_top'])),
                ForAll(X,Implies(X!=sym['top'],
                                sym['a'](X)==sym['a'](sym['bot'])))),
        )

    def abstraction_axioms(sym):
        #these are axioms we proved on the concrete model we can assume here
        return And(
            Exists(X,priv(sym,X)),
            inst_correct_around_skd(sym),
            case10_axiom(sym),
            stability_abstraction_axioms(sym)
        )

    def axiom(sym):
        return And(axiom_leq_node(sym),
                   axiom_3_machines(sym),
                   abstraction_axioms(sym)
                   ) 

    def priv_above(sym,i):
        return And(plus1mod3(sym['a'](i))==sym['a_next'](i),i!=sym['top'])
            
    def priv_below(sym,i):
        return And(plus1mod3(sym['a'](i))==sym['a_prev'](i),i!=sym['bot'])
                         
    def priv_bot(sym,i):
        return priv_above(sym,i)

    def priv_normal(sym,i):
        return Or(
            priv_above(sym,i),
            priv_below(sym,i)
        )
    
    def priv_top(sym,i):
        return And(
            sym['a_prev'](i)==sym['a'](sym['bot']),
            sym['a'](i)!=plus1mod3(sym['a'](sym['bot'])),
        )
    
    def priv(sym,i):
        return Or(
            And(i==sym['bot'],priv_bot(sym,i)),
            And(i==sym['top'],priv_top(sym,i)),
            And(i!=sym['bot'],i!=sym['top'],priv_normal(sym,i)),
        )

    #these are unchanged
    def move_bot(sym1,sym2): 
        skd = sym1['skd']
        return And(
            plus2mod3(sym1['a'](skd))==sym2['a'](skd),
            ForAll(X,Implies(X!=skd,sym2['a'](X)==sym1['a'](X)))
        )

    def move_normal(sym1,sym2):
        skd = sym1['skd']
        return And(
            plus1mod3(sym1['a'](skd))==sym2['a'](skd),
            ForAll(X,Implies(X!=skd,sym2['a'](X)==sym1['a'](X)))
        )

    def move_top(sym1,sym2):
        skd = sym1['skd']
        return And(
            plus1mod3(sym1['a'](sym1['bot']))==sym2['a'](skd),
            ForAll(X,Implies(X!=skd,sym2['a'](X)==sym1['a'](X)))
        )

    def move(sym1,sym2):
        skd = sym1['skd']
        return Or(
            And(skd==sym1['bot'],move_bot(sym1,sym2)),
            And(skd==sym1['top'],move_top(sym1,sym2)),
            And(skd!=sym1['bot'],skd!=sym1['top'],move_normal(sym1,sym2)),
        )

    def move_idle(sym1,sym2):
        return ForAll(X,sym2['a'](X)==sym1['a'](X))

    param_wakeup = {}
    def tr_wakeup(sym1,sym2,param):
        skd = sym1['skd']
        return And(
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        If(priv(sym1,skd),
           move(sym1,sym2),
           move_idle(sym1,sym2)
           ),
        update_instrumentation(sym1,sym2)
        )

    constant_sym_h = constant_sym | {'node_h':Node} #herbrand const.
    tr_wakeup_with_node_h = lambda sym1,sym2,param: And(tr_wakeup(sym1,sym2,param),sym1['node_h']==sym2['node_h'])
    tr1_with_node_h = ('wakeup',param_wakeup,tr_wakeup_with_node_h)
    ts = TS(sorts,axiom,init,[tr1_with_node_h],constant_sym_h,relation_sym,function_sym)

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(priv(sym,X),priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))

    #Property 1 forall n. G (stable -> F priv(n))

    def generalized_priv_below(sym,i):
        return Or(
            priv_below(sym,i),
            And(i==sym['top'],priv_top(sym,i))
        )

    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    sort_dict = {}
    p1 = lambda sym: And(stable(sym),sym['node_h']!=sym['bot'])
    q1 = lambda sym: generalized_priv_below(sym,sym['node_h'])
    prop1 = LivenessProperty(p1,q1,[r],[sort_dict])

    rho = true
    phi1 = lambda sym: And(
        p1(sym),rho(sym),Not(q1(sym))
    )
    psi = lambda sym,param: BoolVal(True)

    strict_order = lambda sym,param1,param2 : And(sym['leq_node'](param1['i'],param2['i']),param1['i']!=param2['i'])
    reverse_order = lambda sym,param1,param2 : And(sym['leq_node'](param2['i'],param1['i']),param1['i']!=param2['i'])

    after_h_below = lambda sym,param : And(generalized_priv_below(sym,param['i']),sym['leq_node'](sym['node_h'],param['i']))
    before_h_below = lambda sym,param : And(generalized_priv_below(sym,param['i']),sym['leq_node'](param['i'],sym['node_h']))
    priv_above_pred = lambda sym,param: priv_above(sym,param['i'])
    generalized_priv_below_pred = lambda sym,param: generalized_priv_below(sym,param['i'])    
    binary_after_below = BinaryFreeRank(after_h_below,{'i':Node})
    binary_above = BinaryFreeRank(priv_above_pred,{'i':Node})
    binary_before_below = BinaryFreeRank(before_h_below,{'i':Node})
    agg_after_below = ParLexFreeRank(binary_after_below,{'i':Node},strict_order)
    agg_above = ParLexFreeRank(binary_above,{'i':Node},reverse_order)
    agg_before_below = ParLexFreeRank(binary_before_below,{'i':Node},strict_order)
    rank1 = LexFreeRank([agg_after_below,agg_above,agg_before_below])
    
    proof1 = LivenessProof(prop1,rank1,rho,phi1,[psi])
    print('checking P1') ; proof1.check_proof(ts)

    #Property 2 forall n. G (stable & n != top -> F priv_above(n))

    p2 = lambda sym: And(stable(sym),sym['node_h']!=sym['top'])
    q2 = lambda sym: priv_above(sym,sym['node_h'])
    prop2 = LivenessProperty(p2,q2,[r],[sort_dict])
    phi2 = lambda sym: And(p2(sym),rho(sym),Not(q2(sym)))
        
    after_h_above = lambda sym,param : And(priv_above(sym,param['i']),sym['leq_node'](sym['node_h'],param['i']))
    before_h_above = lambda sym,param : And(priv_above(sym,param['i']),sym['leq_node'](param['i'],sym['node_h']))

    binary_before_above = BinaryFreeRank(before_h_above,{'i':Node})
    binary_below = BinaryFreeRank(generalized_priv_below_pred,{'i':Node})
    binary_after_above = BinaryFreeRank(after_h_above,{'i':Node})
    agg_before_above = ParLexFreeRank(binary_before_above,{'i':Node},reverse_order)
    agg_below = ParLexFreeRank(binary_below,{'i':Node},strict_order)
    agg_after_above = ParLexFreeRank(binary_after_above,{'i':Node},reverse_order)
    rank2 = LexFreeRank([agg_before_above,agg_below,agg_after_above])

    proof2 = LivenessProof(prop2,rank2,rho,phi2,[psi])  
    print('checking P1') ; proof2.check_proof(ts)

dijsktra3()
