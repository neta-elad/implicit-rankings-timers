from z3 import *
from ts import *
import time

def ghosh():

    #This is the abstraction of Ghosh concrete
    #In this file we prove the fairness property.
    #In the abstraction, instead of using next and prev to define the privileges we treat
    #the values of neighbors as new function symbols that are axiomitized to hold the correct values only for relevant  nodes.
    #Additionally we add as axioms some necessary propertiess

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
                     'next_skd' : Node,
                     'prev_skd' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node]}
    function_sym = {
                     'a' : [Node,BitVecSort(2)],
                     'a_next' : [Node,BitVecSort(2)],
                     'a_prev' : [Node,BitVecSort(2)],
                    }
    
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
        succ_node(sym,sym['skd'],sym['next_skd']),
        succ_node(sym,sym['prev_skd'],sym['skd']),
        ))
        
    def abstraction_axioms(sym):
        skd = sym['skd']
        next_skd = sym['next_skd']
        prev_skd = sym['prev_skd']
        return And(
            sym['a_next'](skd)==sym['a'](next_skd),
            sym['a_next'](prev_skd)==sym['a'](skd),
            sym['a_prev'](skd)==sym['a'](prev_skd),
            sym['a_prev'](next_skd)==sym['a'](skd),
            Exists(X,priv(sym,X)),
        )            

    def axiom(sym):
        return And(axiom_leq_node(sym),
                   abstraction_axioms(sym))
    
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

    def priv_above(sym,i):
        return And(sym['a'](i)+1==sym['a_next'](i),i!=sym['top'])
            
    def priv_below(sym,i):
        return And(sym['a'](i)+1==sym['a_prev'](i),i!=sym['bot'])
    
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
        Or(
            If(priv(sym1,n),
               move(sym1,sym2,n),
               move_idle(sym1,sym2,n))
        ),
        update_instrumentation(sym1,sym2)
        )
    
    constant_sym_h = constant_sym | {'node_h':Node} #herbrand const.
    tr_wakeup_with_node_h = lambda sym1,sym2,param: And(tr_wakeup(sym1,sym2,param),sym1['node_h']==sym2['node_h'])
    tr1_with_node_h = ('wakeup',param_wakeup,tr_wakeup_with_node_h)
    ts = TS(sorts,axiom,init,[tr1_with_node_h],constant_sym_h,relation_sym,function_sym)

    def inv(sym):
        return And(init(sym))
    
    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(priv(sym,X),priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))
    
    #Property 1 forall n. G (stable & n != bot -> F priv_below(n))

    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    sort_dict = {}
    p1 = lambda sym: And(stable(sym),sym['node_h']!=sym['bot'])
    q1 = lambda sym: priv_below(sym,sym['node_h'])
    prop1 = LivenessProperty(p1,q1,[r],[sort_dict])

    rho = inv
    phi1 = lambda sym: And(
        p1(sym),rho(sym),Not(q1(sym))
    )
    psi = lambda sym,param: BoolVal(True)

    strict_order = lambda sym,param1,param2 : And(sym['leq_node'](param1['i'],param2['i']),param1['i']!=param2['i'])
    reverse_order = lambda sym,param1,param2 : And(sym['leq_node'](param2['i'],param1['i']),param1['i']!=param2['i'])

    after_h_below = lambda sym,param : And(priv_below(sym,param['i']),sym['leq_node'](sym['node_h'],param['i']))
    before_h_below = lambda sym,param : And(priv_below(sym,param['i']),sym['leq_node'](param['i'],sym['node_h']))
    priv_above_pred = lambda sym,param: priv_above(sym,param['i'])
    priv_below_pred = lambda sym,param: priv_below(sym,param['i'])    
    binary_after_below = BinaryFreeRank(after_h_below,{'i':Node})
    binary_above = BinaryFreeRank(priv_above_pred,{'i':Node})
    binary_before_below = BinaryFreeRank(before_h_below,{'i':Node})
    agg_after_below = ParLexFreeRank(binary_after_below,{'i':Node},strict_order)
    agg_above = ParLexFreeRank(binary_above,{'i':Node},reverse_order)
    agg_before_below = ParLexFreeRank(binary_before_below,{'i':Node},strict_order)
    rank_4state = LexFreeRank([agg_after_below,agg_above,agg_before_below])
    #this is the ranking we used in dijkstra's 4-state protocol, we need to add to it - the number of breaks

    def in_break(sym,i):
        return And(sym['a'](i)!=sym['a_next'](i),i!=sym['top'])
    
    param_x = {'x':Node}
    
    skd_term = lambda sym1,sym2,param1,param2: sym1['skd']
    next_skd_term = lambda sym1,*args : sym1['next_skd']
    prev_skd_term = lambda sym1,*args : sym1['prev_skd']
    x_to_skd = {'x':skd_term}
    x_to_next = {'x':next_skd_term}
    x_to_prev = {'x':prev_skd_term}
    hints_x = [x_to_skd,x_to_next,x_to_prev]

    pred_break = lambda sym,param: in_break(sym,param['x'])
    binary_break = BinaryFreeRank(pred_break,param_x)
    num_breaks = ParPermFreeRank(binary_break,param_x,{},1,[],hints_x)

    rank1 = LexFreeRank([num_breaks,rank_4state])

    proof1 = LivenessProof(prop1,rank1,rho,phi1,[psi])
    print('checking proof 1') ; proof1.check_proof(ts)


    #Property 2 forall n. G (stable & n != top -> F priv_above(n))

    p2 = lambda sym: And(stable(sym),sym['node_h']!=sym['top'])
    q2 = lambda sym: priv_above(sym,sym['node_h'])
    prop2 = LivenessProperty(p2,q2,[r],[sort_dict])
    phi2 = lambda sym: And(p2(sym),rho(sym),Not(q2(sym)))
        
    after_h_above = lambda sym,param : And(priv_above(sym,param['i']),sym['leq_node'](sym['node_h'],param['i']))
    before_h_above = lambda sym,param : And(priv_above(sym,param['i']),sym['leq_node'](param['i'],sym['node_h']))

    binary_before_above = BinaryFreeRank(before_h_above,{'i':Node})
    binary_below = BinaryFreeRank(priv_below_pred,{'i':Node})
    binary_after_above = BinaryFreeRank(after_h_above,{'i':Node})
    agg_before_above = ParLexFreeRank(binary_before_above,{'i':Node},reverse_order)
    agg_below = ParLexFreeRank(binary_below,{'i':Node},strict_order)
    agg_after_above = ParLexFreeRank(binary_after_above,{'i':Node},reverse_order)
    rank2 = LexFreeRank([num_breaks,agg_before_above,agg_below,agg_after_above])

    proof2 = LivenessProof(prop2,rank2,rho,phi2,[psi])  
    proof2.check_proof(ts)


ghosh()

