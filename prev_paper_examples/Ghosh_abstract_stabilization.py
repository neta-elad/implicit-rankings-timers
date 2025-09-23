from z3 import *
from ts import *
import time

def ghosh():

    #This is the abstraction of Ghosh concrete
    #In this file we prove the stabilization property.
    #In the abstraction, instead of using next and prev to define the privileges we treat
    #the values of neighbors as new function symbols that are axiomitized to hold the correct values only for relevant  nodes.
    #Additionally we add as axioms some necessary properties

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
                    #'next' : [Node,Node],
                    #'prev' : [Node,Node],
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
        #succ_node(sym,sym['prev'](X),X),
        #succ_node(sym,X,sym['next'](X)),
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
        #ForAll(X,sym2['next'](X)==sym1['next'](X)),
        #ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        Or(
            If(priv(sym1,n),
               move(sym1,sym2,n),
               move_idle(sym1,sym2,n))
        ),
        update_instrumentation(sym1,sym2)
        )
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    #ts.bounded_check([lambda sym: priv(sym,sym['skd']),true])

    def inv(sym):
        return And(init(sym))

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(priv(sym,X),priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))
    
    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    p = true
    q = stable
    prop = LivenessProperty(p,q,[r],[{}])
    rho = inv
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: BoolVal(True)

    #we say there is a break in i if a[i]!=a[i+1] 
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

    
    #the number of breaks is non-increasing

    PrivType,(above,below) = EnumSort('PrivType',('above','below'))

    def priv_by_type(sym,x,t):
        return Or(
            And(priv_above(sym,x),t==above),
            And(priv_below(sym,x),t==below),
        )

    ### ranking: (P,D) where P = N_(x,t) token(x,t) (showed above to be conserved)
    ### D = sum_(x,t) V(x,t) where V(x,t) is 0 if x doesn't hold token t, and if it does it gives a bound on the number
    ### of steps x may take until crashing into another privilege.

    param_xti = {'x':Node,'t':PrivType,'i':Node}
    param_i = {'i':Node}
    param_xt = {'x':Node,'t':PrivType}

    # specifically, to count V(x,t), we divide into two parts:
    # moves due to below and moves due to above
    # for example, if a node x has a below privilege:
    # if there is a node z>=x with a above privilege to its right, V(x,below) = z-x (below) 
    # if there is no such node but node z!=x has below then V(x,below) = n-1-z (above) +   n-1-x (below)
    # if there is no such node, but a node z<x with above: V(x,below) = n-1-x (below) +  n-1 (above)  +   z (below)
    # if node x has a above privilege:
    # if there is a node z<=x with a below token to its left, V(x,above) = x-z (above)
    # if there is no such node but node z!=x has above then V(x,above) = x (above)  +   z (below)
    # if there is no such node, but a node z>x with below: V(x,above) = x (above) +  n-1 (below) +  n-1-z (above)
    

    #this has slightly different structure than dijkstra2, using Lin because it seems to be faster to run

    #all in all this gives the following two complicated definitions:
    counts_for_below_move = lambda sym,param: Or(
        And(
            #z-x / n-1-x 
            param['t']==below,
            sym['leq_node'](param['x'],param['i']),
            ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y),sym['leq_node'](Y,param['i']),param['i']!=Y),
                             Not(priv_by_type(sym,Y,above)))), 
        ),
        And(
            #z / n-1
            param['t']==above,
            ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                             Not(priv_by_type(sym,Y,below)))),
            ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                             Implies(priv_by_type(sym,Y,above),Y==param['x'])))
        ),
        And(
            #z
            param['t']==below,
            sym['leq_node'](param['i'],param['x']),
            param['i']!=param['x'],
            ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                    Not(priv_by_type(sym,Y,above)))),
            ForAll(Y,Implies(priv_by_type(sym,Y,below),Y==param['x'])),
            ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                             Not(priv_by_type(sym,Y,above)))), 
        ),
    )
    counts_for_above_move = lambda sym,param: Or(
        And(
            #x-z / x  
            param['t']==above,
            sym['leq_node'](param['i'],param['x']),
            ForAll(Y,Implies(And(sym['leq_node'](Y,param['x']),sym['leq_node'](param['i'],Y),param['i']!=Y),
                             Not(priv_by_type(sym,Y,below)))),
        ),
        And(
            #n-1-z / n-1
            param['t']==below,
            ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                             Not(priv_by_type(sym,Y,above)))),
            ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                             Implies(priv_by_type(sym,Y,below),Y==param['x'])))
        ),
        And(
            #n-1-z
            param['t']==above,
            sym['leq_node'](param['x'],param['i']),
            param['i']!=param['x'],
            ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                    Not(priv_by_type(sym,Y,below)))),
            ForAll(Y,Implies(priv_by_type(sym,Y,above),Y==param['x'])),
            ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                             Not(priv_by_type(sym,Y,below)))), 
        ),
    )    
    
    binary_counts_for_below = BinaryFreeRank(counts_for_below_move,param_xti)
    binary_counts_for_above = BinaryFreeRank(counts_for_above_move,param_xti)

    x_term = lambda sym1,sym2,param1,param2: param1['x']
    i_to_x = {'i':x_term}
    i_to_skd = {'i':skd_term}
    hints_for_dist = [i_to_x,i_to_skd]

    dist_below = ParPointwiseFreeRank(binary_counts_for_below,param_i,param_xt,hints_for_dist)
    dist_above = ParPointwiseFreeRank(binary_counts_for_above,param_i,param_xt,hints_for_dist)
    distance_xt = PointwiseFreeRank([dist_above,dist_below],param_xt)

    param_xt = {'x':Node,'t':PrivType}
    pred_token_xt = lambda sym,param: priv_by_type(sym,param['x'],param['t'])

    #hints
    skd_term = lambda sym1,sym2,param1,param2: sym1['skd']
    x_to_skd = {'x':skd_term}
    next_skd_term = lambda sym1,*args : sym1['next_skd']
    prev_skd_term = lambda sym1,*args : sym1['prev_skd']
    x_to_next = {'x':next_skd_term}
    x_to_prev = {'x':prev_skd_term}
    t_to_above = {'t':lambda *args: above}
    t_to_below = {'t':lambda *args: below}
    hints_A = [x_to_skd | t_to_above, x_to_skd | t_to_below]
    hints_B = [x_to_skd | t_to_above, x_to_skd | t_to_below,
                x_to_next | t_to_above, x_to_next | t_to_below,
                x_to_prev | t_to_above, x_to_prev | t_to_below,]

    const_rank = BinaryFreeRank(lambda sym,param: True,param_xt)
    not_pred_token_xt = lambda sym,param: Not(pred_token_xt(sym,param)) 
    token_xt_and_distance_xt = LinFreeRank([const_rank,distance_xt],
                                                 [not_pred_token_xt,pred_token_xt],param_xt)
    sum_distances = ParPermute2FreeRank(token_xt_and_distance_xt,param_xt,{},
                                          hints_A,hints_A,hints_B)
    rank = LexFreeRank([num_breaks,sum_distances])


    not_priv = lambda sym: Not(priv(sym,sym['skd']))
    both_priv = lambda sym: And(priv_above(sym,sym['skd']),
                                priv_below(sym,sym['skd']))    

    proof = LivenessProof(prop,rank,rho,
                          phi,
                          [psi])
    
    start_time = time.time()
    proof.check_proof(ts) #6 minutes
    end_time = time.time()
    runtime = end_time - start_time
    print(f"Runtime: {runtime} seconds")

ghosh()
