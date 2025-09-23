from z3 import *
from ts import *
import time

def dijkstra4state():

    #This is the abstraction of Dijkstra 4-state concrete
    #In this file we prove the stabilization property.
    #In the abstraction, instead of using next and prev to define the privileges we treat
    #the privileges as new relation symbols that are axiomitized to hold the correct values only for relevant  nodes.

    print('Dijkstra 4-state')

    Node = DeclareSort('Node')
    sorts = [Node]
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)

    PrivType,(above,below) = EnumSort('PrivType',('above','below'))

    constant_sym = { 'skd' : Node,
                     'next_skd' : Node,
                     'prev_skd' : Node,
                     'top' : Node,
                     'bot' : Node
                     }
    relation_sym = {'leq_node' : [Node,Node],
                    'x' : [Node],
                    'up' : [Node],
                    'priv_above' : [Node], #instrumentation relation that should hold the value priv_above(i) = x(i) = x(i+1) & up(i) & !up(i+1) for all i != top
                    'priv_below' : [Node], #instrumentation relation that should hold the value priv_below(i) = x(i) != x(i-1) for all i != bot      
    }
    function_sym = {
        #'next' : [Node,Node],
        #'prev' : [Node,Node]
        }
    

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
        #succ_node(sym,sym['prev'](X),X),
        #succ_node(sym,X,sym['next'](X)),
        succ_node(sym,sym['skd'],sym['next_skd']),
        succ_node(sym,sym['prev_skd'],sym['skd']),
        ))
    
    def abstraction_axioms(sym):
        #these are axioms we proved on the concrete model we can assume here
        return And(
            Exists(X,any_priv(sym,X)),
            inst_correct_for_skd(sym)
        )

    def axiom(sym):
        return And(axiom_leq_node(sym),
                   abstraction_axioms(sym),
                   )

    def inst_correct_for_skd(sym):
        skd = sym['skd']
        prev_skd = sym['prev_skd']
        next_skd = sym['next_skd']
        return And(
            sym['priv_above'](skd)==And(sym['x'](skd)==sym['x'](next_skd),sym['up'](skd),Not(sym['up'](next_skd)),skd!=sym['top']),
            sym['priv_above'](prev_skd)==And(sym['x'](prev_skd)==sym['x'](skd),sym['up'](prev_skd),Not(sym['up'](skd)),prev_skd!=sym['top']),
            sym['priv_below'](skd)==And(sym['x'](skd)!=sym['x'](prev_skd),skd!=sym['bot']),
            sym['priv_below'](next_skd)==And(sym['x'](next_skd)!=sym['x'](skd),next_skd!=sym['bot']),
        )
    

    def init(sym):
        return And(
            sym['up'](sym['bot'])==True,
            sym['up'](sym['top'])==False
        )

    #we rewrite the privileges conditions to use the instrumentation

    def priv_below(sym,i):
        return sym['priv_below'](i)
    
    def priv_above(sym,i):
        return sym['priv_above'](i)
    
    def any_priv(sym,i):
        return Or(priv_above(sym,i),priv_below(sym,i))

    #a more simple notion is how to update the instrumentation variables when a transition takes place, we just need to update
    #priv_below for skd,skd+1 and priv_above for skd,skd-1,
    #in some cases we update some things that will certainly not change, but that does no harm
    #it is easily seen that only the following updates can be necessary for any transition:
    def update_instrumentation(sym1,sym2):
        skd = sym1['skd']
        prev_skd = sym1['prev_skd']
        next_skd = sym1['next_skd']
        return And(
            #priv_above(i) = x(i) = x(i+1) & up(i) & !up(i+1)
            sym2['priv_above'](skd)==And(sym2['x'](skd)==sym2['x'](next_skd),sym2['up'](skd),Not(sym2['up'](next_skd)),skd!=sym2['top']),
            sym2['priv_above'](prev_skd)==And(sym2['x'](prev_skd)==sym2['x'](skd),sym2['up'](prev_skd),Not(sym2['up'](skd)),prev_skd!=sym2['top']),
            ForAll(X,Implies(And(X!=skd,X!=prev_skd),sym2['priv_above'](X)==sym1['priv_above'](X))),
            #priv_below(i) = x(i) != x(i-1)
            sym2['priv_below'](skd)==And(sym2['x'](skd)!=sym2['x'](prev_skd),skd!=sym2['bot']),
            sym2['priv_below'](next_skd)==And(sym2['x'](next_skd)!=sym2['x'](skd),next_skd!=sym2['bot']),
            ForAll(X,Implies(And(X!=skd,X!=next_skd),sym2['priv_below'](X)==sym1['priv_below'](X))),
        )

    def move_below_normal(sym1,sym2):
        skd = sym1['skd']
        return And(
            sym2['x'](skd)==Not(sym1['x'](skd)),
            sym2['up'](skd)==True,
            ForAll(X,Implies(X!=skd,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=skd,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_below_top(sym1,sym2):
        skd = sym1['skd']
        return And(
            sym2['x'](skd)==Not(sym1['x'](skd)),
            sym2['up'](skd)==sym1['up'](skd),
            ForAll(X,Implies(X!=skd,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=skd,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_below(sym1,sym2):
        skd = sym1['skd']
        return If(skd==sym1['top'],
            move_below_top(sym1,sym2),
            move_below_normal(sym1,sym2))
              
    def move_above_normal(sym1,sym2):
        skd = sym1['skd']
        return And(
            sym2['x'](skd)==sym1['x'](skd),
            sym2['up'](skd)==False,
            ForAll(X,Implies(X!=skd,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=skd,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_above_bot(sym1,sym2):
        skd = sym1['skd']
        return And(
            sym2['x'](skd)==Not(sym1['x'](skd)),
            sym2['up'](skd)==sym1['up'](skd),
            ForAll(X,Implies(X!=skd,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=skd,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_above(sym1,sym2):
        skd = sym1['skd']
        return If(skd==sym1['bot'],
            move_above_bot(sym1,sym2),
            move_above_normal(sym1,sym2))

    def move_idle(sym1,sym2):
        return And(
            ForAll(X,sym2['x'](X)==sym1['x'](X)),
            ForAll(X,sym2['up'](X)==sym1['up'](X)),
        ) 

    param_wakeup = {}
    def tr_wakeup(sym1,sym2,param):
        skd = sym1['skd']
        return And(
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        Or(
            And(priv_above(sym1,skd),move_above(sym1,sym2)),
            And(priv_below(sym1,skd),move_below(sym1,sym2)),
            And(Not(any_priv(sym1,skd)),move_idle(sym1,sym2)),
        ), 
        update_instrumentation(sym1,sym2)
    )
        
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    def basic_inv(sym):
        return And(           
            sym['up'](sym['bot'])==True,
            sym['up'](sym['top'])==False,
        )   

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(any_priv(sym,X),any_priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))
    
    r = lambda sym,param: Implies(Exists(X,any_priv(sym,X)),any_priv(sym,sym['skd']))
    p = true
    q = stable
    prop = LivenessProperty(p,q,[r],[{}])
    rho = basic_inv
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: z3.BoolVal(True)


    #Definitions of Rankings:

    #P = N_(x,t) token(x,t)
    #simple trick to make formulas simpler:
    priv_by_type = lambda sym,node,type : Or(
        And(type==above,priv_above(sym,node)),
        And(type==below,priv_below(sym,node))
    )

    param_xt = {'x':Node,'t':PrivType}
    pred_token_xt = lambda sym,param: priv_by_type(sym,param['x'],param['t'])
    binary_token_xt = BinaryFreeRank(pred_token_xt,param_xt)

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

    num_tokens = ParPermFreeRank(binary_token_xt,param_xt,{},1,hints_A,hints_B)
    #proof_simple = LivenessProof(prop,num_tokens,rho,phi,[psi])
    #proof_simple.premise_conserved(ts)

    ### ranking: (P,D) where P = N_(x,t) token(x,t) (showed above to be conserved)
    ### D = sum_(x,t) V(x,t) where V(x,t) is 0 if x doesn't hold token t, and if it does it gives a bound on the number
    ### of steps x may take until crashing into another privilege.

    param_xti = {'x':Node,'t':PrivType,'i':Node}
    param_i = {'i':Node}

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
    

    #first version, with linear constructor - runs faster

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

    const_rank = BinaryFreeRank(lambda sym,param: True,param_xt)
    not_pred_token_xt = lambda sym,param: Not(pred_token_xt(sym,param)) 
    token_xt_and_distance_xt = LinFreeRank([const_rank,distance_xt],
                                                 [not_pred_token_xt,pred_token_xt],param_xt)
    sum_distances = ParPermute2FreeRank(token_xt_and_distance_xt,param_xt,{},
                                          hints_A,hints_A,hints_B)
    rank = LexFreeRank([num_tokens,sum_distances])

    proof = LivenessProof(prop,rank,rho,phi,[psi])
    
    proof.check_proof(ts) 


    #second version - without linear constructor, whats written in the paper, takes more time

    counts_for_below_move = lambda sym,param: And(
        pred_token_xt(sym,param),
        Or(
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
    )
    counts_for_above_move = lambda sym,param: And(
        pred_token_xt(sym,param),
        Or(
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
    )    
    
    binary_counts_for_below = BinaryFreeRank(counts_for_below_move,param_xti)
    binary_counts_for_above = BinaryFreeRank(counts_for_above_move,param_xti)

    x_term = lambda sym1,sym2,param1,param2: param1['x']
    i_to_x = {'i':x_term}
    i_to_skd = {'i':skd_term}
    hints_for_dist = [i_to_x]

    dist_below = ParPointwiseFreeRank(binary_counts_for_below,param_i,param_xt,hints_for_dist)
    dist_above = ParPointwiseFreeRank(binary_counts_for_above,param_i,param_xt,hints_for_dist)
    distance_xt = PointwiseFreeRank([dist_above,dist_below],param_xt)
    
    sum_distances = ParPermute2FreeRank(distance_xt,param_xt,{},
                                            hints_A,hints_A,hints_B ###Here if you remove the hints it times out (you can comment out the line)
                                            )
    rank = LexFreeRank([num_tokens,sum_distances])

    proof = LivenessProof(prop,rank,rho,phi,[psi])
    
    #proof.check_proof(ts) #~500 secs

dijkstra4state()
