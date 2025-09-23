from z3 import *
from ts import *

def toy_stab():

    #Verification of the system described in the first motivating example
    #Nodes are ordered in a ring with bot as a special element
    #at any transition a node may give its privilege to the node to its right
    #we want to show that eventually node bot is scheduled.

    print("toy stabilization")

    #Specification of the transition system

    Node = DeclareSort('Node')
    sorts = [Node]
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    
    constant_sym = { 
        'skd' : Node,
        'bot' : Node, 
    }
    relation_sym = {
        'leq_node' : [Node,Node],
        'token' : [Node],
    }
    function_sym = {
        'next' : [Node,Node] #explicit next function (not EPR)
    }
    def init(sym):
        return Exists(X,sym['token'](X))
    
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
        sym['leq_node'](sym['bot'],X), #bot is min instead of max
        succ_node(sym,X,sym['next'](X)),
        ))

    def axiom(sym):
        return And(axiom_leq_node(sym))

    def priv(sym,x):
        return sym['token'](x)
    
    def move(sym1,sym2,x):
        return And(
            Not(sym2['token'](x)),
            sym2['token'](sym1['next'](x)),
            ForAll(X,Implies(And(X!=x,X!=sym1['next'](x)),
                             sym2['token'](X)==sym1['token'](X)))
        )
    
    def move_idle(sym1,sym2,x):
        return ForAll(X,sym2['token'](X)==sym1['token'](X))

    param_wakeup = {}
    def tr_wakeup(sym1,sym2,param):
        n = sym1['skd']
        return And(
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        Or(
            And(priv(sym1,n),move(sym1,sym2,n)),
            And(Not(priv(sym1,n)),move_idle(sym1,sym2,n))
        )
    )
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)

    #Declaration of transition system:
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    
    #ts.bounded_check([true,true]) #good sanity check

    #Liveness Property:

    def bot_is_skd(sym):
        return sym['skd']==sym['bot']

    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    sort_dict = {}
    p = true
    q = bot_is_skd
    prop = LivenessProperty(p,q,[r],[sort_dict])
    
    #Start of Proof:

    rho = lambda sym: Exists(X,priv(sym,X))
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: BoolVal(True)

    dict_i = {'i':Node}
    dict_j = {'j':Node}

    #Definition of formulas and rankings
    j_counts_towards_i = lambda sym,param: And(
        priv(sym,param['i']),
        param['i']!=sym['bot'],
        sym['leq_node'](param['i'],param['j']),
    )
    binary_rank = BinaryFreeRank(
        j_counts_towards_i, #predicate
        dict_i | dict_j #free variables
    )
    sum_over_j = ParPointwiseFreeRank(
        binary_rank, #input ranking
        dict_j, #quantified variables
        dict_i #free variables
    )
    sum_over_i = ParPermFreeRank(
        sum_over_j, #input ranking
        dict_i, #quantified variables
        {}, #free variables
        1 #number of transpositions
    )

    #sum_over_i.print_reduced(ts) #printing the reduction formula 

    proof = LivenessProof(prop,sum_over_i,rho,phi,[psi]) #proof object

    proof.check_proof(ts) #checking a proof: checks all 8 premises

    #proof.premise_reduced(ts) #checks a single premise


toy_stab()


def toy_stab_diff():

    #Verification of the system described in the first motivating example
    #Nodes are ordered in a ring with bot as a special element
    #at any transition a node may give its privilege to the node to its right
    #we want to show that eventually node bot is scheduled.

    print("toy stabilization")

    #Specification of the transition system

    Node = DeclareSort('Node')
    sorts = [Node]
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    
    constant_sym = { 
        'skd' : Node,
        'bot' : Node, #actually axiomitized to be max in the order for simplicity
    }
    relation_sym = {
        'leq_node' : [Node,Node],
        'token' : [Node],
    }
    function_sym = {
        'next' : [Node,Node] #explicit next function (not EPR)
    }
    def init(sym):
        return Exists(X,sym['token'](X))
    
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
        sym['leq_node'](X,sym['bot']),
        succ_node(sym,X,sym['next'](X)),
        ))

    def axiom(sym):
        return And(axiom_leq_node(sym))

    def priv(sym,x):
        return sym['token'](x)
    
    def move(sym1,sym2,x):
        return And(
            Not(sym2['token'](x)),
            sym2['token'](sym1['next'](x)),
            ForAll(X,Implies(And(X!=x,X!=sym1['next'](x)),
                             sym2['token'](X)==sym1['token'](X)))
        )
    
    def move_idle(sym1,sym2,x):
        return ForAll(X,sym2['token'](X)==sym1['token'](X))

    param_wakeup = {}
    def tr_wakeup(sym1,sym2,param):
        n = sym1['skd']
        return And(
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        Or(
            And(priv(sym1,n),move(sym1,sym2,n)),
            And(Not(priv(sym1,n)),move_idle(sym1,sym2,n))
        )
    )
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)

    #Declaration of transition system:
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    
    #ts.bounded_check([true,true]) #good sanity check

    #Liveness Property:

    def bot_is_skd(sym):
        return sym['skd']==sym['bot']

    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    sort_dict = {}
    p = true
    q = bot_is_skd
    prop = LivenessProperty(p,q,[r],[sort_dict])
    
    #Start of Proof:

    rho = lambda sym: Exists(X,priv(sym,X))
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: BoolVal(True)

    dict_i = {'i':Node}
    dict_j = {'j':Node}

    #Definition of formulas and rankings
    j_counts_towards_i = lambda sym,param: And(
        priv(sym,param['i']),
        sym['leq_node'](param['i'],param['j']),
        param['i']!=param['j']
    )
    binary_rank = BinaryFreeRank(
        j_counts_towards_i, #predicate
        dict_i | dict_j #free variables
    )
    sum_over_j = ParPointwiseFreeRank(
        binary_rank, #input ranking
        dict_j, #quantified variables
        dict_i #free variables
    )
    sum_over_i = ParPermFreeRank(
        sum_over_j, #input ranking
        dict_i, #quantified variables
        {}, #free variables
        1 #number of transpositions
    )

    #sum_over_i.print_reduced(ts) #printing the reduction formula 

    proof = LivenessProof(prop,sum_over_i,rho,phi,[psi]) #proof object

    proof.check_proof(ts) #checking a proof: checks all 8 premises

    #proof.premise_reduced(ts) #checks a single premise

