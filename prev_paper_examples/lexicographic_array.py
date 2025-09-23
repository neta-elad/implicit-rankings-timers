from z3 import *
from ts import *

#not done

def ackermann():

    #slightly modified - removed the finish action, instead we prove eventually m=0 and len=0 (which is precondition for the finish action)
    #additionally removed temporal instrumentation / witness variables

    #Maybe more natural to model two sorts: stack variables and data variables, but both should have nat semantics.
    Nat = DeclareSort('Nat')
    X = Const('X',Nat)
    Y = Const('Y',Nat)
    Z = Const('Z',Nat)
    W = Const('W',Nat)
    sorts = [Nat]

    constant_sym = {
        'zero' : Nat,
        'len' : Nat,
        'm' : Nat, #initiated arbitrarly
        'n' : Nat, #initiated arbitrarly
    }
    relation_sym = {
        'le' : [Nat,Nat],
        'stack' : [Nat,Nat], #one of these is stack variables and the other is data
    }
    function_sym = {
    }

    succ = lambda sym,n1,n2: And(   
        n1!=n2,sym['le'](n1,n2),
        ForAll(Z,Implies(sym['le'](n1,Z),Or(Z==n1,sym['le'](n2,Z))))
    )
    
    def axiom(sym):
        return And(
            ForAll([X,Y,Z],Implies(And(sym['le'](X,Y),sym['le'](Y,Z)),sym['le'](X,Z))),
            ForAll([X,Y],Implies(And(sym['le'](X,Y),sym['le'](Y,X)),X==Y)),
            ForAll([X,Y],Or(sym['le'](X,Y),sym['le'](Y,X))),
            ForAll(X,sym['le'](sym['zero'],X))
        )
    
    def init(sym):
        return And(
            ForAll([X,Y],sym['stack'](X,Y)==False),
            sym['len']==sym['zero'],
        )
    
    #le,zero are unchanged

    def immutable(sym1,sym2):
        return And(
            ForAll([X,Y],sym2['le'](X,Y)==sym1['le'](X,Y)),
            sym2['zero']==sym1['zero']
        )
    
    #mutables are m,n,stack,len

    def stack_unchanged(sym1,sym2):
        return ForAll([X,Y],sym2['stack'](X,Y)==sym1['stack'](X,Y))
    
    def len_unchanged(sym1,sym2):
        return sym2['len']==sym1['len']

    param_step1 = {
        'm_pop' : Nat,
        'len_pop' : Nat,
    }
    def trans_step1(sym1,sym2,param):
        m_pre = sym1['m']
        m_post = sym2['m']
        n_pre = sym1['n']
        n_post = sym2['n']
        zero = sym1['zero']
        len_pre = sym1['len']
        len_post = sym2['len']
        stack_pre = sym1['stack']
        stack_post = sym2['stack']
        m_pop = param['m_pop']
        len_pop = param['len_pop']
        return And(
            m_pre == zero,
            len_pre != zero,
            succ(sym1,len_pop,len_pre),
            stack_pre(len_pop,m_pop),

            immutable(sym1,sym2),
            len_post == len_pop,
            ForAll([X,Y],stack_post(X,Y)==And(stack_pre(X,Y),Not(And(X==len_pop,Y==m_pop)))),
            m_post == m_pop,
            succ(sym1,n_pre,n_post)
        )
    tr_step1 = ('step1',param_step1,trans_step1)

    param_step2 = {}
    def trans_step2(sym1,sym2,param):
        m_pre = sym1['m']
        m_post = sym2['m']
        n_pre = sym1['n']
        n_post = sym2['n']
        zero = sym1['zero']
        return And(
            m_pre != zero,
            n_pre == zero,

            immutable(sym1,sym2),
            succ(sym1,m_post,m_pre),
            succ(sym1,zero,n_post),
            stack_unchanged(sym1,sym2),
            len_unchanged(sym1,sym2)
        )
    tr_step2 = ('step2',param_step2,trans_step2)

    param_step3 = {
        'm_push' : Nat,
    }
    def trans_step3(sym1,sym2,param):
        m_pre = sym1['m']
        m_post = sym2['m']
        n_pre = sym1['n']
        n_post = sym2['n']
        zero = sym1['zero']
        len_pre = sym1['len']
        len_post = sym2['len']
        stack_pre = sym1['stack']
        stack_post = sym2['stack']
        m_push = param['m_push']
        return And(
            m_pre != zero,
            n_pre != zero,
            succ(sym1,m_push,m_pre),

            immutable(sym1,sym2),
            ForAll([X,Y],stack_post(X,Y)==Or(stack_pre(X,Y),And(X==len_pre,Y==m_push))),
            succ(sym1,len_pre,len_post),
            succ(sym1,n_post,n_pre),
            m_post == m_pre
        )
    tr_step3 = ('step3',param_step3,trans_step3)

    transitions = [tr_step1,tr_step2,tr_step3]
    transition_without_step1 = [tr_step2,tr_step3]
    only_step1 = [tr_step1]
    only_step12 = [tr_step1,tr_step2]

    ts = TS(sorts,axiom,init,transitions,constant_sym,relation_sym,function_sym)


    #A formula for initial states that says that m is 4 and n is 3
    init_m_n = lambda sym: Exists([X,Y,Z],And(
        succ(sym,sym['zero'],X), #X=1
        succ(sym,X,Y), #Y=2
        succ(sym,Y,Z), #Z=3
        succ(sym,Z,sym['m']), #m=4
        Z==sym['n'] #n=3
    ))
    #ts.bounded_check([init_m_n,true,true])

    """
    Fits expected run (from ivy file)
    len0 : nat0
    m0 : nat4
    n0 : nat3
    stack0 : [else -> False]

    len1 : nat1
    m1 : nat4
    n1 : nat2
    stack1 : [else ->
    Or(stack0(Var(0), Var(1)),
        Not(Or(Not(Var(0) == nat0),
            Not(Var(1) == nat3))))]

    len2 : nat2
    m2 : nat4
    n2 : nat1
    stack2 : [else ->
    Or(stack1(Var(0), Var(1)),
        Not(Or(Not(Var(0) == nat1),
            Not(Var(1) == nat3))))]
    """

    #This is all very draft because we don't have the formalism down, and you need to do 
    # some finiteness checks that I haven't implemented. 

    r = lambda *args : True
    p = true 
    q = lambda sym: And(sym['m']==sym['zero'],sym['len']==sym['zero'])
    prop = LivenessProperty(p,q,[r],[{}])

    #liveness proof

       
    rho = lambda sym: And(
        #invariants from ivy
        # The stack is only populated for elements smaller than len
        ForAll([X,Y],Implies(sym['stack'](X,Y),Not(sym['le'](sym['len'],X)))),
        # The stack contains at most one element on each position
        ForAll([X, Y, Z], Implies(And(sym['stack'](X, Y), sym['stack'](X, Z)), Y == Z)),
        # The stack is always decreasing
        ForAll([X, Y, Z, W], Implies(And(sym['stack'](X, Y), sym['stack'](Z, W), sym['le'](X, Z)), sym['le'](W, Y))),	   
	    # m is at most the greatest value in the stack + 1
        ForAll([X, Y, Z], Implies(And(sym['stack'](X, Y), Not(sym['le'](Z, Y))), sym['le'](sym['m'], Z))),
    )
    #ts.check_inductiveness(rho)

    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = true

    param_k = {'k':Nat}
    param_i = {'i':Nat}
    param_ik = param_k | param_i

    """
    #ranking: 3-part lex
    # (1) lexicographic aggregation over the possible values on the stack,
    # for each counting the number of positions in the stack that hold it.
    # (2) the current value of m
    # (3) the current value of n

    leq_m = lambda sym,param: sym['le'](param['k'],sym['m'])  
    bin_m = BinaryFreeRank(leq_m,param_k)
    rank_m = ParPointwiseFreeRank(bin_m,param_k)

    leq_n = lambda sym,param: sym['le'](param['k'],sym['n'])  
    bin_n = BinaryFreeRank(leq_n,param_k)
    rank_n = ParPointwiseFreeRank(bin_n,param_k)

    
    #this all doesn't work right now, but it's close
    #we probably need a similar idea to what we used in other places of a ghost value of the stack
    #such that transitions of type step3 do not change the ghost value.    

    stack_predicate = lambda sym,param: sym['stack'](param['i'],param['k'])
    k_is_max_value_in_stack = lambda sym,param: ForAll([X,Y],Implies(sym['stack'](X,Y),sym['le'](Y,param['k'])))
    both_predicates = lambda sym,param: And(stack_predicate(sym,param),k_is_max_value_in_stack(sym,param))

    binary_rank = BinaryFreeRank(stack_predicate,param_ik)
    num_positions_with_value = ParPointwiseFreeRank(binary_rank,param_i,param_k)
    order_formula = lambda sym,param1,param2: And(sym['le'](param1['k'],param2['k']),param1['k']!=param2['k'])
    reverse_order = lambda sym,param1,param2: And(sym['le'](param2['k'],param1['k']),param1['k']!=param2['k'])
    lexicographic_aggregation = ParLexFreeRank(num_positions_with_value,param_k,order_formula)

    rank = LexFreeRank([lexicographic_aggregation,rank_m,rank_n])

    proof = LivenessProof(prop,rank,rho,phi,[psi])
    #proof.check_proof(ts)
    """
    
    #different idea for ranking: just hold the values in the stack - with bot < 0 < 1 < 2 < ..
    #so we track the stack such that m is in position len in the stack.

    predicate = lambda sym,param: Or(
           #counting the number of values k such that k <= stack(i)
           And(
               Exists(X,And(sym['stack'](param['i'],X))),
               ForAll(X,Implies(sym['stack'](param['i'],X),sym['le'](param['k'],X))),
           ),
           #m is in position len in the stack
           And(param['i']==sym['len'],sym['le'](param['k'],sym['m']))
    )
    order_formula = lambda sym,param1,param2: And(sym['le'](param1['i'],param2['i']),param1['i']!=param2['i'])

    binary_rank_stack = BinaryFreeRank(predicate,param_ik)
    value_in_stack = ParPointwiseFreeRank(binary_rank_stack,param_k,param_i)
    whole_stack = ParLexFreeRank(value_in_stack,param_i,order_formula)

    proof = LivenessProof(prop,whole_stack,rho,phi,[psi])
    proof.check_proof(ts)

ackermann()