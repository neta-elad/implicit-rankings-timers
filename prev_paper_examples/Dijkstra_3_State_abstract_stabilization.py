from z3 import *
from ts import *

def dijsktra3state():

    #This is the abstraction of Dijkstra 3-state concrete
    #In this file we prove the stabilization property.
    #In the abstraction, instead of using next and prev to define the privileges we treat
    #the values of neighbors as new function symbols that are axiomitized to hold the correct values only for relevant  nodes.
    #Additionally we add as axioms some necessary properties

    #The ranking argument we use is based directly on
    #Kessels, J.L.W.: An exercise in proving self-stabilization with a variant function. 
    #Inf. Process. Lett. 29(1), 39–42 (1988), https://doi.org/10.1016/0020-0190(88)90131-7

    print('dijkstra3state')

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
                     #'prev_top' : Node, #maybe helpful??
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
            #sym['a_next'](top) == sym['a'](bot),
            #sym['a_prev'](bot) == sym['a'](top), #unnecessary
            #sym['a_next'](bot) == sym['a'](sym['next_bot']),
            #sym['a_prev'](top) == sym['a'](sym['prev_top'])
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
    
    def abstraction_axioms(sym):
        #these are axioms we proved on the concrete model we can assume here
        return And(
            Exists(X,priv(sym,X)),
            inst_correct_around_skd(sym),
            case10_axiom(sym)
        )

    def axiom(sym):
        return And(axiom_leq_node(sym),
                   axiom_3_machines(sym),
                   abstraction_axioms(sym)
                   ) 

    #These are rewritten with the instrumentation:

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
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    #ts.bounded_check([lambda sym:Exists([X,Y],X!=Y),true])

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(priv(sym,X),priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))
    
    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    p = true
    q = stable
    prop = LivenessProperty(p,q,[r],[{}])
    rho = true
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: z3.BoolVal(True)

    #ts.bounded_check([true,true])

    #start of encoding of Kessel's Proof
    #The hinting is not optimal - so it will be quite complicated, but can be improved hopefully.
    #in comments - breaking of the proof into cases which is not necessarily but was helpful when I was writing it.

    #ranking function (a)
    #we encode the scaled sum by treating any coefificent as multiple instances of some enum sort
    #and then using the permuted pointwise constructor with pairs (node,enumsort)

    def greater_than_next(sym,x):
        return sym['a'](x)==plus1mod3(sym['a_next'](x))

    def smaller_than_next(sym,x):
        return plus1mod3(sym['a'](x))==(sym['a_next'](x))
    
    def equal_top_bottom(sym,x):
        #this is a predicate on x for uniformity but can hold true only on x==top
        return And(x==sym['top'],sym['a'](sym['top'])==sym['a'](sym['bot'])) #should we replace a(bot) with a_next(top)

    SixSort, (great1, small1, small2, equal1, equal2, equal3) = EnumSort(
        'SixSort', ('great1','small1','small2','equal1','equal2','equal3')
    )

    def unified_predicate(sym,param):
        t = param['t']
        x = param['x']
        return Or(
            And(t==great1,greater_than_next(sym,x)),
            And(Or(t==small1,t==small2),smaller_than_next(sym,x)),
            And(Or(t==equal1,t==equal2,t==equal3),equal_top_bottom(sym,x)),
        )
    
    binary_rank_a = BinaryFreeRank(unified_predicate,{'x':Node,'t':SixSort})

    ###HINTS
    skd_term = lambda sym1,sym2,param1,param2: sym1['skd']
    next_skd_term = lambda sym1,*args : sym1['next_skd']
    prev_skd_term = lambda sym1,*args : sym1['prev_skd']
    top_term = lambda sym1,*args : sym1['top']
    term_great1 = lambda *args : great1
    term_small1 = lambda *args : small1
    term_small2 = lambda *args : small2
    term_equal1 = lambda *args : equal1
    term_equal2 = lambda *args : equal2
    term_equal3 = lambda *args : equal3
    skd_great1 = {'x':skd_term,'t':term_great1}
    skd_small1 = {'x':skd_term,'t':term_small1}
    skd_small2 = {'x':skd_term,'t':term_small2}
    next_skd_great1 = {'x':next_skd_term,'t':term_great1}
    next_skd_small1 = {'x':next_skd_term,'t':term_small1}
    next_skd_small2 = {'x':next_skd_term,'t':term_small2}
    prev_skd_great1 = {'x':prev_skd_term,'t':term_great1}
    prev_skd_small1 = {'x':prev_skd_term,'t':term_small1}
    prev_skd_small2 = {'x':prev_skd_term,'t':term_small2}
    top_equal1 = {'x':top_term,'t':term_equal1}
    top_equal2 = {'x':top_term,'t':term_equal2}
    top_equal3 = {'x':top_term,'t':term_equal3}

    
    """
    case0 = lambda sym: Not(priv(sym,sym['skd']))
    case1 = lambda sym: And(sym['skd']==sym['bot'],
                            plus1mod3(sym['a'](sym['top']))==sym['a'](sym['bot']),
                            plus1mod3(sym['a'](sym['bot']))==sym['a_next'](sym['bot']))  
    case2 = lambda sym: And(sym['skd']==sym['bot'],
                            sym['a'](sym['top'])==sym['a'](sym['bot']),
                            plus1mod3(sym['a'](sym['bot']))==sym['a_next'](sym['bot']))   
    case3 = lambda sym: And(sym['skd']==sym['bot'],
                            sym['a'](sym['top'])==plus1mod3(sym['a'](sym['bot'])),
                            plus1mod3(sym['a'](sym['bot']))==sym['a_next'](sym['bot']))
    case4 = lambda sym: And(sym['skd']!=sym['bot'],sym['skd']!=sym['top'],
                            plus1mod3(sym['a'](sym['skd']))==sym['a_prev'](sym['skd']),
                            plus1mod3(sym['a'](sym['skd']))==sym['a_next'](sym['skd']),
    )
    case5 = lambda sym: And(sym['skd']!=sym['bot'],sym['skd']!=sym['top'],
                            plus1mod3(sym['a'](sym['skd']))==sym['a_prev'](sym['skd']),
                            sym['a'](sym['skd'])==sym['a_next'](sym['skd']),
    )
    case6 = lambda sym: And(sym['skd']!=sym['bot'],sym['skd']!=sym['top'],
                            plus1mod3(sym['a'](sym['skd']))==sym['a_prev'](sym['skd']),
                            sym['a'](sym['skd'])==plus1mod3(sym['a_next'](sym['skd'])),
    )
    case7 = lambda sym: And(sym['skd']!=sym['bot'],sym['skd']!=sym['top'],
                            sym['a'](sym['skd'])==plus1mod3(sym['a_prev'](sym['skd'])),
                            plus1mod3(sym['a'](sym['skd']))==sym['a_next'](sym['skd']),
    )
    case8 = lambda sym: And(sym['skd']!=sym['bot'],sym['skd']!=sym['top'],
                            sym['a'](sym['skd'])==sym['a_prev'](sym['skd']),
                            plus1mod3(sym['a'](sym['skd']))==sym['a_next'](sym['skd']),
    )
    case9 = lambda sym: And(
        sym['skd']==sym['top'],
        sym['a'](sym['top'])==sym['a_next'](sym['top']),
        sym['a'](sym['top'])==sym['a_prev'](sym['top'])
    )
    case10 = lambda sym: And(
        sym['skd']==sym['top'],
        plus1mod3(sym['a'](sym['top']))==sym['a_next'](sym['top']),
        plus1mod3(sym['a'](sym['top']))==sym['a_prev'](sym['top']),
        phi(sym)
    )#For case 10, reduction of b also depends on the system not being in a stable state
    
    
    case123 = lambda sym: sym['skd']==sym['bot']
    case45678 = lambda sym: And(sym['skd']!=sym['bot'],sym['skd']!=sym['top'])
    case910 = lambda sym: sym['skd']==sym['top']
    case247 = lambda sym: Or(case2(sym),case4(sym),case7(sym)) #the cases where a is reduced 
    case_not247 = lambda sym: Not(case247(sym)) #these are the cases that need be conserved by b
    case110 = lambda sym: Or(case1(sym),case10(sym)) #the cases where b is reduced (sometimes also in 6)
    case_not124710 = lambda sym: Not(Or(case247(sym),case110(sym))) #these need be conserved by c
    #case9 is reduced by c
    case_not12467910 = lambda sym: And(case_not124710(sym),Not(case6(sym)),Not(case9(sym)),phi(sym))
    """

    #we need up to 4 permutations, we include the same terms in A,B instats when we need less to give identity for those terms
    hint0a = ([skd_great1,top_equal1,top_equal2,top_equal3],[skd_great1,top_equal1,top_equal2,top_equal3]) #0 perms
    hint1a = ([prev_skd_small1,prev_skd_small2,skd_small1,skd_small2],[top_equal1,top_equal2,top_equal3,skd_great1]) #4 perms
    hint2a = ([skd_small1,skd_small2,top_equal1,top_equal2],[skd_great1,prev_skd_great1,top_equal1,top_equal2]) #2 perms
    hint3a = ([skd_small1,skd_small2,prev_skd_great1,top_equal1],[prev_skd_small1,prev_skd_small2,skd_great1,top_equal1]) #3 perms
    hint4a = hint0a #0 (succeeds with no hint)
    hint5a = ([prev_skd_great1,top_equal1,top_equal2,top_equal3],[skd_great1,top_equal1,top_equal2,top_equal3]) #1
    hint6a = ([prev_skd_great1,skd_great1,top_equal1,top_equal2],[skd_small1,skd_small2,top_equal1,top_equal2]) #2
    hint7a = ([prev_skd_small1,top_equal1,top_equal2,top_equal3],[prev_skd_great1,top_equal1,top_equal2,top_equal3]) #1 (hint 6 works aswell)
    hint8a = ([skd_small1,skd_small2,top_equal1,top_equal2],[prev_skd_small1,prev_skd_small2,top_equal1,top_equal2]) #2
    hint9a = ([top_equal1,top_equal2,top_equal3,prev_skd_great1],[prev_skd_small1,prev_skd_small2,skd_great1,prev_skd_great1]) #3
    hint10a = ([prev_skd_great1,skd_small1,skd_small2,top_equal1],[prev_skd_small1,prev_skd_small2,skd_great1,skd_small2,top_equal1]) #3

    #different hints for reduced
    hint2a_r = ([skd_small1,skd_small2,top_equal1,top_equal2],[skd_great1,prev_skd_great1,top_equal1,top_equal2],top_equal1) #2 perms
    hint4a_r = ([skd_great1,top_equal1,top_equal2,top_equal3],[skd_great1,top_equal1,top_equal2,top_equal3],prev_skd_great1) #0 (on its own succeeds with no hint)
    hint7a_r = ([prev_skd_small1,top_equal1,top_equal2,top_equal3],[prev_skd_great1,top_equal1,top_equal2,top_equal3],prev_skd_small2) #1 
    
    #testing variants of hinting
    rank_a = ParPermFreeRank_variant(binary_rank_a,{'x':Node,'t':SixSort},{},4,
                                     [hint0a,
                                    hint1a,hint2a,hint3a,
                                    hint4a,hint5a,hint6a,hint7a,hint8a,
                                    hint9a,hint10a
                                     ],
                                    [hint2a_r,hint4a_r,hint7a_r]
                                     )
    """
    proof_a_conserved = LivenessProof(prop,rank_a,rho,
                          phi, #here we can change the case we look at 
                          [psi]) 
    #proof_a_conserved.premise_conserved(ts)
    proof_a_reduced_247 = LivenessProof(prop,rank_a,rho,
                          case247, #here we can change the case we look at 
                          [psi]) 
    #proof_a_reduced_247.premise_reduced(ts)
    """

    """
    #the bounded ranking doesn't work even for just case1
    hints_for_x = [{'x':skd_term},{'x':prev_skd_term},{'x':next_skd_term},{'x':top_term}]
    rank_a_bounded = ParPermFreeRank_bounded(binary_rank_a,{'x':Node,'t':SixSort},{},4,
                                    [],hints_for_x)
    #rank_a_bounded.print_conserved(ts)
    """


    #ranking function (b)

    #we can encode the sum of three elements similarly to rank a
    #but actually as the predicates can be seen as disjoint there is a much simpler encoding

    def predicate_for_b(sym,param):
        x = param['x']
        return Or(
            And(x!=sym['top'],plus1mod3(sym['a'](x))==sym['a_next'](x)),
            And(x!=sym['top'],sym['a'](x)==plus1mod3(sym['a_next'](x)),
                Exists(Y,And(sym['leq_node'](Y,x),Y!=x,sym['a'](Y)!=sym['a_next'](Y)))),
            And(x==sym['top'],Or(sym['a'](sym['top'])==sym['a'](sym['bot']),
                                 plus1mod3(sym['a'](sym['top']))==sym['a'](sym['bot'])))
        )

    skd_term = lambda sym1,sym2,param1,param2: sym1['skd']
    next_skd_term = lambda sym1,*args : sym1['next_skd']
    prev_skd_term = lambda sym1,*args : sym1['prev_skd']
    top_term = lambda sym1,*args : sym1['top']
    x_skd = {'x':skd_term}
    x_next_skd = {'x':next_skd_term}
    x_prev_skd = {'x':prev_skd_term}
    x_top = {'x':top_term}

    binary_rank_b = BinaryFreeRank(predicate_for_b,{'x':Node})
    hint0b = ([x_top],[x_top]) #0
    hint1b = hint0b #0
    hint3b = ([x_skd],[x_top]) #1  #same as 5 
    hint5b = ([x_prev_skd],[x_skd]) #1
    hint6b = hint0b #0 #interesting case 
    hint8b = hint5b #1
    hint9b = hint5b #1
    hint10b = hint5b #1

    hint1b_r = ([x_top],[x_top],x_skd) #0
    hint6b_r = ([x_top],[x_top],x_prev_skd) #only sometimes guarantees reduced
    hint10b_r = ([x_prev_skd],[x_skd],x_skd) #interesting case, has to do with abstraction

    rank_b = ParPermFreeRank_variant(binary_rank_b,{'x':Node},{},1,
                                     [hint0b,hint5b],
                                     [hint1b_r,hint6b_r,hint10b_r]
                                     )
    """
    proof_b_conserved = LivenessProof(prop,rank_b,rho,
                        case_not247, #here we can change the case we look at 
                        [psi]) 
    #proof_b_conserved.premise_conserved(ts)
    proof_b_reduced = LivenessProof(prop,rank_b,rho,
                        case10, #here we can change the case we look at 
                        [psi]) 
    #proof_b_reduced.premise_reduced(ts) #fails in case10 due to abstraction problem?
    """

    #ranking function (c)

    #similarly to (b), we can use the same encoding as in (a), but we can do something simpler.
    #the ranking doesn't need all the power of the sum, lexicographic suffices.

    def diff_from_next(sym,param):
        x = param['x']
        return And(
            x!=sym['top'],
            sym['a'](x)!=sym['a_next'](x)
        )

    binary_diff = BinaryFreeRank(diff_from_next,{'x':Node})
    num_diff = ParPermFreeRank_variant(binary_diff,{'x':Node},{},1,[hint0b,hint5b],[hint1b_r,hint6b_r,hint10b_r]) 
    #the same hints work for c as for b, importantly, we need hints for reduced even when checking conserved.
    #we can do a case split like we did for a,d but this just works

    def top_bottom_equal(sym,param):
        return sym['a'](sym['top'])==sym['a'](sym['bot'])

    binary_top_bottom_equal = BinaryFreeRank(top_bottom_equal,{})

    rank_c = LexFreeRank([binary_top_bottom_equal,num_diff])

    """
    #rank_c.print_conserved(ts)
    proof_c_conserved = LivenessProof(prop,rank_c,rho,
                        case_not124710, #here we can change the case we look at 
                        [psi]) 
    #proof_c_conserved.premise_conserved(ts)
    proof_c_reduced = LivenessProof(prop,rank_c,rho,
                        case9, #here we can change the case we look at 
                        [psi])
    #proof_c_reduced.premise_reduced(ts) #reduced only in case9
    """

    #ranking function (d)
    #this requires a more subtle idea, similar to how we did Dijkstra's second protocol

    TwoSort, (type_left,type_right) = EnumSort('TwoSort',('type_left','type_right'))
    type_left_term = lambda *args: type_left
    type_right_term = lambda *args: type_right

    #type left encodes the part of the ranking that reduces when things move to the left m in M+m and 0 in M-m-1
    #type right encodes the part that reduces when things move to the right M in M+m and M-m-1 in M-m-1
    param_xit = {'x':Node,'i':Node,'t':TwoSort}
    
    def predicate_for_d(sym,param):
        x = param['x']
        i = param['i']
        t = param['t']
        return And(
            x!=sym['top'],
            Or(
            And(t==type_left,
                plus1mod3(sym['a'](x))==sym['a_next'](x),
                sym['leq_node'](i,x),i!=x
                ),
            And(t==type_right,
                Or(
                    plus1mod3(sym['a'](x))==sym['a_next'](x), #every i is counted for this x
                    And(
                        sym['a'](x)==plus1mod3(sym['a_next'](x)),
                        sym['leq_node'](x,i),x!=i)
    ))))
        
    i_skd = {'i':skd_term}
    i_next = {'i':next_skd_term}
    i_prev = {'i':prev_skd_term}
    t_left = {'t':type_left_term}
    t_right = {'t':type_right_term}
    hints = [i_skd | t_right, i_next | t_right, i_prev | t_right,
             i_skd | t_left, i_next | t_left, i_prev | t_left] #this is just all possible hints

    binary_d = BinaryFreeRank(predicate_for_d,param_xit)
    sum_it = ParPointwiseFreeRank(binary_d,{'i':Node,'t':TwoSort},{'x':Node},hints)
    #sum_it.print_conserved(ts)
    hint_missing = ([x_prev_skd],[x_skd],x_prev_skd)

    rank_d = ParPermFreeRank_variant(sum_it,{'x':Node},{},1,[hint0b,hint5b],[hint1b_r,hint6b_r,hint10b_r,hint_missing])
    
    """
    proof_d_conserved = LivenessProof(prop,rank_d,rho,
                        case_not12467910, #here we can change the case we look at 
                        [psi])
    #proof_d_conserved.premise_conserved(ts)
    #proof_d_conserved.premise_reduced(ts)
    """

    rank_total = LexFreeRank([rank_a,rank_b,rank_c,rank_d])

    proof = LivenessProof(prop,rank_total,rho,phi,[psi])
    proof.check_proof(ts)

        

    """
    Older tests of some weaker properties:

    #possible hints
    skd_term = lambda sym1,sym2,param1,param2: sym1['skd']
    next_skd_term = lambda sym1,*args : sym1['next_skd']
    prev_skd_term = lambda sym1,*args : sym1['prev_skd']
    top_term = lambda sym1,*args : sym1['top']
    x_to_skd = {'x':skd_term}
    x_to_next = {'x':next_skd_term}
    x_to_prev = {'x':prev_skd_term}
    x_to_top = {'x':top_term}


    #the number of privileged nodes - may increase 
    x_node = {'x':Node}
    priv_pred = lambda sym,param: priv(sym,param['x'])
    bin_priv = BinaryFreeRank(priv_pred,x_node)
    num_priv = ParPermute2FreeRank(bin_priv,x_node,{})
    


    #First test: the number of arrows is conserved in every transition except for top
    top_doesnt_move = lambda sym: sym['skd'] != sym['top']

    def right_arrow(sym,x):
        #arrow from prev(x) to x
        return And(plus1mod3(sym['a'](x))==sym['a_prev'](x),x!=sym['bot'])
    
    def left_arrow(sym,x):
        #arrow from next(x) to x
        return And(plus1mod3(sym['a'](x))==sym['a_next'](x),x!=sym['top'])

    ArrowType,(type_left, type_right) = EnumSort('ArrowType',('type_left','type_right'))

    def has_arrow_type(sym,param):
        return Or(
            And(right_arrow(sym,param['x']),param['t']==type_right),
            And(left_arrow(sym,param['x']),param['t']==type_left)
        )

    param_xt = {'x':Node,'t':ArrowType}
    binary_arrow = BinaryFreeRank(has_arrow_type,param_xt)
    num_arrows = ParPermute2FreeRank(binary_arrow,param_xt,{})

    proof = LivenessProof(prop,num_arrows,rho,top_doesnt_move,[psi]) 
    #proof.premise_conserved(ts) #succeeds in a few secs, without hints


    
    #Second attempt: y = # left-arrows + 2 # right-arrows 
    #again, not full but good as a test

    ends_dont_move = lambda sym: And(sym['skd'] != sym['bot'],sym['skd'] != sym['top'])

    ScaledArrowType, (s_type_left,s_type_right1,s_type_right2) = EnumSort('ScaledArrowType',('s_type_left','s_type_right1','s_type_right2'))
    term_left = lambda *args : s_type_left
    term_right1 = lambda *args : s_type_right1
    term_right2 = lambda *args : s_type_right2
    t_to_left = {'t':term_left}
    t_to_right1 = {'t':term_right1}
    t_to_right2 = {'t':term_right2}
    hints_t = [t_to_left,t_to_right1,t_to_right2]

    def has_scaled_arrow_type(sym,param):
        return If(param['t']==s_type_left,left_arrow(sym,param['x']),right_arrow(sym,param['x']))
    
    param_xt = {'x':Node,'t':ScaledArrowType}

    hints_x = [x_to_skd,x_to_prev,x_to_next]

    hints = list_dict_product(hints_t,hints_x)

    binary_arrow = BinaryFreeRank(has_scaled_arrow_type,param_xt)
    scaled_sum_arrows = ParPermFreeRank(binary_arrow,param_xt,{},2,
                                        [],
                                        #hints
                                        )
    #scaled_sum_arrows.print_conserved(ts)
    
    proof = LivenessProof(prop,scaled_sum_arrows,rho,ends_dont_move,[psi]) 
    #proof.premise_conserved(ts) #requires 2 permutes but the formula becomes huge with hints

    #The way we implement the hints currently is that we just give all the possible terms for every possible quantifier
    #in this case we give 3 terms for each var giving 9 term vectors for (x,t)
    #there are 4 copies of such variables so in total we get 9^4 = 6561 disjunctions. Too many
    #But really, many (most) are irrelevant or repetitive.

    #Say we consider only the normal machines, then indeed y is conserved at each transition
    #looking at the cases in Dijkstra's proof
    #1. skd,right1 + skd,right2 -> next_skd,right1 + next_skd,right2
    #2. skd,left (+next_skd,right1) -> prev_skd,left +(next_skd,right1)
    #3. skd,left + skd,right1 + skd,right2 -> none
    #4. skd,right1 + skd,right2 + next_skd,right1 + next_skd,right2 -> skd,left
    #5. skd,left + prev_skd,left -> prev_skd,right1 + prev_skd,right2
    #some of the transitions don't change the state at all then an identity permutation will suffice.
    
    skd_left = {'x':skd_term,'t':term_left}
    skd_right1= {'x':skd_term,'t':term_right1}
    skd_right2= {'x':skd_term,'t':term_right2}
    next_skd_left = {'x':next_skd_term,'t':term_left}
    next_skd_right1= {'x':next_skd_term,'t':term_right1}
    next_skd_right2= {'x':next_skd_term,'t':term_right2}
    prev_skd_left = {'x':prev_skd_term,'t':term_left}
    prev_skd_right1 = {'x':prev_skd_term,'t':term_right1}
    prev_skd_right2 = {'x':prev_skd_term,'t':term_right2}

    hint1 = ([skd_right1,skd_right2],[next_skd_right1,next_skd_right2])
    hint2 = ([skd_left,next_skd_right1],[prev_skd_left,next_skd_right1])
    hint3 = ([skd_left,skd_right1],[skd_left,skd_right1]) #identity permutation - pointwise reduction
    hint4 = ([skd_right1,skd_right2],[skd_left,skd_right2])
    hint5 = ([skd_left,prev_skd_left],[skd_right1,skd_right2])

    scaled_sum_arrows = ParPermFreeRank_variant(binary_arrow,param_xt,{},2,
                                    [],
                                    [hint1,hint2,hint3,hint4,hint5]
                                    )
    #scaled_sum_arrows.print_conserved(ts)
    proof = LivenessProof(prop,scaled_sum_arrows,rho,ends_dont_move,[psi]) 
    #proof.premise_conserved(ts)
   """
    

dijsktra3state()