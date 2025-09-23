from z3 import *
from ts import *

def backprop_fixed_order():

    #A backpropogation algorithm for CNF-solving
    #fix an order on variables, and construct a partial assignment
    #at each step make a decision on the current variable
    #then if the current assignment satisfies all clauses output it
    #if there exists a clause that cant be satisfied backpropogate one step
    
    print('sat_backtracking')

    Variable = DeclareSort('Variable')
    Clause = DeclareSort('Clause')
    X = Const('X',Variable)
    Y = Const('Y',Variable)
    Z = Const('Z',Variable)
    W = Const('W',Variable)
    C = Const('C',Clause)
    D = Const('D',Clause)
    b = Const('b',BoolSort())
    tt = BoolVal(True)
    ff = BoolVal(False)

    sorts = [Variable,Clause]
    
    constant_sym = {
        'curr_var' : Variable,
        'dummy_leaf' : Variable, #assignments to dummy_leaf are meaningless and its last in order
        'dummy_root' : Variable, #assignments to dummy_root are meanings and its first in order
        'sat' : BoolSort(),
        'unsat' : BoolSort()
    }
    relation_sym = {
        'var_order' : [Variable,Variable],
        'curr_assignment' : [Variable,BoolSort()],
        'appears' : [Clause,Variable,BoolSort()] #where false stands for the negation
    }
    function_sym = {
    }

    succ = lambda sym,x,y: And(   
        x!=y,sym['var_order'](x,y),
        ForAll(Z,Implies(sym['var_order'](x,Z),Or(Z==x,sym['var_order'](y,Z))))
    )
    order_axiom = lambda sym: And(
        ForAll([X,Y],Implies(And(sym['var_order'](X,Y),sym['var_order'](Y,X)),X==Y)),
        ForAll([X,Y,Z],Implies(And(sym['var_order'](X,Y),sym['var_order'](Y,Z)),sym['var_order'](X,Z))),
        ForAll([X,Y],Or(sym['var_order'](X,Y),sym['var_order'](Y,X))),
        ForAll(X,sym['var_order'](X,sym['dummy_leaf'])),
        ForAll(X,sym['var_order'](sym['dummy_root'],X))
    )
    axiom = lambda sym: And(order_axiom(sym),
                            ForAll([C,b],Not(sym['appears'](C,sym['dummy_leaf'],b))),
                            ForAll([C,b],Not(sym['appears'](C,sym['dummy_root'],b))))
    
    def init(sym):
        return And(
            succ(sym,sym['dummy_root'],sym['curr_var']), #curr_var is initialized to the second minimal value
            ForAll([X,b],sym['curr_assignment'](X,b)==False),
            Not(sym['sat']),
            Not(sym['unsat'])
        )
    
    def immutable(sym1,sym2):
        return And(
            ForAll([X,Y],sym2['var_order'](X,Y)==sym1['var_order'](X,Y)),
            ForAll([C,X,b],sym2['appears'](C,X,b)==sym1['appears'](C,X,b)),
            sym2['dummy_leaf']==sym1['dummy_leaf']
        )
    
    def increase_curr_var(sym1,sym2):
        return succ(sym1,sym1['curr_var'],sym2['curr_var'])
    
    def decrease_curr_var(sym1,sym2):
        return succ(sym1,sym2['curr_var'],sym1['curr_var'])
    
    def curr_var_unchanged(sym1,sym2):
        return sym2['curr_var']==sym1['curr_var']
    
    def curr_assignment_unchanged(sym1,sym2):
        return ForAll([X,b],sym2['curr_assignment'](X,b)==sym1['curr_assignment'](X,b))

    def update_curr_assignment(sym1,sym2,var,value):
        return And(
            sym2['curr_assignment'](var,value),
            Not(sym2['curr_assignment'](var,Not(value))),
            ForAll([X,b],Implies(X!=var,sym2['curr_assignment'](X,b)==sym1['curr_assignment'](X,b))),
        )
    
    def remove_assignment_var(sym1,sym2,var):
        return ForAll([X,b],sym2['curr_assignment'](X,b)==And(sym1['curr_assignment'](X,b),X!=var))
        
    def result_unchanged(sym1,sym2):
        return And(
            sym2['sat']==sym1['sat'],
            sym2['unsat']==sym1['unsat']
        ) 
    
    #we always start by assigning 1 and then assigning 0
    param = {}
    def tr(sym1,sym2,param):
        curr_assignment = sym1['curr_assignment']
        curr_var = sym1['curr_var']
        appears = sym1['appears']
        return And(
            immutable(sym1,sym2),
            Not(sym1['sat']),
            Not(sym1['unsat']),
            Or(
                And(
                    #current variable is not assigned - assign true
                    curr_var != sym1['dummy_leaf'],
                    curr_var != sym1['dummy_root'],
                    ForAll(b,Not(curr_assignment(curr_var,b))), 
                    update_curr_assignment(sym1,sym2,curr_var,tt),
                    increase_curr_var(sym1,sym2),
                    result_unchanged(sym1,sym2)
                ),
                And(
                    #variable was assigned true - assign false
                    curr_var != sym1['dummy_leaf'],
                    curr_var != sym1['dummy_root'],
                    curr_assignment(curr_var,tt), 
                    update_curr_assignment(sym1,sym2,curr_var,ff),
                    increase_curr_var(sym1,sym2),
                    result_unchanged(sym1,sym2)
                ),
                And(
                    #Found a clause where for every literal the corresponding var is assigned to the negated literal - backprop
                    Exists(C,ForAll([X,b],Implies(appears(C,X,b),curr_assignment(X,Not(b))))),
                    decrease_curr_var(sym1,sym2),
                    remove_assignment_var(sym1,sym2,curr_var),
                    result_unchanged(sym1,sym2)
                ),
                And(
                    #variable was assigned false - backprop and remove assignment
                    curr_assignment(curr_var,ff), 
                    decrease_curr_var(sym1,sym2),
                    remove_assignment_var(sym1,sym2,curr_var),
                    result_unchanged(sym1,sym2)
                ),
                And(
                    #all clauses have a satisfying assignment - return sat
                    ForAll(C,Exists([X,b],And(appears(C,X,b),curr_assignment(X,b)))),
                    curr_var_unchanged(sym1,sym2),
                    curr_assignment_unchanged(sym1,sym2),
                    sym2['sat'],
                    sym2['unsat']==sym1['unsat']
                ),
                And(
                    #current var backtracked to root - return unsat
                    curr_var == sym1['dummy_root'],
                    curr_var_unchanged(sym1,sym2),
                    curr_assignment_unchanged(sym1,sym2),
                    sym2['unsat'],
                    sym2['sat']==sym1['sat'],   
                )
            )
        )
    
    tr1 = ('assign',param,tr)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    #ts.bounded_check([true,true])

    def unassigned(sym,var):
        curr_assignment = sym['curr_assignment']
        return And(Not(curr_assignment(var,tt)),Not(curr_assignment(var,ff)))

    def inv(sym):
        curr_assignment = sym['curr_assignment']
        curr_var = sym['curr_var']
        appears = sym['appears']
        root = sym['dummy_root']
        leaf = sym['dummy_leaf']
        return And(
            ForAll(X,Not(And(curr_assignment(X,tt),curr_assignment(X,ff)))),
            Implies(sym['sat'],ForAll(C,Exists([X,b],And(appears(C,X,b),curr_assignment(X,b))))),
            unassigned(sym,root),
            unassigned(sym,leaf),
            ForAll(X,Implies(And(sym['var_order'](curr_var,X),curr_var!=X),
                             unassigned(sym,X))),
            ForAll(X,Implies(And(sym['var_order'](X,curr_var),X!=curr_var,X!=root),
                             Not(unassigned(sym,X)))),
            Not(And(sym['sat'],sym['unsat']))
        )
    
        
    def termination(sym):
        return Or(sym['sat'],sym['unsat'])

    r = true
    p = true 
    q = termination
    prop = LivenessProperty(p,q,[r],[{}])

    rho = inv 
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = true

    #ranking argument:
    #similar to binary counter example, but a bit more complicated
    #the current partial assignment is complicated to a full assignment in the following manner:
    #if we are in a forward search (current var is anassigned) interpret unassigned variables as T
    #if we are in a backward search (current var is assigned) interpret unassgiend variables as F
    #not sure about edge cases
    #additionally we keep track of the number of variables assigned True - we have reduction when this increases
    #and the number of variables assigned False - we have reduction when this decreases

    v_dict = {'v':Variable}
    #the first component
    def forward(sym):
        return And(unassigned(sym,sym['curr_var']),sym['curr_var']!=sym['dummy_root'])

    def ghost_assignment(sym,param):
        v = param['v']
        curr_assign = sym['curr_assignment']
        curr_var = sym['curr_var']
        return And(
            v != sym['dummy_leaf'],
            v != sym['dummy_root'],
            Or(
                curr_assign(v,tt),
                And(forward(sym),unassigned(sym,v),sym['var_order'](curr_var,v))
            )
        )
    
    strict_order = lambda sym1,param1,param2: And(sym1['var_order'](param1['v'],param2['v']),param1['v']!=param2['v'])
    rank1 = ParLexFreeRank(BinaryFreeRank(ghost_assignment,v_dict),v_dict,strict_order)

    #the second component
    def assigned_not_true(sym,param):
        return Not(sym['curr_assignment'](param['v'],tt))  

    def assigned_false(sym,param):
        return sym['curr_assignment'](param['v'],ff)
    num_not_true = ParPointwiseFreeRank(BinaryFreeRank(assigned_not_true,v_dict),v_dict)
    num_false = ParPointwiseFreeRank(BinaryFreeRank(assigned_false,v_dict),v_dict)
    rank2 = PointwiseFreeRank([num_not_true,num_false])

    #the third component 
    def curr_is_leaf(sym,param):
        return sym['curr_var']==sym['dummy_leaf']
    rank3 = BinaryFreeRank(curr_is_leaf)

    rank = LexFreeRank([rank1,rank2,rank3])
    
    proof = LivenessProof(prop,rank,rho,phi,[psi])
    proof.check_proof(ts)


backprop_fixed_order()