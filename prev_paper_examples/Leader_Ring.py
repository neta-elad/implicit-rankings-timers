from z3 import *
from ts import *


def ring_leader():
    
    #Leader Election in a Ring, due to Chang and Roberts
    #Chang, E.J.H., Roberts, R.: An improved algorithm for decentralized extremafinding in circular configurations of processes. 
    #Commun. ACM 22(5), 281–283 (1979), https://doi.org/10.1145/359104.359108
    #we based our modeling and invariants on
    #Feldman, Y.M.Y., Padon, O., Immerman, N., Sagiv, M., Shoham, S.:
    #Bounded quantifier instantiation for checking inductive invariants. 
    #Log. Methods Comput. Sci. 15(3) (2019), https://doi.org/10.23638/LMCS-15(3:18)2019

    print('ring_leader')

    Node = DeclareSort('Node')
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    Id = DeclareSort('Id')
    A = Const('A',Id)
    B = Const('B',Id)
    C = Const('C',Id)
    sorts = [Node,Id]

    constant_sym = {
        'skd' : Node,
        'max' : Node,
    }
    relation_sym = {
        'btw' : [Node,Node,Node],
        'leader' : [Node],
        'le' : [Id,Id],
        'pending' : [Id,Node],
        'sent_own' : [Node],
    }
    function_sym = {
        'id' : [Node,Id],
    }

    axiom_btw = lambda sym: And(
        ForAll([X,Y,Z,W],Implies(And(sym['btw'](W,X,Y),sym['btw'](W,Y,Z)),sym['btw'](W,X,Z))),
        ForAll([W,X,Y],Implies(sym['btw'](W,X,Y),Not(sym['btw'](W,Y,X)))),
        ForAll([W,X,Y],Or(sym['btw'](W,X,Y),sym['btw'](W,Y,X),W==X,W==Y,X==Y)),
        ForAll([X,Y,Z],Implies(sym['btw'](X,Y,Z),sym['btw'](Y,Z,X)))
    )
    axiom_le = lambda sym: And(
        ForAll([A,B],Implies(And(sym['le'](A,B),sym['le'](B,A)),A==B)),
        ForAll([A,B,C],Implies(And(sym['le'](A,B),sym['le'](B,C)),sym['le'](A,C))),
        ForAll([A,B],Or(sym['le'](A,B),sym['le'](B,A))),
    )
    axiom_id = lambda sym: And(
        ForAll([X,Y],Implies(And(sym['id'](X)==sym['id'](Y)),X==Y)),
        ForAll(X,sym['le'](sym['id'](X),sym['id'](sym['max'])))
    )
    axiom_size = lambda sym: Exists([X,Y,Z],And(X!=Y,Y!=Z,Z!=X,ForAll(W,Or(W==X,W==Y,W==Z))))
    
    axiom = lambda sym: And(axiom_btw(sym),axiom_le(sym),axiom_id(sym),
                            #axiom_size(sym)
                            )

    init = lambda sym: And(
        ForAll(X,sym['leader'](X) == False),
        ForAll([A,X],sym['pending'](A,X) == False),
        ForAll(X,sym['sent_own'](X)==False),
    )

    param_wakeup = {'n': Node,'succ': Node}
    tr_wakeup = lambda sym1,sym2,param: And(
        sym1['skd']==param['n'],
        param['n'] != param['succ'],
        ForAll(Z,Or(sym1['btw'](param['n'],param['succ'],Z),Z==param['n'],Z==param['succ'])),
        
        ForAll([X,Y,Z],sym2['btw'](X,Y,Z)==sym1['btw'](X,Y,Z)),
        ForAll([A,B],sym2['le'](A,B)==sym1['le'](A,B)),
        ForAll(X,sym2['id'](X)==sym1['id'](X)),
        sym2['max']==sym1['max'],

        If(sym1['sent_own'](param['n']),
           If(ForAll(A,Not(sym1['pending'](A,param['n']))),
              
              #already sent own and no pending messages -> skip
              And(
                ForAll(X,sym2['leader'](X)==sym1['leader'](X)),
                ForAll(X,sym2['sent_own'](X)==sym1['sent_own'](X)),
                ForAll([X,A],sym2['pending'](A,X)==sym1['pending'](A,X))),
              
              #there is a pending message - process message B
              Exists(B,And(
                  sym1['pending'](B,param['n']),
                  If(B==sym1['id'](param['n']),
                     
                     #B is the same as n's id -> elect n as leader
                     And(
                        ForAll(X,sym2['leader'](X)==Or(sym1['leader'](X),X==param['n'])),
                        ForAll(X,sym2['sent_own'](X)==sym1['sent_own'](X)),
                        ForAll([X,A],sym2['pending'](A,X)==And(sym1['pending'](A,X),Not(And(A==B,X==param['n']))))),
                     
                     If(sym1['le'](sym1['id'](param['n']),B),
                                   
                        #B is higher - pass forward
                        And(
                        ForAll(X,sym2['leader'](X)==sym1['leader'](X)),
                        ForAll(X,sym2['sent_own'](X)==sym1['sent_own'](X)),
                        ForAll([X,A],sym2['pending'](A,X)==Or(
                            And(sym1['pending'](A,X),Not(And(A==B,X==param['n']))),
                            And(X==param['succ'],A==B)))),

                        #B is lower - drop
                        And(
                            ForAll(X,sym2['leader'](X)==sym1['leader'](X)),
                            ForAll(X,sym2['sent_own'](X)==sym1['sent_own'](X)),
                            ForAll([X,A],sym2['pending'](A,X)==And(sym1['pending'](A,X),Not(And(A==B,X==param['n']))))),
                ))))
              ),
            
            #yet to send own id 
            And(
              ForAll(X,sym2['leader'](X)==sym1['leader'](X)),
              ForAll(X,sym2['sent_own'](X)==Or(sym1['sent_own'](X),X==param['n'])),
              ForAll([X,A],sym2['pending'](A,X)==Or(sym1['pending'](A,X),And(A==sym1['id'](param['n']),X==param['succ']))))
            )
    )
    tr1 = ['wakeup',param_wakeup,tr_wakeup]

    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    #leader_elected = lambda sym: Exists(X,sym['leader'](X))
    #pending_message = lambda sym: Exists([A,X],sym['pending'](A,X))
    #ts.bounded_check([true,true,true,true,leader_elected])

    safety = lambda sym: ForAll([X,Y],Implies(And(sym['leader'](X),sym['leader'](Y)),X==Y))
    leader_max = lambda sym: ForAll([X,Y],Implies(sym['leader'](X),sym['le'](sym['id'](Y),sym['id'](X))))
    self_pending_highest_id = lambda sym: ForAll([X,Y],Implies(sym['pending'](sym['id'](X),X),sym['le'](sym['id'](Y),sym['id'](X))))
    no_bypass = lambda sym: ForAll([X,Y,Z],Implies(
        And(sym['pending'](sym['id'](X),Y),sym['btw'](X,Z,Y)),
        sym['le'](sym['id'](Z),sym['id'](X))
    ))
    inv_safety = lambda sym: And(safety(sym),leader_max(sym),self_pending_highest_id(sym),no_bypass(sym))
    #ts.check_inductiveness(inv_safety)
    #ts.check_inductiveness(no_bypass)

    r = lambda sym,param : param['n'] == sym['skd']
    sort_dict = {'n' : Node}
    p = lambda sym: True
    q = lambda sym: Exists(X,sym['leader'](X))
    prop = LivenessProperty(p,q,[r],[sort_dict])

    
    rho = lambda sym: And(
        #ForAll([X,Y],Implies(sym['pending'](sym['id'](X),Y),sym['sent_own'](X))),
        #inv_safety(sym),
        ForAll([A,X],Implies(sym['pending'](A,X),
                             Exists(Y,sym['id'](Y)==A)) ),
        Or(
            q(sym),
            Exists(X,Not(sym['sent_own'](X))),
            Exists([X,Y],sym['pending'](sym['id'](Y),X))
        ),
        ForAll(X,Implies(And(sym['sent_own'](X),Not(sym['leader'](X))),
            Exists(Y,Or( #quantifier alteration that is hard 
                Not(sym['le'](sym['id'](Y),sym['id'](X))),
                sym['pending'](sym['id'](X),Y))))
        )
    )
    phi = lambda sym: And(
        Not(q(sym)),
        rho(sym)   
    )
    psi = lambda sym,param: Or(
        Not(sym['sent_own'](param['n'])),
        Exists(X,sym['pending'](sym['id'](X),param['n']))
    )

    n1_dict = {'n1':Node}
    n2_dict = {'n2':Node}
    n1n2_dict = n1_dict | n2_dict
    pred_pending_n1n2 = lambda sym,param: sym['pending'](sym['id'](param['n1']),param['n2']) 
    pred_sent_n2 = lambda sym,param : Not(sym['sent_own'](param['n2']))
    pred_sent_max = lambda sym,param: Not(sym['sent_own'](sym['max']))

    #extracting an order from the ring structure, such that max is maximal.
    less_btw_n2_by_max = lambda sym,param1,param2: Or(
        sym['btw'](param1['n2'],param2['n2'],sym['max']),
        And(param2['n2']==sym['max'],param1['n2']!=sym['max'])) 

    rank_bin_pending = BinaryFreeRank(pred_pending_n1n2,n1n2_dict)
    rank_agg_pending = ParPointwiseFreeRank(rank_bin_pending,{'n1':Node},n2_dict) #n2 is still free
    rank_bin_sent_n2 = BinaryFreeRank(pred_sent_n2,n2_dict)
    rank_n2 = LexFreeRank([rank_bin_sent_n2,rank_agg_pending],n2_dict)
    rank_agg_n2 = ParLexFreeRank(rank_n2,n2_dict,less_btw_n2_by_max)
    rank_bin_sent_max = BinaryFreeRank(pred_sent_max)
    rank1 = LexFreeRank([rank_bin_sent_max,rank_agg_n2])

    proof1 = LivenessProof(prop,rank1,rho,phi,[psi])
    #proof1.check_proof(ts)  

    #Alternative ranking, a little nicer 
    #This is the one I use in the paper
    rank_agg_pending_both = ParLexFreeRank(rank_bin_pending,n1n2_dict,less_btw_n2_by_max)
    rank_agg_sent = ParPointwiseFreeRank(rank_bin_sent_n2,n2_dict)
    rank2 = LexFreeRank([rank_agg_sent,rank_agg_pending_both])
    
    proof2 = LivenessProof(prop,rank2,rho,phi,[psi])
    proof2.check_proof(ts)

ring_leader()

def ring_leader_without_messages():
    
    #this is a different modeling that they used in 
    #Chih-Duo Hong and Anthony W. Lin. 2024. 
    #Regular Abstractions for Array Systems. 
    #Proc. ACM Program. Lang. 8, POPL, Article 22 (January 2024), 29 pages. https://doi.org/10.1145/3632864
    #it is less natural in our mind, we didn't manage to verify it, but probably due to issues in the premises of the rule that do not involve ranking

    print('ring_leader_without_messages')

    true = lambda sym: True 

    Node = DeclareSort('Node')
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    Id = DeclareSort('Id')
    A = Const('A',Id)
    B = Const('B',Id)
    C = Const('C',Id)
    sorts = [Node,Id]

    constant_sym = {
        'skd' : Node,
        'max' : Node,
        'zero' : Id,
    }
    relation_sym = {
        'btw' : [Node,Node,Node],
        'leader' : [Node],
        'le' : [Id,Id],
        'sent_own' : [Node],
    }
    function_sym = {
        'id' : [Node,Id],
        'msg' : [Node,Id] #instead of a message relation we have a function
    }

    axiom_btw = lambda sym: And(
        ForAll([X,Y,Z,W],Implies(And(sym['btw'](W,X,Y),sym['btw'](W,Y,Z)),sym['btw'](W,X,Z))),
        ForAll([W,X,Y],Implies(sym['btw'](W,X,Y),Not(sym['btw'](W,Y,X)))),
        ForAll([W,X,Y],Or(sym['btw'](W,X,Y),sym['btw'](W,Y,X),W==X,W==Y,X==Y)),
        ForAll([X,Y,Z],Implies(sym['btw'](X,Y,Z),sym['btw'](Y,Z,X)))
    )
    axiom_le = lambda sym: And(
        ForAll([A,B],Implies(And(sym['le'](A,B),sym['le'](B,A)),A==B)),
        ForAll([A,B,C],Implies(And(sym['le'](A,B),sym['le'](B,C)),sym['le'](A,C))),
        ForAll([A,B],Or(sym['le'](A,B),sym['le'](B,A))),
        ForAll(A,sym['le'](sym['zero'],A))
    )
    axiom_id = lambda sym: And(
        ForAll([X,Y],Implies(And(sym['id'](X)==sym['id'](Y)),X==Y)),
        ForAll(X,sym['id'](X)!=sym['zero']),
        ForAll(X,sym['le'](sym['id'](X),sym['id'](sym['max'])))
    )    
    axiom = lambda sym: And(axiom_btw(sym),axiom_le(sym),axiom_id(sym))

    init = lambda sym: And(
        ForAll(X,sym['leader'](X) == False),
        ForAll(X,sym['sent_own'](X)==False),
        ForAll(X,sym['msg'](X)==sym['zero'])
    )

    def send_own(sym1,sym2,i,iplus1):
        return And(
            ForAll(X,sym2['leader'](X)==sym1['leader'](X)),
            sym2['sent_own'](i)==True,
            ForAll(X,Implies(X!=i,sym2['sent_own'](X)==sym1['sent_own'](X))),
            If(sym1['le'](sym1['msg'](iplus1),sym1['id'](i)),And(
                   #pass id forward
                   sym2['msg'](iplus1)==sym1['id'](i),
                   ForAll(X,Implies(X!=iplus1,sym2['msg'](X)==sym1['msg'](X))))
                   ,
                   #dont pass id forward
                   ForAll(X,sym2['msg'](X)==sym1['msg'](X))
               )
        )
    
    def process_msg(sym1,sym2,i,iplus1):
        return And(
            ForAll(X,sym2['sent_own'](X)==sym1['sent_own'](X)),
            If(sym1['msg'](i)==sym1['id'](i),
               ForAll(X,sym2['leader'](X)==Or(sym1['leader'](X),X==i)),
               ForAll(X,sym2['leader'](X)==sym1['leader'](X))),
            If(And(sym1['le'](sym1['msg'](iplus1),sym1['msg'](i)),sym1['le'](sym1['id'](i),sym1['msg'](i))),
                  And(
                   sym2['msg'](iplus1)==sym1['msg'](i),
                   sym2['msg'](i)==sym1['zero'],
                   ForAll(X,Implies(And(X!=iplus1,X!=i),sym2['msg'](X)==sym1['msg'](X))),
                  ),
                  And(
                   sym2['msg'](i)==sym1['zero'],
                   ForAll(X,Implies(X!=i,sym2['msg'](X)==sym1['msg'](X))),
                  ))
        )
    
    param_wakeup = {'n': Node,'succ': Node}
    tr_wakeup = lambda sym1,sym2,param: And(
        #not total as a relation - missing idle
        sym1['skd']==param['n'],
        param['n'] != param['succ'],
        ForAll(Z,Or(sym1['btw'](param['n'],param['succ'],Z),Z==param['n'],Z==param['succ'])),
        
        ForAll([X,Y,Z],sym2['btw'](X,Y,Z)==sym1['btw'](X,Y,Z)),
        ForAll([A,B],sym2['le'](A,B)==sym1['le'](A,B)),
        ForAll(X,sym2['id'](X)==sym1['id'](X)),
        sym2['max']==sym1['max'],
        sym2['zero']==sym1['zero'],

        If(Not(sym1['sent_own'](param['n'])),
            send_own(sym1,sym2,param['n'],param['succ']),
            process_msg(sym1,sym2,param['n'],param['succ']))
    )
    tr1 = ['wakeup',param_wakeup,tr_wakeup]

    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    leader_elected = lambda sym: Exists(X,sym['leader'](X))
    pending_message = lambda sym: Exists([A,X],sym['pending'](A,X))
    #ts.bounded_check([true,true,true,true,leader_elected])

    safety = lambda sym: ForAll([X,Y],Implies(And(sym['leader'](X),sym['leader'](Y)),X==Y))
    leader_max = lambda sym: ForAll([X,Y],Implies(sym['leader'](X),sym['le'](sym['id'](Y),sym['id'](X))))
    self_pending_highest_id = lambda sym: ForAll([X,Y],Implies(sym['msg'](X)==sym['id'](X),sym['le'](sym['id'](Y),sym['id'](X))))
    no_bypass = lambda sym: ForAll([X,Y,Z],Implies(
        And(sym['msg'](Y)==sym['id'](X),sym['btw'](X,Z,Y)),
        sym['le'](sym['id'](Z),sym['id'](X))))
    #msg_prop = lambda sym: ForAll(X,Or(sym['msg'](X)==sym['zero'],sym['le'](sym['id'](X),sym['msg'](X))))

    inv_safety = lambda sym: And(no_bypass(sym),self_pending_highest_id(sym),leader_max(sym),safety(sym))
    #ts.check_inductiveness(inv_safety)

    r = lambda sym,param : param['n'] == sym['skd']
    sort_dict = {'n' : Node}
    p = lambda sym: True
    q = lambda sym: Exists(X,sym['leader'](X))
    q_strong = lambda sym: sym['leader'](sym['max'])
    prop = LivenessProof(p,q_strong,[r],[sort_dict])

    rho = lambda sym: And(
        #inv_safety(sym),
        ForAll(X,Or(Exists(Y,sym['msg'](X)==sym['id'](Y)),sym['msg'](X)==sym['zero'])),
        Or(q(sym),
            Not(sym['sent_own'](sym['max'])),
            Exists(X,sym['msg'](X)==sym['id'](sym['max']))),
        ForAll(X,Implies(And(sym['sent_own'](X),Not(sym['leader'](X))),
            Exists(Y,Or(
                Not(sym['le'](sym['id'](Y),sym['id'](X))),
                sym['msg'](Y)==sym['id'](X) )))),
        ForAll(X,Implies(sym['msg'](X)==sym['id'](sym['max']),sym['sent_own'](sym['max']))),
        #ForAll(X,Implies(sym['leader'](X),Or(sym['msg'](X)==sym['id'](X),sym['msg'](X)==sym['zero'])))
    ) 
    phi = lambda sym : And(rho(sym),p(sym),Not(q_strong(sym)))
    psi = lambda sym,param : Or(And(param['n']==sym['max'],Not(sym['sent_own'](sym['max']))),
                                sym['msg'](param['n'])==sym['id'](sym['max']))
    

