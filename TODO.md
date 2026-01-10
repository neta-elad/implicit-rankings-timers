# TODOs / Future Work

## Optimizations
- Optimize the number of timers by stopping the recursion on any non-temporal formula and not only atoms.
- Better normalization, maybe pnf? For example, G(ForAll) ~ ForAll(G).
- Axioms that may eliminate spurious phantom states, e.g. t_(p and q) >= t_p, t_q.
- Assume in post-state for invariants

## Aesthetics

- when printing a rank, do not print formulas, only constructors and names of formulas, currently this is inconsistent.

## More Examples
- From L2S: multi_paxos, stoppable_paxos.
- From Implicit Rankings: other Dijkstra 3-State, Dijkstra 4-State, Ghosh.
- From Liveness to Safety for Distributed Systems: Spanning Tree, Leader Election, Maximal Independent Set.
- Challenging future examples: TLB Shootdown, Sliding Window, Stellar Consensus Protocol, Chord, Apple Memory model