# TODOs / Future Work

## Optimizations
- Optimize the number of timers by stopping the recursion on any non-temporal formula and not only atoms.
- Better normalization, maybe pnf? For example, G(ForAll) ~ ForAll(G).
- Axioms that may eliminate spurious phantom states, e.g. t_(p and q) >= t_p, t_q.
- Assume in post-state for invariants
- A "Decreasing Counter-Abstraction" for timers: instead of encoding timers as natural numbers consider only 0, fin, inf, but such that timers still decrease between two copies of fin in transitions. Maybe this improves performance? should be sound.

## Aesthetics

- when printing a rank, do not print formulas, only constructors and names of formulas, currently this is inconsistent.

## More Examples
- From L2S: stoppable_paxos, TLB shootdown (perhaps there was a bug in the original proof?)
- From Liveness to Safety for Distributed Systems: Spanning Tree, Leader Election, Maximal Independent Set.ֿ
- From Runtime squeezers: subsets, monotone sequences.
- From first implicit rankings paper: other Dijkstra 3-State, Dijkstra 4-State, Ghosh. (These require annoying abstraction details and offer no new insights)
- Challenging future examples: Sliding Window, Stellar Consensus Protocol, Chord, Apple Memory model
