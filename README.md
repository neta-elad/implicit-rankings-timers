# Verifying First-Order Temporal Properties of Infinite States Systems via Implicit Rankings and Timers
**First ensure you have Python 3.13 on your machine**

- To install required dependencies run:
    ```shell
    make install
    ```
  
- To check type annotations run:
    ```shell
    make check
    ```
  
- To run a specific file, e.g., `examples/ticket.py`, run:
    ```shell
    make examples/ticket.py
    ```
  
- In case something goes wrong in install run:
    ```shell
    make clean 
    ```
  
- Before committing please run:
    ```shell
    make precommit
    ```
  
- To count size of an Ivy proof, e.g., `ivy_examples/ticket.ivy`, run:
    ```shell
    make measure_ivy_proof.py IVY_FILE=ivy_examples/ticket.ivy
    ```
  
For a simple example, check out the `examples/trivial_termination.py` file.

## Features
### Timeout
Set global timeout (in milliseconds) for SMT queries
with the `TIMEOUT_MS` environment variable:
```shell
TIMEOUT_MS=50 make examples/ticket.py
```

### Timers mode
Timers can be implemented either as uninterpreted sort, or by using integers.
Default mode is defined in `timers.py` (`_DEFAULT_TIMERS_MODE` variable).
Mode can be changed on the fly when running an example, 
by using the `TIMERS` environment variable with value `int` or `unint`:
```shell
TIMERS=int make examples/ticket.py
```

```shell
TIMERS=unint make examples/ticket.py
```


## TODOs
- [ ] well-foundedndess check in DomLex

## Optimizations
- [ ] Optimize the number of timers by stopping the recursion on any non-temporal formula and not only atoms, and other such optimizations.
- [ ] Better normalization, maybe pnf? For example, G(ForAll) ~ ForAll(G)
- [ ] (?) Timer semantics: inf > F(p) > 0 implies F(p) = 0

## For Artifact  
- [ ] In readme, write list of all features
- [ ] Improve formatter
- [ ] if ParamSpec of DomPW (e.g) is not one of the options, it should give an error.
- [ ] (?) add modified argument and check to see everything is modified

## More Examples we can do
- The rest of the liveness to safety examples: multi_paxos, stoppable_paxos, tlb_shootdown (huge). Possibly model paxos more accurately. 
- Motivating examples from Towards Liveness Proofs at Scale, and possibly the apple memory model (huge)
- Finish examples from implicit rankings paper - 3 other self-stabilization protocols (kind of annoying probably).
- Shunting Yard and Dutch Flag from Manna & Dershovitz paper (easy)
- Stellar Consensus Protocol: https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy
- Rabia Consensus Protocol: https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy
- Stretch: chord.

## Future Research 
- [ ] Integration with invariant inference algorithm
- [ ] Sanity: show the system has infinite traces
- [ ] Automation for finding ranking
- [ ] Often a rank decreases for some transition only if it decreases for all transitions - annoying conceptually, this is why you need to split based on state properties and not transitions, or what path in the transition took place.
