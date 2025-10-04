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
- [ ] prove all examples.
- [ ] test out hints
- [ ] make sure DomPerm is not buggy
- [ ] DomLex generalize to allow formulas that aren't necessarily relations, like last paper.
- [ ] Timer Semantics: add that always transitions of inf->inf, F(p) > 0 implies F(p) = 0
- [ ] Add method for counting the number of constructors in a rank - timerRank should be +1.
- [ ] In readme, write list of all features
- [ ] (optional) differentiate timeouts and violations in printing
- [ ] (optional) improve formatter
- [ ] (optional) option to compute quantifier structure for calls
- [ ] (?) splitting checks for different cases 
- [ ] (?) add modified argument and check to see everything is modified
- [ ] (?) reusing invariants and ranks between proofs
- [ ] (?) sometimes a rank decreases for some transition only if it decreases for all transitions - annoying conceptually
- [ ] (stretch) ability to write unit tests for a spec
- [ ] (stretch) Integration with invariant inference algorithm
- [ ] (stretch) Sanity: show the system has infinite traces
- [ ] (stretch) Automation for finding ranking
