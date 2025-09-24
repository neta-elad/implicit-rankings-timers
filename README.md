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

## TODOs
- [ ] Many examples TODO
- [ ] Implementing hints for existentially quantified constructors, including soundness conditions.
    DomPW 
    [{}, {}, {}] - options for exists y disjunctively
    DomPermPW
    [ ([{},{}] , [{},{}], {}), ([{},{}] , [{},{}], {}) ]
    Soundness
    [ [{},{}] , [{},{}] ]
- [ ] In readme, write list of all features
- [ ] More informative soundness failures, if a relation is not declared WF it just says "Checking soundness: failed", for Pos the sort being finite should also suffice.
- [ ] Improve formatter"
- [ ] differentiate timeouts and violations in printing
- [ ] Timer Semantics: add that always transitions of inf->inf, F(p) > 0 implies F(p) = 0?
- [ ] (?) splitting checks for different cases 
- [ ] (?) Add modified argument and check to see everything is modified
- [ ] (?) Can we reuse invariants in diff proofs?
- [ ] (stretch) ability to write unit tests for a spec
- [ ] (stretch) Integration with invariant inference algorithm
- [ ] (stretch) Sanity: show the system has infinite traces
- [ ] (stretch) Automation for finding ranking
