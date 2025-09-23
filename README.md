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
- [ ] Fix broken / slow examples
  - [ ] Toy stabilization
  - [ ] Ring leader
  - [ ] Ackerman
- [x] Give prop unnegated and do NNF whenever a timer is used
- [x] Add option to track more temporal formulas in the timer system
- [x] witnesses for temporal formulas (skolemization) - related to above
- [ ] Implementing hints for existentially quantified constructors, including soundness conditions.
- [x] State witnesses (mutable)
- [ ] In readme, write list of all features
- [ ] Improve formatter
- [ ] differentiate timeouts and violations in printing
- [x] Remove .update() function - it's confusing, or make better update function for updating just one relation/function value
- [ ] Timer Semantics: add that always transitions of inf->inf, F(p) > 0 implies F(p) = 0?
- [ ] (?) Add modified argument and check to see everything is modified
- [ ] (?) Can we reuse invariants in diff proofs?
- [ ] (stretch) ability to write unit tests for a spec
- [ ] (stretch) Integration with invariant inference algorithm
- [ ] (stretch) Sanity: show the system has infinite traces
- [ ] (stretch) Automation for finding ranking
