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
- [ ] Add DomPermPW and PW constructors
  - [x] DomPermPW: take from previous paper + minimal&soundness is like DomPW
  - [ ] PW: take from previous paper + minimal&soundness like Lex
- [ ] Give prop unnegated and do NNF whenever a timer is used
- [ ] Implementing hints for existentially quantified constructors, including soundness conditions.
- [ ] In readme, write list of all features
- [ ] Improve formatter
- [ ] differentiate timeouts and violations in printing
- [ ] (?) Remove .update() function - it's confusing, or make better update function for updating just one relation/function value
- [ ] (?) Timer Semantics: add that always transitions of inf->inf, F(p) > 0 implies F(p) = 0?
- [ ] (?) Add modified argument and check to see everything is modified
- [ ] (?) Add option to track more temporal formulas in the timer system
- [ ] (?) witnesses for temporal formulas (skolemization) - related to above
- [ ] (?) State witnesses (mutable)
- [ ] (?) Can we reuse invariants in diff proofs?
- [ ] (?) Bounded model-checking: given an array of formulas phi_i,
            check if there exists a trace that satisfies phi_0 
            in state 0, phi_1 in state 1, etc.
- [ ] (stretch) ability to write unit tests for a spec
- [ ] (stretch) Integration with invariant inference algorithm
- [ ] (stretch) Sanity: show the system has infinite traces
- [ ] (stretch) Automation for finding ranking
