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
- [x] Sanity: init is sat, every tr is sat, init & tr is sat
  - [x] Sanity failures for `examples/ticket.py` -- sanity is too strong, init & tr for every tr instead of disjunction.
- [x] Checking conserved before checking decreases
- [ ] Add DomPermPW and PW constructors
- [ ] Implementing hints for existentially quantified constructors, including soundness conditions.
- [ ] (?) Add modified argument and check to see everything is modified
- [x] (?) Printing model to file + link to model 
- [ ] models and unsat cores in a folder instead of main folder.
- [ ] (?) Bounded model-checking: given an array of formulas phi_i,
            check if there exists a trace that satisfies phi_0 
            in state 0, phi_1 in state 1, etc.
- [ ] (stretch) Integration with invariant inference algorithm
- [ ] (stretch) Sanity: show the system has infinite traces
- [ ] (stretch) Automation for finding ranking