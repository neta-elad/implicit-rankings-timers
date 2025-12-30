# Verifying First-Order Temporal Properties of Infinite States Systems via Implicit Rankings and Timers

This repository contains the implementation of the methods described the paper 
"Verifying First-Order Temporal Properties of Infinite States Systems via Implicit Rankings and Timers" 
by Raz Lotan, Neta Elad, Oded Padon and Sharon Shoham. 
The tool allows encoding a transition system specified in first-order logic, 
and verifying first-order temporal properties of it. 
The verification is done via the timer reduction (Section 4),
that reduces the verification of temporal properties to the verification of termination. 
Termination is then verified with the use of implicit rankings and invariants (Section 5).

## Using the Artifact Image
Download the appropriate Docker image from 
<https://doi.org/10.5281/zenodo.18094939>, 
and load it by running:
```shell
docker load -i artifact-<platform>.tar.gz
```
where `<platform>` is either `arm64` (for Mac M1/M2/M3)
or `amd64`.

Then run it with:
```shell
docker run artifact-<platform> make all
```

You can run a specific example with:
```shell
docker run artifact-<platform> make examples/ticket.py
```

## Running the Code Locally

**First ensure you have Python 3.13 on your machine**

- Get a copy of the source code by running:
    ```shell
    git clone git@github.com:neta-elad/implicit-rankings-timers.git && cd implicit-rankings-timers
    ```

- To install required dependencies run:
    ```shell
    make install
    ```

- To run all examples, run:
    ```shell
    make all
    ```
  
- To run a specific file, e.g., `examples/ticket.py`, run:
    ```shell
    make examples/ticket.py
    ```

- Open full docs by running
    ```shell
    make docs/out-open
    ```
  
- To check type annotations run:
    ```shell
    make check
    ```

- In case something goes wrong in install run:
    ```shell
    make clean 
    ```

- To count size of an Ivy proof, e.g., `ivy_examples/ticket.ivy`, run:
    ```shell
    make measure_ivy_proof.py IVY_FILE=ivy_examples/ticket.ivy
    ```

## Features
### Timeout
Set global timeout (in milliseconds) for SMT queries
with the `TIMEOUT_MS` environment variable:
```shell
make examples/ticket.py TIMEOUT_MS=50
```

### Timers mode
Timers can be implemented either as uninterpreted sort, or by using integers.
Default mode is defined in `timers.py` (`_DEFAULT_TIMERS_MODE` variable).
Mode can be changed on the fly when running an example, 
by using the `TIMERS` environment variable with value `int` or `unint`:
```shell
make examples/ticket.py TIMERS=int
```

```shell
make examples/ticket.py TIMERS=unint
```

## TODOs

### Cleanup

- Review size of proof, e.g why does DomLex not count the size of the order relation?

### Optimizations
- [ ] Optimize the number of timers by stopping the recursion on any non-temporal formula and not only atoms.
- [ ] Better normalization, maybe pnf? For example, G(ForAll) ~ ForAll(G).
- [ ] Axioms that may eliminate spurious phantom states, e.g. t_(p and q) >= t_p, t_q.

### Examples
- Clean up paxos: review weird assumption and weird timeout.
- review Dijsktra k-state - why does it work without temporal invariant?
- multi_paxos, stoppable_paxos.
- Examples from implicit rankings: 3 other self-stabilization protocols.
- Challenging future examples: TLB Shootdown, Sliding Window, Stellar Consensus Protocol, Chord, Apple Memory model
