# Verifying First-Order Temporal Properties of Infinite States Systems via Implicit Rankings and Timers

This repository contains the implementation of the methods described 
in the TACAS 2026 paper 
"Verifying First-Order Temporal Properties of Infinite States Systems via Implicit Rankings and Timers" 
by Raz Lotan, Neta Elad, Oded Padon and Sharon Shoham. 
The tool allows encoding a transition system specified in first-order logic, 
and verifying first-order temporal properties of it. 
The verification is done via the timer reduction (Section 4),
that reduces the verification of temporal properties to the verification of termination. 
Termination is then verified with the use of implicit rankings and invariants (Section 5).

The complete docs for how to use the Python library are available at
<https://neta-elad.github.io/implicit-rankings-timers/>,
but can also be built locally (see below).

## Using the Artifact Image
Download the appropriate Docker image from 
<https://doi.org/10.5281/zenodo.18094938>, 
and load it by running:
```shell
docker load -i artifact-<platform>.tar.gz
```
where `<platform>` is either `arm64` (for Mac M1/M2/M3)
or `amd64`.

Then run it with:
```shell
docker run artifact-<platform> make all QUIET=true
```

You can run a specific example with:
```shell
docker run artifact-<platform> make examples/ticket.py QUIET=true
```

To get full log of a run, simply remove the `QUITE=true` environment variable.

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

- Build docs locally and open them by running
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

- To count size of an Ivy proof, e.g., `ivy_files/ticket.ivy`, run:
    ```shell
    make measure_ivy_proof.py IVY_FILE=ivy_files/ticket.ivy
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

### Quiet mode
To print the results a run in a compact format (akin to Table 2 of the paper),
use the flag `QUIET=true`:
```shell
make examples/ticket.py QUIET=true
```