# Implicit Rankings with Timers
This is the Python library accompanying the
TACAS 2026 paper
"*Verifying First-Order Temporal Properties of
Infinite-State Systems via Timers and Rankings*"
by Raz Lotan, Neta Elad, Oded Padon and Sharon Shoham.
It allows for easy, type-safe definitions of transition systems
and temporal properties,
and constructing proofs using implicit rankings and timers.

## Getting Started
All necessary symbols are re-exported from the `prelude` 
module, so you can start by simply writing:
```python
from prelude import *
```
## Environment variables
The library uses two environment variable 
to configure high-level behavior:
- `TIMERS`, sets timers mode (see [`timers`](timers.html)).
- `TIMEOUT_MS`, sets global timeout in milliseconds *per SMT query*.
