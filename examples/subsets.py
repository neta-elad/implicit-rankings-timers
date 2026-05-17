"""
subsets example from Ish-Shalom, O., Itzhaky, S., Rinetzky, N., Shoham, S.: Run-time complexity bounds
using squeezers. In: Programming Languages and Systems. pp. 320–347. Springer
International Publishing, Cham (2021) https://link.springer.com/chapter/10.1007/978-3-030-72019-3_12

The program generates all subsets of {m, ..., n-1} of size k iteratively.
Note that the transition system uses actual integers, and not uninterpreted integers
because we need to compare the index to the array value. 

consider m = 2, n = 5, k = 2, the program runs as follows:
I = [ _ , _ ], j = 0, f = True -> tr_init 
I = [ 2 , _ ], j = 1, f = True -> tr_right_fill
I = [ 2 , 3 ], j = 2, f = True -> tr_start_left_scan
I = [ 2 , 3 ], j = 1, f = False -> tr_start_right_fill
I = [ 2 , 4 ], j = 2, f = True -> tr_start_left_scan
I = [ 2 , 4 ], j = 1, f = False -> tr_left_scan
I = [ 2 , 4 ], j = 0, f = False -> tr_start_right_fill
I = [ 3 , 4 ], j = 1, f = True -> tr_right_fill
I = [ 3 , 4 ], j = 2, f = True -> tr_start_left_scan
I = [ 3 , 4 ], j = 1, f = False -> tr_left_scan
I = [ 3 , 4 ], j = 0, f = False -> tr_left_scan
I = [ 3 , 4 ], j = -1, f = False - end


consider m = 2, n = 6, k = 2, the program runs as follows:
I = [ _ , _ ], j = 0, f = True -> tr_init
I = [ 2 , _ ], j = 1, f = True -> tr_right_fill
I = [ 2 , 3 ], j = 2, f = True -> tr_start_left_scan
I = [ 2 , 3 ], j = 1, f = False -> tr_start_right_fill
I = [ 2 , 4 ], j = 2, f = True -> tr_start_left_scan
I = [ 2 , 4 ], j = 1, f = False -> tr_start_right_fill
I = [ 2 , 5 ], j = 2, f = True -> tr_start_left_scan
I = [ 2 , 5 ], j = 1, f = False -> tr_left_scan
I = [ 2 , 5 ], j = 0, f = False -> tr_start_right_fill
I = [ 3 , 5 ], j = 1, f = True -> tr_right_fill
I = [ 3 , 4 ], j = 2, f = True -> tr_start_left_scan
I = [ 3 , 4 ], j = 1, f = False -> tr_start_right_fill
I = [ 3 , 5 ], j = 2, f = True -> tr_start_left_scan
I = [ 3 , 5 ], j = 1, f = False -> tr_left_scan
I = [ 3 , 5 ], j = 0, f = False -> tr_start_right_fill
I = [ 4 , 5 ], j = 1, f = True -> tr_right_fill
I = [ 4 , 5 ], j = 2, f = True -> tr_start_left_scan
I = [ 4 , 5 ], j = 1, f = False -> tr_left_scan
I = [ 4 , 5 ], j = 0, f = False -> tr_left_scan
I = [ 4 , 5 ], j = -1, f = False - end

what's interesting about this run is that the array is momentarily
set to [ 3 , 5 ] which is "out of order" - as seen by the fact that it returns later.
This is similar to what happens in the binary counter example, 
which means we also need to maintain a "ghost" array that holds the "correct" value
of the array, for example, here the first [ 3 , 5 ] is really [ 3 , 4 ]. 
In this way, the array values only increase. Alternatively, maybe we can use a "bottom" value
for array cells that are above j.
"""

from prelude import *
from typing import cast

class Subsets(TransitionSystem):
    n : Immutable[Int]
    k: Immutable[Int]
    m: Immutable[Int]
    j: Int
    I: Fun[Int, Int]
    f: Bool

    @init
    def initial_values(self) -> BoolRef:
        return And(
            self.n >= cast(Int, 0),
            self.k >= 0,
            self.m >= 0,
            self.j == 0,
            self.f == True
            # I is garbage values
        )
    
    def while_condition(self) -> BoolRef:
        return self.j >= 0

    def start_left_scan_condition(self) -> BoolRef:
        return self.j >= self.k

    @transition
    # this happens once a subset is filled - starts a left scan to find an element that is too small (I[j] < n-k+j)
    def tr_start_left_scan(self) -> BoolRef:
        return And(
            self.while_condition(),
            self.start_left_scan_condition(),

            self.f.update(false),
            self.j.update(cast(Int, self.j - 1)),
            self.I.unchanged()
        )
    
    def init_condition(self) -> BoolRef:
        return And(self.j == 0, self.f)
    
    @transition
    # this happens only once setting the first element of the array to m
    def tr_init(self) -> BoolRef:
        return And(
            self.while_condition(),
            Not(self.start_left_scan_condition()),
            self.init_condition(),

            self.f.update(true),
            self.I.update({(self.j,): self.m}),
            self.j.update(cast(Int, self.j + 1))
        )
    
    def right_fill_condition(self) -> BoolRef:
        return self.f
    
    @transition
    # this fills the array from left to right incrementing the value by one, until j>=k - where we start going left
    def tr_right_fill(self) -> BoolRef:
        return And(
            self.while_condition(),
            Not(self.start_left_scan_condition()),
            Not(self.init_condition()),
            self.right_fill_condition(),

            self.f.update(true),
            self.I.update({(self.j,): cast(Int, self.I(cast(Int, self.j - 1)) + 1)}),
            self.j.update(cast(Int, self.j + 1))
        )
    
    def left_scan_condition(self) -> BoolRef:
        return self.I(self.j) >= self.n - self.k + self.j
    
    @transition
    def tr_left_scan(self) -> BoolRef:
        return And(
            self.while_condition(),
            Not(self.start_left_scan_condition()),
            Not(self.init_condition()),
            Not(self.right_fill_condition()),
            self.left_scan_condition(),

            self.f.update(false),
            self.j.update(cast(Int, self.j - 1)),
            self.I.unchanged()
        )
    
    @transition
    def tr_start_right_fill(self) -> BoolRef:
        return And(
            self.while_condition(),
            Not(self.start_left_scan_condition()),
            Not(self.init_condition()),
            Not(self.right_fill_condition()),
            Not(self.left_scan_condition()),

            self.f.update(true),
            self.I.update({(self.j,): cast(Int, self.I(self.j) + 1)}),
            self.j.update(cast(Int, self.j + 1))
        )
    
class Termination(Prop[Subsets]):
    def prop(self) -> BoolRef:
        return false

class SubsetsProof(Proof[Subsets],prop=Termination):
    # I think the ranking needed is interesting
    # I did it at some point but i don't remember
    # but it's somehow DomLex over the array I, similarly to the binary counter.

    def rank(self) -> Rank:
        return BinRank(true)

    pass

proof = SubsetsProof()
proof.check()