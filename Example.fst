module Example
module W = Quicksort.Int.Weak
module S = Quicksort.Int.Strong

// Type and refinement
type nat = i:int{ i >= 0 }

let _ = assert(forall(n:nat) . n >= 0)
let _ = assert(~(exists(n:nat) . n < 0))

// Function type
let incr (x:nat)
  : y:nat { y > x }
  = x + 1

// List
let empty = []
let ints: list int = [3; 1; 4]
//         head :: tail
let vals = 0    :: ints

let _ = assert (vals == [0; 3; 1; 4])

let l = [2; 1; 2; 1]
let ws = [1; 1; 1; 2]

let _ = assert(W.prop1 ws /\ W.prop2 l ws)

let ss = [1; 1; 2; 2]

// let _ = assert(S.prop1 ws /\   S.prop2 l ws )
let _ = assert(S.prop1 ws /\ ~(S.prop2 l ws))
let _ = assert(S.prop1 ss /\   S.prop2 l ss )
