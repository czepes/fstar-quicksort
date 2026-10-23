module Quicksort.Int.Aux

let rec length (l:list int)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let rec append (l1 l2:list int)
  : l:list int{ length l = length l1 + length l2 }
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2
