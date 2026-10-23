module Quicksort.Generic.Aux

let rec length #t (l:list t)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let rec append #t (l1 l2:list t)
  : list t
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

let rec count (#t:eqtype) (x:t) (l:list t)
  : nat
  = match l with
    | [] -> 0
    | hd :: tl -> (if hd = x then 1 else 0) + count x tl

let total_order (#t:Type) (f: t -> t -> bool)
  = (forall a . f a a)                                 // reflexivity
    /\ (forall a1 a2 . (f a1 a2 /\ f a2 a1) ==> a1 == a2) // anti-symmetry
    /\ (forall a1 a2 a3 . f a1 a2 /\ f a2 a3 ==> f a1 a3) // transitivity
    /\ (forall a1 a2 . f a1 a2 \/ f a2 a1)               // totality
let total_order_t (t:Type) = f:(t -> t -> bool) { total_order f }
