module Quicksort.Int.Weak

include Quicksort.Int.Aux
include Quicksort.Int.Impl

let rec sorted (l:list int)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> x <= y && sorted (y :: xs)

let rec mem (i:int) (l:list int)
  : bool
  = match l with
    | [] -> false
    | hd :: tl -> hd = i || mem i tl

let rec partition_mem (f:int -> bool)
                      (l:list int)
  : Lemma (let hi, lo = partition f l in
           (forall x. mem x hi ==> f x) /\
           (forall x. mem x lo ==> not (f x)) /\
           (forall x. mem x l = (mem x hi || mem x lo)))
  = match l with
    | [] -> ()
    | _ :: tl -> partition_mem f tl

let rec sorted_concat (lo:list int{ sorted lo })
                      (pivot:int)
                      (hi:list int{ sorted hi })
  : Lemma (requires (forall y. mem y lo ==> not (pivot <= y)) /\
                    (forall y. mem y hi ==> pivot <= y))
          (ensures sorted (append lo (pivot :: hi)))
  = match lo with
    | [] -> ()
    | _ :: tl -> sorted_concat tl pivot hi

let rec append_mem (l1 l2:list int)
  : Lemma (ensures (forall z. mem z (append l1 l2) = (mem z l1 || mem z l2)))
  = match l1 with
    | [] -> ()
    | _ :: tl -> append_mem tl l2

let prop1 = sorted
let prop2 (l s:list int) = (forall i . mem i l = mem i s)

let rec sort_correct (l:list int)
  : Lemma (ensures (let s = sort l in
                    prop1 s /\
                    prop2 l s))
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let f = (<=) pivot in
      let hi, lo = partition f tl in
      sort_correct hi; // (1) proves that partitions
      sort_correct lo; // (2) are indeed sorted
      // (3) proves that partition is valid:
      // no data lost, partitions are satisfy predicate
      partition_mem f tl;
      // (4) proves that combination of sorted parts with
      // pivot (resulting list) is sorted.
      // * `requires` clause is satisfied with (3)
      // * refinement on `l1`, `l2` are satisfied with (1), (2)
      sorted_concat (sort lo) pivot (sort hi);
      // (5) proves that all elements of input list are in
      // the result, using postcondition of (3) and
      // induction hypothesis to relate elements of `append ...`
      // to the input list `l`
      append_mem (sort lo) (pivot :: sort hi)
