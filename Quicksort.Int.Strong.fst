module Quicksort.Int.Strong

include Quicksort.Generic.Aux
include Quicksort.Generic.Impl

let rec sorted (l:list int)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> x <= y && sorted (y :: xs)

let mem (#t:eqtype) (i:t) (l:list t)
  : bool
  = count i l > 0

let is_permutation (#t:eqtype) (l1 l2:list t) =
  forall x. count x l1 = count x l2

let rec append_count (#t:eqtype) (l1 l2:list t)
  : Lemma (ensures (forall a. count a (append l1 l2) = (count a l1 + count a l2)))
  = match l1 with
    | [] -> ()
    | _ :: tl -> append_count tl l2

// Auxiliary lemmas
let rec partition_mem_permutation (#t:eqtype)
                                  (f:t -> bool)
                                  (l:list t)
  : Lemma (let hi, lo = partition f l in
           (forall x. mem x hi ==> f x) /\
           (forall x. mem x lo ==> not (f x)) /\
           (is_permutation l (append hi lo)))
  = match l with
    | [] -> ()
    | hd :: tl ->
      partition_mem_permutation f tl;
      let hi, lo = partition f tl in
      append_count hi lo;
      append_count hi (hd :: lo);
      append_count (hd :: hi) lo

let rec sorted_concat (l1:list int{sorted l1})
                      (pivot:int)
                      (l2:list int{sorted l2})
  : Lemma (requires (forall y. mem y l1 ==> not (pivot <= y)) /\
                    (forall y. mem y l2 ==> pivot <= y))
          (ensures sorted (append l1 (pivot :: l2)))
  = match l1 with
    | [] -> ()
    | _ :: tl -> sorted_concat tl pivot l2

let permutation_app_lemma (#t:eqtype) (pivot:t)
                          (tl lo hi:list t)
  : Lemma (requires (is_permutation tl (append lo hi)))
          (ensures  (let l = pivot :: tl in is_permutation l (append lo (pivot :: hi))))
  = append_count lo hi;
    append_count lo (pivot :: hi)

// Correctness proofs
let prop1 = sorted
let prop2 = is_permutation

let rec sort_correct (l:list int)
  : Lemma (ensures (let s = sort (<=) l in
                    prop1 s /\ prop2 l s))
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let f = (<=) in
      let hi, lo = partition (f pivot) tl in
      partition_mem_permutation (f pivot) tl;
      append_count lo hi;
      append_count hi lo;
      assert(is_permutation tl (append lo hi));
      sort_correct hi;
      sort_correct lo;
      let slo, shi = sort f lo, sort f hi in
      sorted_concat slo pivot shi;
      append_count slo shi;
      assert(is_permutation tl (append slo shi));
      permutation_app_lemma pivot tl slo shi

let rec sort_intrinsic (l:list int)
  : Tot (s:list int { prop1 s /\ prop2 l s })
    (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let f = fun x -> pivot <= x in
      let hi, lo = partition f tl in
      let shi, slo = sort_intrinsic hi, sort_intrinsic lo in
      partition_mem_permutation f tl;
      append_count lo hi;
      append_count hi lo;
      assert(is_permutation tl (append lo hi));
      sorted_concat (slo) pivot (shi);
      append_count (slo) (shi);
      assert(is_permutation tl (append (slo) (shi)));
      permutation_app_lemma pivot tl (slo) (shi);
      append (slo) (pivot :: shi)
