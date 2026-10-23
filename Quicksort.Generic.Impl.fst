module Quicksort.Generic.Impl

include Quicksort.Generic.Aux

let rec partition (#t:Type) (f:t -> bool) (l:list t)
  : x:(list t & list t) { length (fst x) + length (snd x) = length l }
  = match l with
    | [] -> [], []
    | hd :: tl ->
      let l1, l2 = partition f tl in
      if f hd
      then hd :: l1, l2
      else l1, hd :: l2

let rec sort #t (f:total_order_t t) (l:list t)
  : Tot (list t) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      append (sort f lo) (pivot :: sort f hi)
