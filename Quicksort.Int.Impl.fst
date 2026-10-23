module Quicksort.Int.Impl

include Quicksort.Int.Aux

//                (pivot <= ?)
let rec partition (f:int -> bool) (l:list int)
  : x:(list int & list int) { length (fst x) + length (snd x) = length l }
  = match l with
    | [] -> [], []
    | hd :: tl ->
      let l1, l2 = partition f tl in
      if f hd
      then hd :: l1, l2
      else l1, hd :: l2

let rec sort (l:list int)
  : Tot (list int) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo = partition ((<=) pivot) tl in
      let sorted_lo = sort lo in
      let sorted_hi = sort hi in
      append sorted_lo (pivot :: sorted_hi)
