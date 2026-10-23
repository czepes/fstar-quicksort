module Quicksort.Int.Main
module Q = Quicksort.Int.Strong

let string_of_int_list (l:list int) =
  Printf.sprintf "[%s]"
    (String.concat "; " (List.Tot.map (Printf.sprintf "%d") l))

let main () =
  let orig = [7; 0; -3; 7; 99; 5; 3; 4] in
  let sorted = Q.sort_intrinsic orig in
  let msg =
    Printf.sprintf "Original list = %s\nSorted list   = %s\n"
     (string_of_int_list orig)
     (string_of_int_list sorted)
  in
  FStar.IO.print_string msg

// Run ``main ()`` when module loads
#push-options "--warn_error -272"
let _ = main()
#pop-options
