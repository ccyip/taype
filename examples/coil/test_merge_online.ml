open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 2 in

  (* let xs = mylist_of_list [7; 12; 17; 18; 20] in *)
  (* let ys = mylist_of_list [3; 5; 11; 14; 19] in *)
  let xs = mylist_of_list [7; 12] in
  let ys = mylist_of_list [3; 9] in

  let res =
    run_coil "merge"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_list_eq_s n ys ]
      (input_sexp_conv Conv.int_of_sexp)
    |> Plaintext.obliv_list_r
  in
  mylist_to_sexp res |> print_sexp
