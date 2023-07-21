open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 8 in

  (* let xs = mylist_of_list [9; 2; 3; 12; 6; 8; 7; 1; 4; 5; 0; 10; 21; 16; 30; 13] in *)
  let xs = mylist_of_list [9; 2; 3; 12; 6; 8; 7; 1] in
  let i = 6 in

  let res =
    run_coil_simple "linear_oram"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s i ]
    |> Plaintext.obliv_int_r
  in
  Conv.sexp_of_int res |> print_sexp
