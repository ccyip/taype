open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 8 in

  let keys = mylist_of_list [ 2; 14; 4; 9; 3; 19; 15; 1 ] in
  let values = mylist_of_list [ 2; 7; 12; 8; 13; 15; 5; 15 ] in
  let key = 4 in

  let res =
    run_coil_simple "assoc_lookup"
      [
        Plaintext.obliv_list_eq_s n keys;
        Plaintext.obliv_list_eq_s n values;
        Plaintext.obliv_int_s key;
      ]
    |> Plaintext.obliv_int_r
  in
  Conv.sexp_of_int res |> print_sexp
