open Containers
open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 8 in

  let xs = mylist_of_list List.(1 -- n) in
  let y = 2 in

  let res =
    run_coil_simple "elem"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
    |> Plaintext.obliv_bool_r
  in
  Conv.sexp_of_bool res |> print_sexp;

  let xs = mylist_of_list List.(1 -- n) in
  let y = n + 1 in

  let res =
    run_coil_simple "elem"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
    |> Plaintext.obliv_bool_r
  in
  Conv.sexp_of_bool res |> print_sexp
