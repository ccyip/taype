open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper.M (Driver)

let () =
  let n = 4 in

  let xs = mylist_of_list [ 1; 2; 3; 4 ] in
  let y = 2 in

  let res =
    run_coil_simple "elem"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
    |> Plaintext.obliv_bool_r
  in
  Conv.sexp_of_bool res |> Sexp.to_string_hum |> print_endline;

  let xs = mylist_of_list [ 1; 2; 3; 4 ] in
  let y = 5 in

  let res =
    run_coil_simple "elem"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
    |> Plaintext.obliv_bool_r
  in
  Conv.sexp_of_bool res |> Sexp.to_string_hum |> print_endline
