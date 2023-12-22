open Containers
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 4 in

  let xs = mylist_of_list List.(1 -- n) in
  let y = n + 1 in

  let res =
    run_coil "filter_list"
      [ Plaintext.obliv_list_s n xs; Plaintext.obliv_int_s y ]
      Deser.list
  in
  mylist_to_sexp res |> print_sexp;

  let xs = mylist_of_list List.(1 -- n) in
  let y = n / 2 + 1 in

  let res =
    run_coil "filter_list"
      [ Plaintext.obliv_list_s n xs; Plaintext.obliv_int_s y ]
      Deser.list
  in
  mylist_to_sexp res |> print_sexp
