open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 8 in

  let xs = mylist_of_list [ 14; 15; 9; 13; 6; 16; 19; 10 ] in
  let y = 11 in

  let res =
    run_coil "map_as_filter"
      [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
      Deser.list_eq
  in
  mylist_to_sexp res |> print_sexp
