open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let n = 8 in

  let xs = mylist_of_list [ 13; 6; 11; 8; 3; 7; 17; 12 ] in

  let res =
    run_coil "spa" [ Plaintext.obliv_list_eq_s n xs ] Deser.(pair int int)
  in
  Conv.sexp_of_pair Conv.sexp_of_int Conv.sexp_of_int res |> print_sexp
