open Containers
open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper
open Coil_helper.M (Driver)

let () =
  let k = 2 in
  let n = 2 in

  let features = mylist_of_list List.(map (fun x -> x * 10) (1 -- n)) in
  let dtree = Sexp.of_string_conv_exn "(0 15 (1 18 1 2) 3)" dtree_of_sexp in

  let res =
    run_coil "dtree_max"
      [
        Plaintext.obliv_dtree_max_s k dtree;
        Plaintext.obliv_list_eq_s n features;
      ]
      Deser.int
  in
  Conv.sexp_of_int res |> print_sexp;

  let res =
    run_coil "dtree_all" [ Plaintext.obliv_list_eq_s n features ] Deser.int
  in
  Conv.sexp_of_int res |> print_sexp
