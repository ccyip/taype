open Sexplib
open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper.M (Driver)

let () =
  let n = 2 in

  let xs = mylist_of_list [ 1; 2 ] in
  let y = 3 in

  let a =
    run_coil "filter_list"
      [ Plaintext.obliv_list_s n xs; Plaintext.obliv_int_s y ]
  in
  (* TODO: better way of communicating public view of the result *)
  let res = Plaintext.obliv_list_r 2 a in
  mylist_to_sexp res |> Sexp.to_string_hum |> print_endline;

  let xs = mylist_of_list [ 1; 2 ] in
  let y = 1 in

  let a =
    run_coil "filter_list"
      [ Plaintext.obliv_list_s n xs; Plaintext.obliv_int_s y ]
  in
  let res = Plaintext.obliv_list_r 2 a in
  mylist_to_sexp res |> Sexp.to_string_hum |> print_endline;
