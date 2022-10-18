open Driver
open Common
open Sexplib
open Prelude
open Tutorial
open Tutorial_conceal
open Tutorial_reveal
open Tutorial_helper

let _ =
  parse_options ();
  setup_driver_simple ();

  let n = get_public_int () in
  let size = obliv_list n in
  let obliv_xs = get_private (mylist_of_sexp_check n) (private_s_list n) size in
  let obliv_x = get_private_int () in

  collect_stat ();

  let obliv_res = obliv_insert n obliv_x obliv_xs in

  record_stat ();

  (* Make sure the public view is consistent with the one defined in taype. *)
  let res = unsafe_r_list (n+1) obliv_res in

  finalize_driver ();

  print_stat ();
  mylist_to_sexp res |> print_sexp
