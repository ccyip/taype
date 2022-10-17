open Driver
open Common
open Sexplib
open Prelude
open List
open List_conceal
open List_reveal
open List_helper

let _ =
  parse_options ();
  setup_driver_simple ();

  let n = get_public Conv.int_of_sexp in
  let size = obliv_list n in
  let obliv_xs = get_private (mylist_of_sexp_check n) (private_s_list n) size in
  let obliv_x = get_private_int () in
  let expected = get_expected mylist_of_sexp in

  collect_stat ();

  let obliv_res = obliv_insert n obliv_x obliv_xs in

  record_stat ();

  let res = unsafe_r_list (n+1) obliv_res in

  finalize_driver ();

  expected = res |> print_result
