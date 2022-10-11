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
  let obliv_xs = get_private of_sexp (private_s_list n) size in
  let obliv_x = get_private Conv.int_of_sexp private_s_int 1 in
  let expected = get_expected Conv.bool_of_sexp in

  collect_stat ();

  let obliv_res = obliv_lookup n obliv_x obliv_xs in
  let res = unsafe_r_bool obliv_res in

  record_stat ();
  finalize_driver ();

  expected = res |> print_result