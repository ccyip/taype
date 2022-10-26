open Driver
open Prelude
open Common
open Sexplib
open Tree
open Tree_conceal
open Tree_reveal
open Tree_helper

let _ =
  parse_options ();
  setup_driver_simple ();

  let n = get_public_int () in
  let t = get_private (tree_of_sexp_check n) (private_s_tree n) (obliv_tree n) in
  let x = get_private_int () in
  let expected = get_expected Conv.bool_of_sexp in

  collect_stat ();

  let obliv_res = obliv_lookup n t x in

  record_stat ();

  let res = unsafe_r_bool obliv_res in

  finalize_driver ();

  expected = res |> print_result
