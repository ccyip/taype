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
  let xs = get_private
      (tree_of_sexp_check n)
      (private_s_tree n)
      (obliv_tree n) in
  let y = get_private_int () in
  let expected = get_expected tree_of_sexp in

  collect_stat ();

  let obliv_res = obliv_test_filter n xs y in

  record_stat ();

  let res = unsafe_r_tree n obliv_res in

  finalize_driver ();

  expected = res |> print_result
