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

  let k1 = get_public_int () in
  let t1 = get_private
      (tree_of_sexp_check k1)
      (private_s_tree k1)
      (obliv_tree k1) in
  let k2 = get_public_int () in
  let t2 = get_private
      (tree_of_sexp_check k2)
      (private_s_tree k2)
      (obliv_tree k2) in
  let x = get_private_int () in

  collect_stat ();

  let obliv_res = obliv_node k1 k2 t1 t2 x in

  record_stat ();

  let res = unsafe_r_tree (1 + max k1 k2) obliv_res in

  finalize_driver ();

  print_stat ();
  tree_to_sexp res |> print_sexp
