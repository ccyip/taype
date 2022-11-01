open Driver
open Prelude
open Common
open Sexplib
open Dtree
open Dtree_conceal
open Dtree_reveal
open Dtree_helper

let _ =
  parse_options ();
  setup_driver_simple ();

  let t = get_public dtree_of_sexp in
  let u = private_s_dtree_all t t in
  let k = get_public_int () in
  let xs = get_private
      (features_of_sexp_check k)
      (private_s_features k)
      (obliv_features k) in

  collect_stat ();

  let obliv_res = obliv_decide_all t k u xs in

  record_stat ();

  let res = unsafe_r_int obliv_res in

  finalize_driver ();

  print_stat ();
  Conv.sexp_of_int res |> print_sexp
