open Driver
open Prelude
open Common
open Sexplib
open Misc
open Misc_conceal
open Misc_reveal
open Misc_helper

let _ =
  parse_options ();
  setup_driver_simple ();

  let k = get_public_int () in
  let size = obliv_list k in
  let obliv_xs1 = get_private (mylist_of_sexp_check k) (private_s_list k) size in
  let obliv_xs2 = get_private (mylist_of_sexp_check k) (private_s_list k) size in
  let expected = get_expected Conv.int_of_sexp in

  collect_stat ();

  let obliv_res = obliv_elect1 k obliv_xs1 obliv_xs2 in

  record_stat ();

  let res = unsafe_r_int obliv_res in

  finalize_driver ();

  expected = res |> print_result
