open Driver
open Common
open Sexplib
open Prelude
open Millionaire
open Millionaire_conceal
open Millionaire_reveal

let _ =
  parse_options ();
  setup_driver_simple ();

  let a = get_private Conv.int_of_sexp private_s_int 1 in
  let b = get_private Conv.int_of_sexp private_s_int 1 in
  let expected = get_expected Conv.bool_of_sexp in

  collect_stat ();

  let obliv_res = obliv_compare a b in

  record_stat ();

  let res = unsafe_r_bool obliv_res in

  finalize_driver ();

  expected = res |> print_result
