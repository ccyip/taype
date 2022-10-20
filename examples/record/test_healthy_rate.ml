open Driver
open Common
open Sexplib
open Prelude
open Record
open Record_conceal
open Record_reveal
open Record_helper

let _ =
  parse_options ();
  setup_driver_simple ();

  let v = get_public db_view_of_sexp in
  let db = get_private
      (db_of_sexp_check v)
      (private_s_db v)
      (obliv_db v) in
  let b = get_private_int () in
  let e = get_private_int () in
  let expected = get_expected Conv.int_of_sexp in

  collect_stat ();

  let obliv_res = obliv_healthy_rate_of_age_group v db b e in

  (* #mux = 5^n - 1, where n is the length of the database. *)
  record_stat ();

  let res = unsafe_r_int obliv_res in

  finalize_driver ();

  expected = res |> print_result
