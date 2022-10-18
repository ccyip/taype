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

  let db_v = get_public db_view_of_sexp in
  let db = get_private
      (db_of_sexp_check db_v)
      (private_s_db db_v)
      (obliv_db db_v) in
  let p_v = get_public patient_view_of_sexp in
  let p = get_private
      (patient_of_sexp_check p_v)
      (private_s_patient p_v)
      (obliv_patient p_v) in

  collect_stat ();

  let obliv_res = obliv_min_euclidean_distance db_v p_v db p in

  record_stat ();

  let res = unsafe_r_int obliv_res in

  finalize_driver ();

  print_stat ();
  Conv.sexp_of_int res |> print_sexp
