open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Record.M (Driver)
open Record_helper.M (Driver)

let () =
  setup_driver_simple ();

  let v = get_public db_view_of_sexp in
  let db = get_private
      (db_of_sexp_check v)
      (Conceal.obliv_db_s v)
      (Conceal.obliv_db_s_for v) in
  let b = get_private_int () in
  let e = get_private_int () in
  let expected = get_expected_int () in

  collect_stat ();

  let obliv_res = obliv_healthy_rate_of_age_group db b e in

  record_stat ();

  let res = Reveal.obliv_int_r obliv_res in

  finalize_driver ();

  expected = res |> print_result
