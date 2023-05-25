open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Record.M (Driver)
open Record_helper.M (Driver)

let () =
  setup_driver_simple ();

  let v = get_public db_view_of_sexp in
  let db1 = get_private
      (db_of_sexp_check v)
      (Conceal.obliv_db_s v)
      (Conceal.obliv_db_s_for v) in
  let v = get_public db_view_of_sexp in
  let db2 = get_private
      (db_of_sexp_check v)
      (Conceal.obliv_db_s v)
      (Conceal.obliv_db_s_for v) in

  collect_stat ();

  let db = obliv_db_concat db1 db2 in
  let obliv_mean = obliv_age_mean db in
  let obliv_variance = obliv_age_variance db in

  record_stat ();

  let mean = Reveal.obliv_int_r obliv_mean in
  let variance = Reveal.obliv_int_r obliv_variance in

  finalize_driver ();

  print_stat ();
  Printf.printf "%d\n" mean;
  Printf.printf "%d\n" variance
