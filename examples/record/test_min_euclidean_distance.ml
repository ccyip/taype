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
  let v = get_public patient_view_of_sexp in
  let p = get_private
      (patient_of_sexp_check v)
      (Conceal.obliv_patient_s v)
      (Conceal.obliv_patient_s_for v) in

  collect_stat ();

  let obliv_res = obliv_min_euclidean_distance db p in

  record_stat ();

  let res = Reveal.obliv_int_r obliv_res in

  finalize_driver ();

  print_stat ();
  Printf.printf "%d\n" res
