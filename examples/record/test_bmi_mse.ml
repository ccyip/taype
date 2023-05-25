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
  let k = get_public_int () in
  let db2 = get_private
      (bmi_db_of_sexp_check k)
      (Conceal.obliv_bmi_db_s k)
      (Conceal.obliv_bmi_db_s_for k) in

  collect_stat ();

  let obliv_res = obliv_bmi_mse db1 db2 in

  record_stat ();

  let res = Reveal.obliv_int_r obliv_res in

  finalize_driver ();

  print_stat ();
  Printf.printf "%d\n" res
