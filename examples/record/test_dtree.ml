open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Record.M (Driver)
open Record_helper.M (Driver)

let () =
  setup_driver_simple ();

  let v = get_public dtree_view_of_sexp in
  let t = get_private
      (dtree_of_sexp_check v)
      (Conceal.obliv_dtree_s v)
      (Conceal.obliv_dtree_s_for v) in
  let v = get_public patient_view_of_sexp in
  let p = get_private
      (patient_of_sexp_check v)
      (Conceal.obliv_patient_s v)
      (Conceal.obliv_patient_s_for v) in
  let expected = get_expected_bool () in

  collect_stat ();

  let obliv_res = obliv_decide t p in

  record_stat ();

  let res = Reveal.obliv_bool_r obliv_res in

  finalize_driver ();

  expected = res |> print_result
