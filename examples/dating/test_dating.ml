open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Dating.M (Driver)
open Dating_helper.M (Driver)

let () =
  setup_driver_simple ();

  let n = get_public_int () in
  let prof1 =
    get_private profile_of_sexp
      (Conceal.obliv_profile_s true)
      (Conceal.obliv_profile_s_for true)
  in
  let pred1 =
    get_private (pred_of_sexp_check n) (Conceal.obliv_pred_s n)
      (Conceal.obliv_pred_s_for n)
  in
  let prof2 =
    get_private profile_of_sexp
      (Conceal.obliv_profile_s true)
      (Conceal.obliv_profile_s_for true)
  in
  let pred2 =
    get_private (pred_of_sexp_check n) (Conceal.obliv_pred_s n)
      (Conceal.obliv_pred_s_for n)
  in

  collect_stat ();

  let res = obliv_good_match prof1 pred1 prof2 pred2 in

  record_stat ();

  let res = Reveal.obliv_bool_r res in

  finalize_driver ();

  print_stat ();
  Printf.printf "%B\n" res
