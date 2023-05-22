open Sexplib
open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Dtree.M (Driver)
open Dtree_helper.M (Driver)

let () =
  setup_driver_simple ();

  let kt = get_public_int () in
  let t =
    get_private
      (dtree_of_sexp_check_max kt)
      (Conceal.obliv_dtree_max_s kt)
      (Conceal.obliv_dtree_max_s_for kt)
  in
  let k = get_public_int () in
  let xs =
    get_private (features_of_sexp_check k)
      (Conceal.obliv_features_s k)
      (Conceal.obliv_features_s_for k)
  in

  collect_stat ();

  let obliv_res = obliv_decide_max t xs in

  record_stat ();

  let res = Reveal.obliv_int_r obliv_res in

  finalize_driver ();

  print_stat ();
  Conv.sexp_of_int res |> print_sexp
