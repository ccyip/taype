open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Misc.M (Driver)
open Misc_helper.M (Driver)

let () =
  setup_driver_simple ();

  let n = get_public_int () in
  let xs =
    get_private (mylist_of_sexp_check n) (Conceal.obliv_list_s n)
      (Conceal.obliv_list_s_for n)
  in
  let ys =
    get_private (mylist_of_sexp_check n) (Conceal.obliv_list_s n)
      (Conceal.obliv_list_s_for n)
  in
  let expected = get_expected_int () in

  collect_stat ();

  let res = obliv_test_elect1 xs ys in

  record_stat ();

  let res = Reveal.obliv_int_r res in

  finalize_driver ();

  expected = res |> print_result
