open Common
open Sexplib
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open List.M (Driver)
open List_helper.M (Driver)

let () =
  setup_driver_simple ();
  let n = get_public_int () in
  let xs =
    get_private (mylist_of_sexp_check n) (Conceal.obliv_list_s n)
      (Conceal.obliv_list_s_for n)
  in
  let y = get_private_int () in
  let expected =
    get_expected (Conv.pair_of_sexp mylist_of_sexp mylist_of_sexp)
  in

  collect_stat ();

  let res1, res2 = obliv_test_span xs y in

  record_stat ();

  let res1 = Reveal.obliv_list_r res1 in
  let res2 = Reveal.obliv_list_r res2 in

  finalize_driver ();

  expected = (res1, res2) |> print_result
