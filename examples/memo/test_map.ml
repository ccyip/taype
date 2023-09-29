open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Memo.M (Driver)
open Memo_helper.M (Driver)

let () =
  setup_driver_simple ();
  let n = get_public nat_of_sexp in
  let xs =
    get_private (mylist_of_sexp_check n) (Conceal.obliv_list_s n)
      (Conceal.obliv_list_s_for n)
  in
  let y = get_private_int () in
  let expected = get_expected mylist_of_sexp in

  collect_stat ();

  (* let res = obliv_test_map' n (snd xs) y in *)
  let res = obliv_test_map xs y in

  record_stat ();

  (* let res = Reveal.obliv_list_r (n, res) in *)
  let res = Reveal.obliv_list_r res in

  finalize_driver ();

  expected = res |> print_result
