open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Scratch.M (Driver)
open Scratch_helper.M (Driver)

let () =
  setup_driver_simple ();

  let n = get_public_int () in
  let xs =
    get_private (mylist_of_sexp_check n) (Conceal.obliv_list_s n)
      (Conceal.obliv_list_s_for n)
  in
  let y = get_private_int () in
  let expected = get_expected_bool () in

  collect_stat ();

  (* let res = obliv_elem' n y (snd xs) in *)
  let res = obliv_elem y xs in

  record_stat ();

  let res = Reveal.obliv_bool_r res in

  finalize_driver ();

  expected = res |> print_result
