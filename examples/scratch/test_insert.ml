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
    get_private
      (mylist_of_sexp_check_eq n)
      (Conceal.obliv_list_eq_s n)
      (Conceal.obliv_list_eq_s_for n)
  in
  let y = get_private_int () in
  let expected = get_expected mylist_of_sexp in

  collect_stat ();

  (* let res = obliv_insert_eq' n y (snd xs) in *)
  let res = obliv_insert y xs in

  record_stat ();

  (* let res = Reveal.obliv_list_eq_r (n + 1, res) in *)

  let res = Reveal.obliv_list_r res in
  (* let res = *)
  (*   match res with *)
  (*   | Either.Left res -> Reveal.obliv_list_eq_r res *)
  (*   | Either.Right _ -> assert false *)
  (* in *)

  finalize_driver ();

  expected = res |> print_result
