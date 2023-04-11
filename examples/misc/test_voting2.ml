(* open Driver *)
(* open Prelude *)
(* open Common *)
(* open Sexplib *)
(* open Misc *)
(* open Misc_conceal *)
(* open Misc_reveal *)
(* open Misc_helper *)

(* let _ = *)
(*   parse_options (); *)
(*   setup_driver_simple (); *)

(*   let n = get_public_int () in *)
(*   let k1 = get_public_int () in *)
(*   let obliv_xs1 = *)
(*     get_private (mylist_of_sexp_check k1) (private_s_list k1) (obliv_list k1) in *)
(*   let k2 = get_public_int () in *)
(*   let obliv_xs2 = *)
(*     get_private (mylist_of_sexp_check k2) (private_s_list k2) (obliv_list k2) in *)
(*   let expected = get_expected Conv.int_of_sexp in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_elect2 n k1 obliv_xs1 k2 obliv_xs2 in *)

(*   record_stat (); *)

(*   let res = unsafe_r_int obliv_res in *)

(*   finalize_driver (); *)

(*   expected = res |> print_result *)
