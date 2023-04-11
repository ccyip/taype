(* open Driver *)
(* open Prelude *)
(* open Common *)
(* open Sexplib *)
(* open List *)
(* open List_conceal *)
(* open List_reveal *)
(* open List_helper *)

(* let _ = *)
(*   parse_options (); *)
(*   setup_driver_simple (); *)

(*   let n = get_public_int () in *)
(*   let size = obliv_list n in *)
(*   let xs = get_private (mylist_of_sexp_check n) (private_s_list n) size in *)
(*   let ys = get_private (mylist_of_sexp_check n) (private_s_list n) size in *)
(*   let expected = get_expected Conv.int_of_sexp in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_hamming_distance n xs ys in *)

(*   record_stat (); *)

(*   let res = unsafe_r_int obliv_res in *)

(*   finalize_driver (); *)

(*   expected = res |> print_result *)
