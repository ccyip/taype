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
(*   let xs = get_private *)
(*       (mylist_of_sexp_check n) *)
(*       (private_s_list n) *)
(*       (obliv_list n) in *)
(*   let y = get_private_int () in *)
(*   let expected = get_expected mylist_of_sexp in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_test_map n xs y in *)

(*   record_stat (); *)

(*   let res = unsafe_r_list n obliv_res in *)

(*   finalize_driver (); *)

(*   expected = res |> print_result *)
