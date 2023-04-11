(* open Driver *)
(* open Common *)
(* open Sexplib *)
(* open Prelude *)
(* open Calculator *)
(* open Calculator_conceal *)
(* open Calculator_reveal *)
(* open Calculator_helper *)

(* let _ = *)
(*   parse_options (); *)
(*   setup_driver_simple (); *)

(*   let k1 = get_public_int () in *)
(*   let e1 = get_private *)
(*     (expr_of_sexp_check k1) *)
(*     (private_s_expr k1) *)
(*     (obliv_expr k1) in *)
(*   let k2 = get_public_int () in *)
(*   let e2 = get_private *)
(*     (expr_of_sexp_check k2) *)
(*     (private_s_expr k2) *)
(*     (obliv_expr k2) in *)
(*   let x = get_private_int () in *)
(*   let y = get_private_int () in *)
(*   let z = get_private_int () in *)
(*   (\* let expected = get_expected Conv.int_of_sexp in *\) *)

(*   collect_stat (); *)

(*   let xs1 = obliv_vars2 x y in *)
(*   let out1 = obliv_eval 2 k1 xs1 e1 in *)
(*   let xs2 = obliv_vars2 out1 z in *)
(*   let obliv_res = obliv_eval 2 k2 xs2 e2 in *)

(*   record_stat (); *)

(*   let res = unsafe_r_int obliv_res in *)

(*   finalize_driver (); *)

(*   (\* expected = res |> print_result *\) *)
(*   print_stat (); *)
(*   Conv.sexp_of_int res |> print_sexp *)
