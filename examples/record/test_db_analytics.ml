(* open Driver *)
(* open Common *)
(* open Sexplib *)
(* open Prelude *)
(* open Record *)
(* open Record_conceal *)
(* open Record_reveal *)
(* open Record_helper *)

(* let _ = *)
(*   parse_options (); *)
(*   setup_driver_simple (); *)

(*   let v1 = get_public db_view_of_sexp in *)
(*   let db1 = get_private *)
(*       (db_of_sexp_check v1) *)
(*       (private_s_db v1) *)
(*       (obliv_db v1) in *)
(*   let v2 = get_public db_view_of_sexp in *)
(*   let db2 = get_private *)
(*       (db_of_sexp_check v2) *)
(*       (private_s_db v2) *)
(*       (obliv_db v2) in *)

(*   collect_stat (); *)

(*   let db = obliv_db_concat v1 v2 db1 db2 in *)
(*   let v = db_view_concat v1 v2 in *)
(*   let obliv_mean = obliv_age_mean v db in *)
(*   let obliv_variance = obliv_age_variance v db in *)

(*   record_stat (); *)

(*   let mean = unsafe_r_int obliv_mean in *)
(*   let variance = unsafe_r_int obliv_variance in *)

(*   finalize_driver (); *)

(*   print_stat (); *)
(*   Conv.sexp_of_int mean |> print_sexp; *)
(*   Conv.sexp_of_int variance |> print_sexp *)
