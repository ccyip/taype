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

(*   let v = get_public db_view_of_sexp in *)
(*   let db = get_private *)
(*       (db_of_sexp_check v) *)
(*       (private_s_db v) *)
(*       (obliv_db v) in *)
(*   let id = get_private_int () in *)
(*   let expected = get_expected Conv.bool_of_sexp in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_is_obese_by_id v db id in *)

(*   record_stat (); *)

(*   let res = unsafe_r_bool obliv_res in *)

(*   finalize_driver (); *)

(*   print_stat (); *)
(*   expected = res |> print_result *)
