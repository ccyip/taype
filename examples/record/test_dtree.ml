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

(*   let tv = get_public dtree_view_of_sexp in *)
(*   let t = get_private *)
(*       (dtree_of_sexp_check tv) *)
(*       (private_s_dtree tv) *)
(*       (obliv_dtree tv) in *)
(*   let pv = get_public patient_view_of_sexp in *)
(*   let p = get_private *)
(*       (patient_of_sexp_check pv) *)
(*       (private_s_patient pv) *)
(*       (obliv_patient pv) in *)
(*   let expected = get_expected Conv.bool_of_sexp in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_decide tv pv t p in *)

(*   record_stat (); *)

(*   let res = unsafe_r_bool obliv_res in *)

(*   finalize_driver (); *)

(*   expected = res |> print_result *)
