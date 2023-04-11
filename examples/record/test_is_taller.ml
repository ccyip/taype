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

(*   let va = get_public patient_view_of_sexp in *)
(*   let a = get_private *)
(*       (patient_of_sexp_check va) *)
(*       (private_s_patient va) *)
(*       (obliv_patient va) in *)
(*   let vb = get_public patient_view_of_sexp in *)
(*   let b = get_private *)
(*       (patient_of_sexp_check vb) *)
(*       (private_s_patient vb) *)
(*       (obliv_patient vb) in *)
(*   let expected = get_expected Conv.bool_of_sexp in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_is_taller va vb a b in *)

(*   record_stat (); *)

(*   let res = unsafe_r_bool obliv_res in *)

(*   finalize_driver (); *)

(*   expected = res |> print_result *)
