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
(*   let db1 = get_private *)
(*       (db_of_sexp_check v) *)
(*       (private_s_db v) *)
(*       (obliv_db v) in *)
(*   let k = get_public_int () in *)
(*   let db2 = get_private *)
(*       (bmi_db_of_sexp_check k) *)
(*       (private_s_bmi_db k) *)
(*       (obliv_bmi_db k) in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_bmi_mse v k db1 db2 in *)

(*   record_stat (); *)

(*   let res = unsafe_r_int obliv_res in *)

(*   finalize_driver (); *)

(*   print_stat (); *)
(*   Conv.sexp_of_int res |> print_sexp *)
