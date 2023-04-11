(* open Driver *)
(* open Prelude *)
(* open Common *)
(* open Sexplib *)
(* open Kmeans *)
(* open Kmeans_conceal *)
(* open Kmeans_reveal *)
(* open Kmeans_helper *)

(* let _ = *)
(*   parse_options (); *)
(*   setup_driver_simple (); *)

(*   let n_iter = get_public_int () in *)
(*   let n_clusters = get_public_int () in *)
(*   let dim = get_public_int () in *)
(*   let k1 = get_public_int () in *)
(*   let obliv_xs1 = get_private *)
(*       (vlist_of_sexp_check (dim, k1)) *)
(*       (private_s_vlist (dim, k1)) (obliv_vlist (dim, k1)) in *)
(*   let k2 = get_public_int () in *)
(*   let obliv_xs2 = get_private *)
(*       (vlist_of_sexp_check (dim, k2)) *)
(*       (private_s_vlist (dim, k2)) (obliv_vlist (dim, k2)) in *)

(*   collect_stat (); *)

(*   let obliv_res = obliv_kmeans n_iter n_clusters dim k1 k2 obliv_xs1 obliv_xs2 in *)

(*   record_stat (); *)

(*   let res = unsafe_r_vec (k1+k2) obliv_res in *)

(*   finalize_driver (); *)

(*   print_stat (); *)
(*   vec_to_sexp res |> print_sexp *)
