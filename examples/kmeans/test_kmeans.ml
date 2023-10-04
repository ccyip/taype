open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Kmeans.M (Driver)
open Kmeans_helper.M (Driver)

let () =
  setup_driver_simple ();

  let n_iter = get_public_int () in
  let n_clusters = get_public_int () in
  let dim = get_public_int () in
  let k = get_public_int () in
  let v = (dim, k) in
  let xs1 =
    get_private (vlist_of_sexp_check v) (Conceal.obliv_vlist_s v)
      (Conceal.obliv_vlist_s_for v)
  in
  let k = get_public_int () in
  let v = (dim, k) in
  let xs2 =
    get_private (vlist_of_sexp_check v) (Conceal.obliv_vlist_s v)
      (Conceal.obliv_vlist_s_for v)
  in

  collect_stat ();

  let res = obliv_test_kmeans n_iter n_clusters dim xs1 xs2 in

  record_stat ();

  let res = Reveal.obliv_vec_r res in
  (* let res =
    match res with
    | Either.Left res -> Reveal.obliv_vec_r res
    | Either.Right _ -> assert false
  in *)

  finalize_driver ();

  print_stat ();
  vec_to_sexp res |> print_sexp
