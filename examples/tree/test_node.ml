open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Tree.M (Driver)
open Tree_helper.M (Driver)

let () =
  setup_driver_simple ();

  let k1 = get_public_int () in
  let t1 =
    get_private (tree_of_sexp_check k1) (Conceal.obliv_tree_s k1)
      (Conceal.obliv_tree_s_for k1)
  in
  let k2 = get_public_int () in
  let t2 =
    get_private (tree_of_sexp_check k2) (Conceal.obliv_tree_s k2)
      (Conceal.obliv_tree_s_for k2)
  in
  let x = get_private_int () in

  collect_stat ();

  let res = obliv_node t1 t2 x in

  record_stat ();

  let res = Reveal.obliv_tree_r res in

  finalize_driver ();

  print_stat ();
  tree_to_sexp res |> print_sexp
