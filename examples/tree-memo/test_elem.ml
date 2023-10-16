open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Tree.M (Driver)
open Tree_helper.M (Driver)

let () =
  setup_driver_simple ();

  let k = get_public spine_of_sexp in
  let t =
    get_private (tree_of_sexp_check k) (Conceal.obliv_tree_s k)
      (Conceal.obliv_tree_s_for k)
  in
  let y = get_private_int () in
  let expected = get_expected_bool () in

  collect_stat ();

  let res = obliv_elem t y in

  record_stat ();

  let res = Reveal.obliv_bool_r res in

  finalize_driver ();

  expected = res |> print_result
