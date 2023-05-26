open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Calculator.M (Driver)
open Calculator_helper.M (Driver)

let () =
  setup_driver_simple ();

  let n = get_public_int () in
  let e1 =
    get_private (expr_of_sexp_check n) (Conceal.obliv_expr_s n)
      (Conceal.obliv_expr_s_for n)
  in
  let n = get_public_int () in
  let e2 =
    get_private (expr_of_sexp_check n) (Conceal.obliv_expr_s n)
      (Conceal.obliv_expr_s_for n)
  in
  let x = get_private_int () in
  let y = get_private_int () in
  let z = get_private_int () in

  collect_stat ();

  let xs1 = obliv_vars2 x y in
  let out1 = obliv_eval xs1 e1 in
  let xs2 = obliv_vars2 out1 z in
  let res = obliv_eval xs2 e2 in

  record_stat ();

  let res = Reveal.obliv_int_r res in

  finalize_driver ();

  print_stat ();
  Printf.printf "%d\n" res
