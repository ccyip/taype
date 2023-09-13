open Sexplib
open Taype_driver
open Taype_driver_coil
open Driver
open Coil.M (Driver)
open Coil_helper.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  let k = 2 in
  let n = 2 in

  let dtree = Conceal.obliv_dtree_max_s_for k Party.Trusted in
  let features = Conceal.obliv_list_eq_s_for n Party.Trusted in

  let res = obliv_decide_max dtree features in

  compile_coil "dtree_max" res Ser.int;

  let dtree = Sexp.of_string_conv_exn "(0 15 (1 18 1 2) 3)" dtree_of_sexp in
  let features = Conceal.obliv_list_eq_s_for n Party.Trusted in

  let res = obliv_decide_all dtree features in

  compile_coil "dtree_all" res Ser.int;

  finalize_driver ()
