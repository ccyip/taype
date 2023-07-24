open Sexplib
open Taype_driver
open Taype_driver_coil
open Driver
open Coil_helper
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  let n = 2 in

  let xs = Conceal.obliv_list_eq_s_for n Party.Trusted in
  let ys = Conceal.obliv_list_eq_s_for n Party.Trusted in

  let res = obliv_merge xs ys in

  compile_coil "merge" res (output_sexp_conv Conv.sexp_of_int);

  finalize_driver ()
