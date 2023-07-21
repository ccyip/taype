open Sexplib
open Taype_driver
open Taype_driver_coil
open Driver
open Coil_helper
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  let n = 2 in

  let xs = Conceal.obliv_list_s_for n Party.Trusted in
  let y = Conceal.obliv_int_s_for Party.Trusted in

  let res = obliv_test_filter xs y in

  compile_coil "filter_list" res (output_sexp_conv Conv.sexp_of_int);

  finalize_driver ()
