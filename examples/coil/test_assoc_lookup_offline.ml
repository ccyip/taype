open Taype_driver
open Taype_driver_coil
open Driver
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  let n = 8 in

  let keys = Conceal.obliv_list_eq_s_for n Party.Trusted in
  let values = Conceal.obliv_list_eq_s_for n Party.Trusted in
  let key = Conceal.obliv_int_s_for Party.Trusted in

  let res = obliv_assoc_lookup keys values key in

  compile_coil_simple "assoc_lookup" res;

  finalize_driver ()
