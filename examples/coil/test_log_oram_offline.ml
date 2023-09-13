open Taype_driver
open Taype_driver_coil
open Driver
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  let n = 16 in

  let xs = Conceal.obliv_list_eq_s_for n Party.Trusted in
  let i = Conceal.obliv_int_s_for Party.Trusted in

  let res = obliv_log_lookup xs i in

  compile_coil "log_lookup" res Ser.int;

  finalize_driver ()
