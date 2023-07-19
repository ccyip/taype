open Taype_driver
open Taype_driver_coil
open Driver
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  let n = 2 in

  let xs = Conceal.obliv_list_eq_s_for n Party.Trusted in
  let y = Conceal.obliv_int_s_for Party.Trusted in

  let res = obliv_elem y xs in

  compile_coil "elem" res;

  finalize_driver ()
