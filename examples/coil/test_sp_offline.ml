open Taype_driver
open Taype_driver_coil
open Driver
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  (* coil/c++ uses up too much memory to compile if [n] gets too big. The sp
  auction benchmark in coil is tested with [n = 8], but its implementation is
  incorrect. *)
  let n = 4 in

  let xs = Conceal.obliv_list_eq_s_for n Party.Trusted in

  let res = obliv_sp xs in

  compile_coil "spa" res Ser.(pair int int);

  finalize_driver ()
