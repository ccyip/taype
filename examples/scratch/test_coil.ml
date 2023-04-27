open Taype_driver
open Common
open Taype_driver_coil
open Driver
open Setup (Driver)
open Scratch.M (Driver)
open Scratch_helper.M (Driver)

let () =
  setup_driver_simple ();

  let n = 8 in
  let xs = Conceal.obliv_list_s_for n (Party.Private 1) in
  let y = Conceal.obliv_int_s 3 in

  let res = obliv_elem y xs in

  (* let n = 8 in *)
  (* let xs = Conceal.obliv_list_s_for n (Party.Private 1) in *)
  (* let y = Conceal.obliv_int_s 3 in *)

  (* let (_, res) = obliv_insert' y xs in *)

  print_coil res;
  print_newline ();

  finalize_driver ()
