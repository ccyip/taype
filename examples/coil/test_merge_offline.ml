open Taype_driver
open Taype_driver_coil
open Driver
open Coil_helper
open Coil.M (Driver)

let () =
  setup_driver "127.0.0.1" 12345 Party.Public;

  (* For some reason, coil compiles this extremely slow given bigger [n], even
  with sum optimization enabled. *)
  let n = 3 in

  let xs = Conceal.obliv_list_eq_s_for n Party.Trusted in
  let ys = Conceal.obliv_list_eq_s_for n Party.Trusted in

  let res = obliv_merge xs ys in

  (* let res =
    match res with Either.Left r -> r | Either.Right _ -> assert false
  in
  compile_coil "merge_list" res Ser.list_eq; *)

  compile_coil "merge_list" res Ser.list;

  finalize_driver ()
