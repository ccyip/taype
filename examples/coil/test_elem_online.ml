open Taype_driver_coil
open Coil.M (Driver)
open Coil_helper.M (Driver)

let () =
  let n = 2 in

  let xs = mylist_of_list [ 1; 2 ] in
  let y = 3 in

  let res =
    run_coil "elem" [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
    |> Plaintext.obliv_int_r
  in
  Printf.printf "%d\n" res;

  let xs = mylist_of_list [ 1; 3 ] in
  let y = 3 in

  let res =
    run_coil "elem" [ Plaintext.obliv_list_eq_s n xs; Plaintext.obliv_int_s y ]
    |> Plaintext.obliv_int_r
  in
  Printf.printf "%d\n" res
