open Common
module Driver = (val parse_options ())
open Driver
open Setup (Driver)
open Misc.M (Driver)

let () =
  setup_driver_simple ();

  let a = get_private_int () in
  let b = get_private_int () in
  let expected = get_expected_bool () in

  collect_stat ();

  let res = obliv_le a b in

  record_stat ();

  let res = Reveal.obliv_bool_r res in

  finalize_driver ();

  expected = res |> print_result
