open Driver
open Common
open Sexplib
open Prelude
open Tutorial
open Tutorial_conceal
open Tutorial_reveal
open Tutorial_helper

let _ =
  (* First we parse the commandline options. This tells us what party we are. *)
  parse_options ();
  (* Then setup the driver. *)
  setup_driver_simple ();

  (* Read the maximum length of the input list. This is the public view, so
     every party gets the same public value here. *)
  let n = get_public Conv.int_of_sexp in
  (* Calculate the size of the oblivious list. The parties who do not own the
     private list need this information to jointly compute the "encrypted" list
     with the party who owns it. *)
  let size = obliv_list n in
  (* Obtain an oblivious list. The party who owns the private list reads it
     from the input, and "encrypt" it with [private_s_list]. The other parties
     do not have this private list, but still participate in the encryption. *)
  let obliv_xs = get_private (mylist_of_sexp_check n) (private_s_list n) size in
  (* Obtain an oblivious integer. *)
  let obliv_x = get_private Conv.int_of_sexp private_s_int 1 in
  (* A testing program may also read an expected result to compare with the
     output of the oblivious computation. This can be done with the function
     [get_expected]. For example, [get_expected of_sexp]. *)

  (* We want to collect performance statistics. *)
  collect_stat ();

  (* Perform the core oblivious computation, [obliv_lookup] in this case. *)
  let obliv_res = obliv_lookup n obliv_x obliv_xs in

  (* Save the performance statistics. *)
  record_stat ();

  (* Reveal the result. *)
  let res = unsafe_r_bool obliv_res in

  (* Clean up the driver. *)
  finalize_driver ();

  (* Print out the statistics. If we also read the expected result, we would
     compare here and print out "failed" if they don't match: [print_result
     (expected = res)] *)
  print_stat ();
  (* Print out the result as an S-expression. *)
  Conv.sexp_of_bool res |> print_sexp
