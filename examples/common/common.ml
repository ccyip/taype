open Driver
open Prelude
open Sexplib
open Scanf
open Fun

let my_party : int ref = ref (-1)
let switch : string ref = ref ""
let stat : int ref = ref (-1)

let party_of_string = function
  | "public" -> party_public
  | "alice" -> party_alice
  | "bob" -> party_bob
  | _ -> failwith "Unknown party: only supports public, alice, and bob"

(* Parse the commandline options. The first options is the party name, and the
   optional second one is the oblivious type selector. *)
let parse_options () =
  if Array.length Sys.argv < 2 then failwith "Not enough arguments";
  my_party := party_of_string Sys.argv.(1);
  if Array.length Sys.argv > 2 then switch := Sys.argv.(2)

(* A simple wrapper around [setup_driver]. Probably should have a better way to
   find an unused port. *)
let setup_driver_simple ?(verbose=false) () =
  setup_driver ~verbose "127.0.0.1" 12345 !my_party

let scan_line () =
  let (party, s) = scanf "%s@:%s@\n" (fun x y -> (x, y)) in
  (party_of_string (String.trim party), s)

(* Get a public data from input. [conv] is used to convert the sexp to the
   data. *)
let get_public conv =
  let (party, s) = scan_line () in
  if party <> party_public then failwith "Input party is not public";
  Sexp.of_string_conv_exn s conv

(* Get a private data from input. [conv] is used to convert the sexp to the data
   for the party who owns it. [sec] is the section function to "encrypt" the
   data. If we do not own this data, we create an oblivious array of size
   [size], with the help from the party who owns it. *)
let get_private conv sec size =
  let (party, s) = scan_line () in
  if party = !my_party
  then sec (Sexp.of_string_conv_exn s conv)
  else obliv_array_new_from size party

let get_public_int () = get_public Conv.int_of_sexp
let get_public_bool () = get_public Conv.bool_of_sexp
let get_private_int () = get_private Conv.int_of_sexp private_s_int 1
let get_private_bool () = get_private Conv.bool_of_sexp private_s_bool 1

(* Get the expected result of the computation from input. [conv] is used to
   convert the sexp to the data. *)
let get_expected conv =
  let s = scanf "expected :%s@\n" id in
  Sexp.of_string_conv_exn s conv

let record_stat () = stat := report_stat ()

let print_stat () = print_int !stat; print_newline ()

let print_result ok =
  if ok then print_stat () else print_endline "failed"

let print_sexp s =
  print_endline (Sexp.to_string s)

let of_sexp_check of_sexp check v s =
  let d = of_sexp s in
  if (not (check d v)) then failwith "input data is invalid";
  d
