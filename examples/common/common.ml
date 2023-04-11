open Taype_driver
open Sexplib
open Scanf
open Fun

let this_party : party ref = ref PublicP
let stat : int ref = ref (-1)

let party_of_string = function
  | "public" -> PublicP
  | "alice" -> PrivateP 1
  | "bob" -> PrivateP 2
  | _ -> failwith "Unknown party: only supports public, alice, and bob"

let driver_of_string = function
  | "plaintext" -> (module Taype_driver_plaintext.Driver : S)
  | "emp" -> (module Taype_driver_emp.Driver : S)
  | _ -> failwith "Unknown driver: only supports plaintext and emp"

let scan_line () =
  scanf "%s@:%s@\n" (fun p s -> (party_of_string (String.trim p), s))

let parse_options () =
  if Array.length Sys.argv < 3 then failwith "Not enough arguments";
  this_party := party_of_string Sys.argv.(2);
  driver_of_string Sys.argv.(1)

let get_public of_sexp =
  let party, s = scan_line () in
  match party with
  | PublicP -> Sexp.of_string_conv_exn s of_sexp
  | PrivateP _ -> failwith "Input party is not public"

let get_public_int () = get_public Conv.int_of_sexp
let get_public_bool () = get_public Conv.bool_of_sexp

let get_expected of_sexp =
  let s = scanf "expected :%s@\n" id in
  Sexp.of_string_conv_exn s of_sexp

let get_expected_int () = get_expected Conv.int_of_sexp
let get_expected_bool () = get_expected Conv.bool_of_sexp

module Setup (Driver : S) = struct
  open Driver

  (* Probably should use a better way to find an unused port. *)
  let setup_driver_simple ?verbose () =
    setup_driver ?verbose "127.0.0.1" 12345 !this_party

  let record_stat () = stat := report_stat ()

  let get_private size of_sexp sec =
    let party, s = scan_line () in
    if !this_party = party || !this_party = PublicP then
      sec (Sexp.of_string_conv_exn s of_sexp)
    else Conceal.obliv_array_new_for party size

  let get_private_int () = get_private 1 Conv.int_of_sexp Conceal.obliv_int_s
  let get_private_bool () = get_private 1 Conv.bool_of_sexp Conceal.obliv_bool_s
end

let print_stat () =
  print_int !stat;
  print_newline ()

let print_result ok = if ok then print_stat () else print_endline "failed"
let print_sexp s = print_endline (Sexp.to_string s)

let of_sexp_check of_sexp check view s =
  let data = of_sexp s in
  if not (check data view) then failwith "input data is invalid";
  data
