open Taype_driver
open Sexplib

val parse_options : unit -> (module S)
(** Parse the commandline options. The first option is the driver name, and the
    second option is the party name. This function returns a driver module
    according the given driver name. *)

val get_public : (Sexp.t -> 'a) -> 'a
(** [get_public of_sexp] gets a public data from the input. The data is in
    S-expression format, converted using [of_sexp]. *)

val get_public_int : unit -> int
val get_public_bool : unit -> bool

val get_expected : (Sexp.t -> 'a) -> 'a
(** [get_public of_sexp] gets the expected result of the computation from the
    input. The data is in S-expression format, converted using [of_sexp]. *)

val get_expected_int : unit -> int
val get_expected_bool : unit -> bool

module Setup : functor (Driver : S) -> sig
  open Driver

  val setup_driver_simple : ?verbose:bool -> unit -> unit
  (** A convenient wrapper around [setup_driver]. *)

  val record_stat : unit -> unit
  (** A convenient wrapper around [report_stat]. *)

  val get_private : int -> (Sexp.t -> 'a) -> ('a -> obliv_array) -> obliv_array
  (** [get_private size of_sexp sec] gets a private data from the input. The
      party who owns this data converts it from the S-expression format using
      [of_sexp] and "encrypts" it using the section function [sec]. The other
      parties who has no access to this private data participates in the
      encryption by creating an oblivious array of size [size]. *)

  val get_private_int : unit -> obliv_array
  val get_private_bool : unit -> obliv_array
end

val print_stat : unit -> unit
(** Print out the performance statistics. *)

val print_result : bool -> unit
(** [print_result ok] prints out the performance statistics if the computation
    succeeds ([ok] is [true]), otherwise prints out a failing message. *)

val print_sexp : Sexp.t -> unit

val of_sexp_check : ('a -> 'b) -> ('b -> 'c -> bool) -> 'c -> 'a -> 'b
(** [of_sexp_check of_sexp check view s] converts an S-expression [s] to a data
    using [of_sexp], and checks if it is consistent with its [view] using the
    checking function [check]. *)
