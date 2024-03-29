open Sexplib
open Taype_driver_coil

let print_sexp s = print_endline (Sexp.to_string_hum s)

module Ser = struct
  open Coil.M (Driver)
  include Ser

  let list = oadt Conv.sexp_of_int obliv_list
  let list_eq = oadt Conv.sexp_of_int obliv_list_eq
end

module Deser = struct
  open Coil.M (Driver)
  include Deser

  let list = oadt Conv.int_of_sexp Plaintext.obliv_list_r
  let list_eq = oadt Conv.int_of_sexp Plaintext.obliv_list_eq_r
end

module M (Driver : Taype_driver.S) = struct
  open Coil.M (Driver)

  let rec mylist_to_list = function
    | Nil -> []
    | Cons (x, xs) -> x :: mylist_to_list xs

  let rec mylist_of_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, mylist_of_list xs)

  let mylist_to_sexp xs =
    mylist_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int

  let mylist_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> mylist_of_list

  let rec dtree_to_sexp = function
    | Node (idx, thd, l, r) ->
        Sexp.List
          [
            Conv.sexp_of_int idx;
            Conv.sexp_of_int thd;
            dtree_to_sexp l;
            dtree_to_sexp r;
          ]
    | Leaf x -> Conv.sexp_of_int x

  let rec dtree_of_sexp = function
    | Sexp.List [ idx; thd; l; r ] ->
        Node
          ( Conv.int_of_sexp idx,
            Conv.int_of_sexp thd,
            dtree_of_sexp l,
            dtree_of_sexp r )
    | s -> Leaf (Conv.int_of_sexp s)
end
