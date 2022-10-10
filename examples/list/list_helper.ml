open Sexplib
open List

let to_sexp xs =
  let rec go = function
    | Nil -> []
    | Cons (x, xs) -> x :: go xs
  in Conv.sexp_of_list Conv.sexp_of_int (go xs)

let of_sexp s =
  let rec go = function
    | [] -> Nil
    | x :: xs -> Cons (x, go xs)
  in go (Conv.list_of_sexp Conv.int_of_sexp s)
