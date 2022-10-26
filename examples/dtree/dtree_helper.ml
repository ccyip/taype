open Sexplib
open Common
open Dtree

let rec dtree_to_sexp = function
  | Node (idx, thd, l, r) ->
    Sexp.List [Conv.sexp_of_int idx; Conv.sexp_of_int thd;
               dtree_to_sexp l; dtree_to_sexp r]
  | Leaf x -> Conv.sexp_of_int x

let rec dtree_of_sexp = function
  | Sexp.List [idx; thd; l; r] ->
    Node (Conv.int_of_sexp idx, Conv.int_of_sexp thd,
          dtree_of_sexp l, dtree_of_sexp r)
  | s -> Leaf (Conv.int_of_sexp s)

let rec dtree_depth = function
  | Leaf _ -> 0
  | Node (_, _, l, r) -> 1 + max (dtree_depth l) (dtree_depth r)

let dtree_check t k = dtree_depth t = k

let dtree_of_sexp_check = of_sexp_check dtree_of_sexp dtree_check

let rec features_to_list = function
  | Nil -> []
  | Cons (x, xs) -> x :: features_to_list xs

let rec features_of_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, features_of_list xs)

let features_to_sexp xs = features_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int

let features_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> features_of_list

let features_check xs k = Stdlib.List.length (features_to_list xs) = k

let features_of_sexp_check = of_sexp_check features_of_sexp features_check
