open Sexplib
open Common
open Tree

let rec tree_to_sexp = function
  | Node (x, l, r) ->
    Sexp.List [Conv.sexp_of_int x; tree_to_sexp l; tree_to_sexp r]
  | Leaf x -> Conv.sexp_of_int x

let rec tree_of_sexp = function
  | Sexp.List [x; l; r] ->
    Node (Conv.int_of_sexp x, tree_of_sexp l, tree_of_sexp r)
  | s -> Leaf (Conv.int_of_sexp s)

let rec tree_depth = function
  | Leaf _ -> 0
  | Node (_, l, r) -> 1 + max (tree_depth l) (tree_depth r)

let tree_check t k = tree_depth t <= k

let tree_of_sexp_check = of_sexp_check tree_of_sexp tree_check
