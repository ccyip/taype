open Sexplib
open Common
open Tree

  let rec tree_to_sexp = function
    | Node (x, Leaf, Leaf) -> Conv.sexp_of_int x
    | Node (x, l, r) ->
        Sexp.List [ Conv.sexp_of_int x; tree_to_sexp l; tree_to_sexp r ]
    | Leaf -> Sexp.List []

  let rec tree_of_sexp = function
    | Sexp.List [ x; l; r ] ->
        Node (Conv.int_of_sexp x, tree_of_sexp l, tree_of_sexp r)
    | Sexp.List [] -> Leaf
    | s -> Node (Conv.int_of_sexp s, Leaf, Leaf)


let rec tree_depth = function
  | Leaf -> 0
  | Node (_, l, r) -> 1 + max (tree_depth l) (tree_depth r)

let tree_check t k = tree_depth t <= k

let tree_of_sexp_check = of_sexp_check tree_of_sexp tree_check

let rec mylist_to_list = function
  | Nil -> []
  | Cons (x, xs) -> x :: mylist_to_list xs

let rec mylist_of_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, mylist_of_list xs)

let mylist_to_sexp xs = mylist_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int

let mylist_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> mylist_of_list

let mylist_check xs k = Stdlib.List.length (mylist_to_list xs) <= k

let mylist_of_sexp_check = of_sexp_check mylist_of_sexp mylist_check
