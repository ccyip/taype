open Sexplib
open Common
open Dtree

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

let rec spineF_to_sexp = function
  | SFNode (idx, l, r) ->
    Sexp.List [Conv.sexp_of_int idx; spineF_to_sexp l; spineF_to_sexp r]
  | SFLeaf -> Sexp.List []

let rec spineF_of_sexp = function
  | Sexp.List [idx; l; r] ->
    SFNode (Conv.int_of_sexp idx, spineF_of_sexp l, spineF_of_sexp r)
  | _ -> SFLeaf

let rec spine_to_sexp = function
  | SNode (l, r) ->
    Sexp.List [spine_to_sexp l; spine_to_sexp r]
  | SLeaf -> Sexp.List []

let rec spine_of_sexp = function
  | Sexp.List [l; r] ->
    SNode (spine_of_sexp l, spine_of_sexp r)
  | _ -> SLeaf

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

let rec dtree_check_spineF t = function
  | SFNode (idx, l, r) ->
    begin match t with
    | Node (idx', _, lt, rt) ->
      idx = idx' && dtree_check_spineF lt l && dtree_check_spineF rt r
    | Leaf _ -> false
    end
  | SFLeaf ->
    begin match t with
    | Node _ -> false
    | Leaf _ -> true
    end

let rec dtree_check_spine t = function
  | SNode (l, r) ->
    begin match t with
    | Node (_, _, lt, rt) ->
      dtree_check_spine lt l && dtree_check_spine rt r
    | Leaf _ -> false
    end
  | SLeaf ->
    begin match t with
    | Node _ -> false
    | Leaf _ -> true
    end

let dtree_check_height t k = dtree_depth t = k
let dtree_check_max t k = dtree_depth t <= k

let dtree_of_sexp_check_spineF = of_sexp_check dtree_of_sexp dtree_check_spineF
let dtree_of_sexp_check_spine = of_sexp_check dtree_of_sexp dtree_check_spine
let dtree_of_sexp_check_height = of_sexp_check dtree_of_sexp dtree_check_height
let dtree_of_sexp_check_max = of_sexp_check dtree_of_sexp dtree_check_max
