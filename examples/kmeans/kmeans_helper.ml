open Sexplib
open Kmeans
open Common

let rec vec_to_list = function
  | Nil -> []
  | Cons (x, xs) -> x :: vec_to_list xs

let rec vec_of_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, vec_of_list xs)

let vec_to_sexp xs = vec_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int

let vec_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> vec_of_list

let vec_check xs k = List.length (vec_to_list xs) = k

let vec_of_sexp_check = of_sexp_check vec_of_sexp vec_check

let rec vlist_to_list = function
  | VNil -> []
  | VCons (x, xs) -> x :: vlist_to_list xs

let rec vlist_of_list = function
    | [] -> VNil
    | x :: xs -> VCons (x, vlist_of_list xs)

let vlist_to_sexp xs = vlist_to_list xs |> Conv.sexp_of_list vec_to_sexp

let vlist_of_sexp s = Conv.list_of_sexp vec_of_sexp s |> vlist_of_list

let vlist_check xs (dim, k) =
  let xs = vlist_to_list xs in
  List.for_all (fun v -> vec_check v dim) xs && List.length xs = k

let vlist_of_sexp_check = of_sexp_check vlist_of_sexp vlist_check
