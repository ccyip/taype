(* open Sexplib *)
(* open Tutorial *)
(* open Common *)

(* (\* This file implements the conversion between s-expression and the list data in *)
(*    the Taype source code. When we convert from s-expression to list, we also *)
(*    check if the given public view is valid, i.e. if it is not smaller than the *)
(*    actual length of the list. *\) *)

(* let rec mylist_to_list = function *)
(*   | Nil -> [] *)
(*   | Cons (x, xs) -> x :: mylist_to_list xs *)

(* let rec mylist_of_list = function *)
(*     | [] -> Nil *)
(*     | x :: xs -> Cons (x, mylist_of_list xs) *)

(* let mylist_to_sexp xs = mylist_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int *)

(* let mylist_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> mylist_of_list *)

(* let mylist_check xs k = List.length (mylist_to_list xs) <= k *)

(* let mylist_of_sexp_check = of_sexp_check mylist_of_sexp mylist_check *)
