open Sexplib
open Common

module M (Driver : Taype_driver.S) = struct
  open Scratch.M (Driver)

  let rec mylist_to_list = function
    | Nil -> []
    | Cons (x, xs) -> x :: mylist_to_list xs

  let rec mylist_of_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, mylist_of_list xs)

  let mylist_to_sexp xs =
    mylist_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int

  let mylist_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> mylist_of_list
  let mylist_check xs k = Stdlib.List.length (mylist_to_list xs) <= k
  let mylist_of_sexp_check = of_sexp_check mylist_of_sexp mylist_check

  let mylist_check_eq xs k = Stdlib.List.length (mylist_to_list xs) = k
  let mylist_of_sexp_check_eq = of_sexp_check mylist_of_sexp mylist_check_eq
end
