open Sexplib
open Common
open Calculator

let rec vars_to_list = function
  | Nil -> []
  | Cons (x, xs) -> x :: vars_to_list xs

let rec vars_of_list = function
  | [] -> Nil
  | x :: xs -> Cons (x, vars_of_list xs)

let vars_to_sexp xs = vars_to_list xs |> Conv.sexp_of_list Conv.sexp_of_int

let vars_of_sexp s = Conv.list_of_sexp Conv.int_of_sexp s |> vars_of_list

let vars_check xs k = List.length (vars_to_list xs) = k

let vars_of_sexp_check = of_sexp_check vars_of_sexp vars_check

let rec expr_to_sexp = function
  | Const x -> Conv.sexp_of_int x
  | Var idx -> Sexp.Atom ("$" ^ string_of_int idx)
  | Add (e1, e2) -> Sexp.List [Sexp.Atom "+" ; expr_to_sexp e1; expr_to_sexp e2]
  | Sub (e1, e2) -> Sexp.List [Sexp.Atom "-" ; expr_to_sexp e1; expr_to_sexp e2]
  | Mul (e1, e2) -> Sexp.List [Sexp.Atom "*" ; expr_to_sexp e1; expr_to_sexp e2]
  | Div (e1, e2) -> Sexp.List [Sexp.Atom "/" ; expr_to_sexp e1; expr_to_sexp e2]

let rec expr_of_sexp = function
  | Sexp.List [Sexp.Atom "+"; e1; e2] -> Add (expr_of_sexp e1, expr_of_sexp e2)
  | Sexp.List [Sexp.Atom "-"; e1; e2] -> Sub (expr_of_sexp e1, expr_of_sexp e2)
  | Sexp.List [Sexp.Atom "*"; e1; e2] -> Mul (expr_of_sexp e1, expr_of_sexp e2)
  | Sexp.List [Sexp.Atom "/"; e1; e2] -> Div (expr_of_sexp e1, expr_of_sexp e2)
  | Sexp.Atom s when String.starts_with ~prefix:"$" s ->
    Var (String.sub s 1 (String.length s - 1) |> int_of_string)
  | s -> Const (Conv.int_of_sexp s)

let rec expr_depth e =
  match e with
  | Const _ | Var _ -> 0
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2) ->
    1 + max (expr_depth e1) (expr_depth e2)

let expr_check e k = expr_depth e <= k

let expr_of_sexp_check = of_sexp_check expr_of_sexp expr_check
