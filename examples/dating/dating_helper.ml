open Sexplib
open Common

module M (Driver : Taype_driver.S) = struct
  open Dating.M (Driver)

  let profile_of_sexp = function
    | Sexp.List [ g; a; h; i ] ->
        Profile
          ( Conv.int_of_sexp g,
            Conv.int_of_sexp a,
            Conv.int_of_sexp h,
            Conv.int_of_sexp i )
    | _ -> assert false

  let feature_of_string = function
    | "g" -> Gender
    | "a" -> Age
    | "h" -> Height
    | "i" -> Income
    | _ -> assert false

  let rec exp_of_sexp = function
    | Sexp.List [ Sexp.Atom "+"; e1; e2 ] -> Add (exp_of_sexp e1, exp_of_sexp e2)
    | Sexp.Atom s when String.starts_with ~prefix:"&" s -> 
      Var (true, String.sub s 1 (String.length s - 1) |> feature_of_string)
    | Sexp.Atom s when String.starts_with ~prefix:"$" s -> 
      Var (false, String.sub s 1 (String.length s - 1) |> feature_of_string)
    | s -> Const (Conv.int_of_sexp s)

  let rec pred_of_sexp = function
    | Sexp.List [ Sexp.Atom "<="; e1; e2] -> Le (exp_of_sexp e1, exp_of_sexp e2)
    | Sexp.List [ Sexp.Atom "and"; p1; p2] -> And (pred_of_sexp p1, pred_of_sexp p2)
    | Sexp.List [ Sexp.Atom "or"; p1; p2] -> Or (pred_of_sexp p1, pred_of_sexp p2)
    | Sexp.List [ Sexp.Atom "not"; p1] -> Not (pred_of_sexp p1)
    | _ -> assert false

  let rec exp_depth = function
    | Const _ | Var _ -> 0
    | Add (e1, e2) -> 1 + max (exp_depth e1) (exp_depth e2)

  let rec pred_depth = function
    | Le (e1, e2) -> max (exp_depth e1) (exp_depth e2)
    | And (p1, p2) | Or (p1, p2) -> 1 + max (pred_depth p1) (pred_depth p2)
    | Not p -> 1 + pred_depth p

  let pred_check p k = pred_depth p <= k
  let pred_of_sexp_check = of_sexp_check pred_of_sexp pred_check
end
