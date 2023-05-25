open Sexplib
open Common

module M (Driver : Taype_driver.S) = struct
  open Record.M (Driver)

  let patient_to_sexp (Patient (id, age, h, w)) =
    Conv.sexp_of_list Conv.sexp_of_int [ id; age; h; w ]

  let patient_of_sexp s =
    match Conv.list_of_sexp Conv.int_of_sexp s with
    | [ id; age; h; w ] -> Patient (id, age, h, w)
    | _ -> failwith "Cannot parse as patient"

  let patient_check (Patient (id, _, h, w)) = function
    | Known_id id' -> id = id'
    | Known_data (h', w') -> h = h' && w = w'

  let patient_of_sexp_check = of_sexp_check patient_of_sexp patient_check

  let rec db_to_list = function
    | Db_Empty -> []
    | Db_More (p, ps) -> p :: db_to_list ps

  let rec db_of_list = function
    | [] -> Db_Empty
    | p :: ps -> Db_More (p, db_of_list ps)

  let db_to_sexp ps = db_to_list ps |> Conv.sexp_of_list patient_to_sexp
  let db_of_sexp s = Conv.list_of_sexp patient_of_sexp s |> db_of_list

  let rec db_check ps vs =
    match ps with
    | Db_Empty -> (
        match vs with Db_View_Empty -> true | Db_View_More _ -> false)
    | Db_More (p, ps') -> (
        match vs with
        | Db_View_Empty -> false
        | Db_View_More (v, vs') -> patient_check p v && db_check ps' vs')

  let db_of_sexp_check = of_sexp_check db_of_sexp db_check

  let rec bmi_db_to_list = function
    | Nil -> []
    | Cons (id, bmi, bmis) -> (id, bmi) :: bmi_db_to_list bmis

  let rec bmi_db_of_list = function
    | [] -> Nil
    | (id, bmi) :: bmis -> Cons (id, bmi, bmi_db_of_list bmis)

  let bmi_db_to_sexp bmis =
    bmi_db_to_list bmis
    |> Conv.sexp_of_list (Conv.sexp_of_pair Conv.sexp_of_int Conv.sexp_of_int)

  let bmi_db_of_sexp s =
    Conv.list_of_sexp (Conv.pair_of_sexp Conv.int_of_sexp Conv.int_of_sexp) s
    |> bmi_db_of_list

  let bmi_db_check bmis k = List.length (bmi_db_to_list bmis) = k
  let bmi_db_of_sexp_check = of_sexp_check bmi_db_of_sexp bmi_db_check

  let patient_view_to_sexp = function
    | Known_id id -> Sexp.List [ Sexp.Atom "i"; Conv.sexp_of_int id ]
    | Known_data (h, w) ->
        Sexp.List [ Sexp.Atom "d"; Conv.sexp_of_int h; Conv.sexp_of_int w ]

  let patient_view_of_sexp = function
    | Sexp.List [ Sexp.Atom "i"; id ] -> Known_id (Conv.int_of_sexp id)
    | Sexp.List [ Sexp.Atom "d"; h; w ] ->
        Known_data (Conv.int_of_sexp h, Conv.int_of_sexp w)
    | _ -> failwith "Cannot parse as patient view"

  let rec db_view_to_list = function
    | Db_View_Empty -> []
    | Db_View_More (v, vs) -> v :: db_view_to_list vs

  let rec db_view_of_list = function
    | [] -> Db_View_Empty
    | v :: vs -> Db_View_More (v, db_view_of_list vs)

  let db_view_to_sexp vs =
    db_view_to_list vs |> Conv.sexp_of_list patient_view_to_sexp

  let db_view_of_sexp s =
    Conv.list_of_sexp patient_view_of_sexp s |> db_view_of_list

  let feature_to_sexp = function
    | Age -> Sexp.Atom "a"
    | Height -> Sexp.Atom "h"
    | Weight -> Sexp.Atom "w"

  let feature_of_sexp = function
    | Sexp.Atom "a" -> Age
    | Sexp.Atom "h" -> Height
    | Sexp.Atom "w" -> Weight
    | _ -> failwith "Cannot parse as feature"

  let rec dtree_to_sexp = function
    | Node (f, thrd, lt, rt) ->
        Sexp.List
          [
            feature_to_sexp f;
            Conv.sexp_of_int thrd;
            dtree_to_sexp lt;
            dtree_to_sexp rt;
          ]
    | Leaf d -> Conv.sexp_of_bool d

  let rec dtree_of_sexp = function
    | Sexp.List [ f; thrd; lt; rt ] ->
        Node
          ( feature_of_sexp f,
            Conv.int_of_sexp thrd,
            dtree_of_sexp lt,
            dtree_of_sexp rt )
    | s -> Leaf (Conv.bool_of_sexp s)

  let rec dtree_view_to_sexp = function
    | Node_View (f, lt, rt) ->
        Sexp.List
          [ feature_to_sexp f; dtree_view_to_sexp lt; dtree_view_to_sexp rt ]
    | Leaf_View -> Sexp.List []

  let rec dtree_view_of_sexp = function
    | Sexp.List [ f; lt; rt ] ->
        Node_View
          (feature_of_sexp f, dtree_view_of_sexp lt, dtree_view_of_sexp rt)
    | Sexp.List [] -> Leaf_View
    | _ -> failwith "Cannot parse as dtree_view"

  let rec dtree_check t = function
    | Node_View (f, lv, rv) -> (
        match t with
        | Node (f', _, lt, rt) ->
            f = f' && dtree_check lt lv && dtree_check rt rv
        | Leaf _ -> false)
    | Leaf_View -> ( match t with Node _ -> false | Leaf _ -> true)

  let dtree_of_sexp_check = of_sexp_check dtree_of_sexp dtree_check
end
