open Containers
open Lib.Solver

exception Ill_formed_input

let parse_atom = function `Atom x -> x | _ -> raise Ill_formed_input
let parse_atoms = List.map parse_atom

let parse_atom_list = function
  | `List l -> parse_atoms l
  | _ -> raise Ill_formed_input

let parse_atom_lists = List.map parse_atom_list

let parse_goal = function
  | `List (`Atom name :: ty) -> (name, parse_atoms ty)
  | _ -> raise Ill_formed_input

let parse_goals = function
  | `List (`Atom "goals" :: goals) -> List.map parse_goal goals
  | _ -> raise Ill_formed_input

let parse_classes = function
  | `List (`Atom "classes" :: (_ :: _ as classes)) -> parse_atom_lists classes
  | _ -> raise Ill_formed_input

let parse_axioms = function
  | `List (`Atom "axioms" :: axioms) ->
      let parse_axiom = function
        | `List (`Atom name :: tys) -> (name, parse_atom_lists tys)
        | _ -> raise Ill_formed_input
      in
      List.map parse_axiom axioms
  | _ -> raise Ill_formed_input

let rec parse_formula = function
  | `List [ `Atom "="; `Atom lhs; `Atom rhs ] -> Eq (lhs, rhs)
  | `List (`Atom "or" :: disj) ->
      let parse1 = function
        | `List conj -> And (List.map parse_formula conj)
        | _ -> raise Ill_formed_input
      in
      Or (List.map parse1 disj)
  | _ -> raise Ill_formed_input

let parse_def vars ty formulas subgoals =
  let parse_var = function
    | `List [ `Atom name; `Atom cls ] -> (name, cls)
    | _ -> raise Ill_formed_input
  in
  {
    vars = List.map parse_var vars;
    ty = parse_atoms ty;
    formulas = List.map parse_formula formulas;
    subgoals = List.map parse_goal subgoals;
  }

let parse_defs = function
  | `List (`Atom "definitions" :: defs) ->
      let parse1 = function
        | `List [ `Atom name; `List vars; `List ty; `List fs; `List gs ] ->
            (name, parse_def vars ty fs gs)
        | _ -> raise Ill_formed_input
      in
      List.map parse1 defs
  | _ -> raise Ill_formed_input

let parse_input = function
  | [ goals; classes; axioms; defs ] ->
      ( parse_goals goals,
        parse_classes classes,
        parse_axioms axioms,
        parse_defs defs )
  | _ -> raise Ill_formed_input

let sexp_of_output = function
  | Ok _ -> `List [ `Atom "solved" ]
  | Error _ -> `List [ `Atom "failed" ]

let main input_file output_file =
  let input = Sexp.parse_file_list input_file |> Result.get_or_failwith in
  let goals, classes, axioms, defs = parse_input input in
  let output = solve goals classes axioms defs in
  Sexp.to_file output_file (sexp_of_output output)

let () =
  if Array.length Sys.argv < 3 then invalid_arg "not enough"
  else
    let input_file = Sys.argv.(1) in
    let output_file = Sys.argv.(2) in
    let log_file =
      if Array.length Sys.argv > 3 then Some Sys.argv.(3) else None
    in
    match log_file with
    | Some file ->
        IO.with_out ~flags:[ Open_wronly; Open_creat; Open_text; Open_trunc ]
          file (fun oc ->
            log_channel := Some oc;
            main input_file output_file)
    | None -> main input_file output_file
