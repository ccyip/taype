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
  | `List (`Atom name :: ty) -> { name; ty = parse_atoms ty }
  | _ -> raise Ill_formed_input

let parse_goals = function
  | `List (`Atom "goals" :: goals) -> List.map parse_goal goals
  | _ -> raise Ill_formed_input

let parse_classes = function
  | `List (`Atom "classes" :: (_ :: _ as classes)) ->
      let parse_base = function
        | `List [ `Atom base; `Atom cost ] -> (base, Int.of_string_exn cost)
        | _ -> raise Ill_formed_input
      in
      let parse_class = function
        | `List cls -> List.map parse_base cls
        | _ -> raise Ill_formed_input
      in
      List.map parse_class classes
  | _ -> raise Ill_formed_input

let parse_axioms = function
  | `List (`Atom "axioms" :: axioms) ->
      let parse_axiom = function
        | `List (`Atom name :: tys) -> (name, parse_atom_lists tys)
        | _ -> raise Ill_formed_input
      in
      List.map parse_axiom axioms
  | _ -> raise Ill_formed_input

let parse_coers = function
  | `List (`Atom "coerces" :: coers) ->
      let parse_coer = function
        | `List [ `Atom orig; `Atom dest ] -> (orig, dest)
        | _ -> raise Ill_formed_input
      in
      List.map parse_coer coers
  | _ -> raise Ill_formed_input

let rec parse_formula = function
  | `List [ `Atom "="; `Atom lhs; `Atom rhs ] -> Eq (lhs, rhs)
  | `List (`Atom "or" :: disj) ->
      let parse_conj = function
        | `List conj -> And (List.map parse_formula conj)
        | _ -> raise Ill_formed_input
      in
      Or (List.map parse_conj disj)
  | _ -> raise Ill_formed_input

let parse_def vars signs ty formulas subgoals =
  let parse_var = function
    | `List [ `Atom name; `Atom cls ] -> (name, cls)
    | _ -> raise Ill_formed_input
  in
  let parse_sign = function
    | `Atom "+" -> true
    | `Atom "-" -> false
    | _ -> raise Ill_formed_input
  in
  {
    vars = List.map parse_var vars;
    signs = List.map parse_sign signs;
    ty = parse_atoms ty;
    formulas = List.map parse_formula formulas;
    subgoals = List.map parse_goal subgoals;
  }

let parse_defs = function
  | `List (`Atom "definitions" :: defs) ->
      let parse1 = function
        | `List
            [
              `Atom name;
              `List vars;
              `List signs;
              `List ty;
              `List formulas;
              `List subgoals;
            ] ->
            (name, parse_def vars signs ty formulas subgoals)
        | _ -> raise Ill_formed_input
      in
      List.map parse1 defs
  | _ -> raise Ill_formed_input

let parse_input = function
  | [ goals; classes; axioms; coers; defs ] ->
      ( parse_goals goals,
        parse_classes classes,
        parse_axioms axioms,
        parse_coers coers,
        parse_defs defs )
  | _ -> raise Ill_formed_input

let sexp_of_output = function
  | Ok solved ->
      let to_sexp (goal, model) =
        Sexp.of_variant goal.name (sexp_of_ty goal.ty :: raw_sexp_of_model model)
      in
      Sexp.of_variant "solved" @@ List.map to_sexp solved
  | Error refused -> Sexp.of_variant "failed" @@ List.map Goal.to_sexp refused

let main input_file output_file stat_file =
  let input =
    match input_file with
    | "-in" -> Sexp.parse_chan_list stdin
    | _ -> Sexp.parse_file_list input_file
  in
  let goals, classes, axioms, coers, defs =
    parse_input (Result.get_or_failwith input)
  in
  let output, stat = solve goals classes axioms coers defs in
  let output = sexp_of_output output in
  (match output_file with
  | "-out" -> Sexp.to_chan stdout output
  | _ -> Sexp.to_file output_file output);
  match stat_file with
  | Some file ->
      IO.with_out_a file (fun oc ->
          Yojson.Basic.to_channel oc stat;
          output_char oc '\n')
  | None -> ()

let () =
  if Array.length Sys.argv < 3 then invalid_arg "not enough"
  else
    let input_file = Sys.argv.(1) in
    let output_file = Sys.argv.(2) in
    let log_file =
      if Array.length Sys.argv > 3 then Some Sys.argv.(3) else None
    in
    let stat_file =
      if Array.length Sys.argv > 4 then Some Sys.argv.(4) else None
    in
    match log_file with
    | Some file ->
        IO.with_out file (fun oc ->
            Logs.set_channel oc;
            main input_file output_file stat_file)
    | None -> main input_file output_file stat_file
