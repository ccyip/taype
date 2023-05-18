open Containers
module HashSet = CCHashSet

module Logs = struct
  let channel : out_channel option ref = ref None
  let set_channel oc = channel := Some oc

  let info header msg =
    match !channel with
    | Some oc ->
        IO.write_line oc "================================";
        IO.write_line oc header;
        IO.write_line oc "--------------------------------";
        IO.write_line oc msg
    | None -> ()
end

type ty = string list [@@deriving show]
type goal = { name : string; ty : ty } [@@deriving show]

module Goal = struct
  type t = goal [@@deriving show]

  let equal = Equal.poly
  let hash { name; ty } = Hash.(pair string (list string)) (name, ty)

  let subst model { name; ty } =
    let get x = List.Assoc.get_exn x model ~eq:Equal.string in
    { name; ty = List.map get ty }
end

type formula =
  | Eq of string * string
  | Or of formula list
  | And of formula list
  | Not of formula

type formulas = formula list

type def = {
  vars : (string * string) list;
  ty : ty;
  formulas : formulas;
  subgoals : goal list;
}

type model = (string * string) list [@@deriving show]

module SolverCtx = struct
  type solver = {
    svr : Z3.Solver.solver;
    ty : ty;
    subgoals : goal list;
    tbl : (string, Z3.Expr.expr) Hashtbl.t;
  }

  type t = (string, solver) Hashtbl.t

  let solver_ctx : t = Hashtbl.create 1024
  let ctx = Z3.mk_context []
  let sort_tbl : (string, Z3.Sort.sort) Hashtbl.t = Hashtbl.create 1024
  let ctor_tbl : (string, Z3.Expr.expr) Hashtbl.t = Hashtbl.create 1024
  let find k = Hashtbl.find solver_ctx k

  let init_class clss =
    let repr = List.hd clss in
    let mk_ctor x =
      Z3.Datatype.mk_constructor_s ctx x
        (Z3.Symbol.mk_string ctx ("is-" ^ x))
        [] [] []
    in
    let ctors = List.map mk_ctor clss in
    let sort = Z3.Datatype.mk_sort_s ctx (repr ^ "-class") ctors in
    let get_ctor_expr ctor =
      Z3.Datatype.Constructor.get_constructor_decl ctor
      |> Z3.Expr.mk_const_f ctx
    in
    let exprs = List.map get_ctor_expr ctors in
    Hashtbl.add sort_tbl repr sort;
    Hashtbl.add_iter ctor_tbl (List.to_iter (List.combine clss exprs))

  let init_var solver (name, cls) =
    let sort = Hashtbl.find sort_tbl cls in
    let expr = Z3.Expr.mk_const_s ctx name sort in
    Hashtbl.add solver.tbl name expr

  let find_expr tbl x =
    match Hashtbl.get tbl x with Some e -> e | None -> Hashtbl.find ctor_tbl x

  let rec expr_of_formula tbl = function
    | Eq (lhs, rhs) ->
        let lhs = find_expr tbl lhs in
        let rhs = find_expr tbl rhs in
        Z3.Boolean.mk_eq ctx lhs rhs
    | Or [] -> Z3.Boolean.mk_false ctx
    | Or [ f ] -> expr_of_formula tbl f
    | Or disj -> Z3.Boolean.mk_or ctx (List.map (expr_of_formula tbl) disj)
    | And [] -> Z3.Boolean.mk_true ctx
    | And [ f ] -> expr_of_formula tbl f
    | And conj -> Z3.Boolean.mk_and ctx (List.map (expr_of_formula tbl) conj)
    | Not f -> Z3.Boolean.mk_not ctx (expr_of_formula tbl f)

  let add_formula solver f =
    Z3.Solver.add solver.svr [ expr_of_formula solver.tbl f ]

  let add_formulas solver = List.iter (add_formula solver)

  let init_def (name, { vars; ty; formulas; subgoals }) =
    let tbl = Hashtbl.create 1024 in
    (* FIXME: use Z3.Optimize *)
    (* TODO: add cost constraints *)
    let solver = { svr = Z3.Solver.mk_simple_solver ctx; ty; subgoals; tbl } in
    List.iter (init_var solver) vars;
    add_formulas solver formulas;
    Logs.info ("Created solver for " ^ name) (Z3.Solver.to_string solver.svr);
    Hashtbl.add solver_ctx name solver

  let init classes defs =
    List.iter init_class classes;
    List.iter init_def defs

  let convert_model model =
    let convert x e =
      let e = Z3.Model.eval model e true |> Option.get_exn_or "eval" in
      let name =
        Z3.Expr.get_func_decl e |> Z3.FuncDecl.get_name |> Z3.Symbol.get_string
      in
      (x, name)
    in
    Hashtbl.map_list convert

  let mk_ty_eq = List.map2 (fun x y -> Eq (x, y))

  let check_with ({ svr; _ } as solver) ty =
    let fs = mk_ty_eq solver.ty ty in
    Z3.Solver.push svr;
    add_formulas solver fs;
    let result =
      match Z3.Solver.check svr [] with
      | SATISFIABLE -> (
          match Z3.Solver.get_model svr with
          | Some model -> Some (convert_model model solver.tbl)
          | None -> None)
      | UNSATISFIABLE | UNKNOWN -> None
    in
    Z3.Solver.pop svr 1;
    result

  let refuse goal =
    let refuse1 _ solver =
      let add subgoal =
        if String.(goal.name = subgoal.name) then
          add_formula solver (Not (And (mk_ty_eq goal.ty subgoal.ty)))
      in
      List.iter add solver.subgoals
    in
    Hashtbl.iter refuse1 solver_ctx
end

module GoalSet = struct
  include HashSet.Make (Goal)

  let pp = pp Goal.pp
end

type goal_state = Given | Refused | In_progress | Solved of model * GoalSet.t
[@@deriving show]

module GoalCtx = struct
  module Hashtbl = Hashtbl.Make' (Goal)

  type t = goal_state Hashtbl.t

  let pp = Hashtbl.pp Goal.pp pp_goal_state
  let goal_ctx : t = Hashtbl.create 1024
  let set k v = Hashtbl.replace goal_ctx k v
  let unset k = Hashtbl.remove goal_ctx k
  let get k = Hashtbl.get goal_ctx k

  let init axioms =
    let init1 (name, tys) = List.iter (fun ty -> set { name; ty } Given) tys in
    List.iter init1 axioms

  let propagate goal new_deps =
    let replace_deps _ = function
      | Solved (_, deps) when GoalSet.mem deps goal ->
          GoalSet.remove deps goal;
          GoalSet.union_mut ~into:deps new_deps
      | _ -> ()
    in
    Hashtbl.iter replace_deps goal_ctx

  let invalidate goal =
    SolverCtx.refuse goal;
    let remove _ = function
      | Solved (_, deps) when GoalSet.mem deps goal -> None
      | st -> Some st
    in
    Hashtbl.filter_map_inplace remove goal_ctx

  let get_refused () =
    let refused (goal, st) = match st with Refused -> Some goal | _ -> None in
    Hashtbl.to_list goal_ctx |> List.filter_map refused

  let get_solved () =
    let solved (goal, st) =
      match st with
      | Solved (model, deps) ->
          assert (GoalSet.cardinal deps = 0);
          Some (goal, model)
      | _ -> None
    in
    Hashtbl.to_list goal_ctx |> List.filter_map solved
end

let rec solve_ goal =
  let solver = SolverCtx.find goal.name in
  match SolverCtx.check_with solver goal.ty with
  | Some model ->
      let subgoals = List.map (Goal.subst model) solver.subgoals in
      let results = List.map solve_goal subgoals in
      if List.mem Refused results then
        (* Solvers have been updated. *)
        solve_ goal
      else
        let deps = GoalSet.create 1024 in
        let add_in_progress g = function
          | In_progress -> GoalSet.insert deps g
          | _ -> ()
        in
        List.iter2 add_in_progress subgoals results;
        let add_deps = function
          | Solved (_, deps') -> GoalSet.union_mut ~into:deps deps'
          | _ -> ()
        in
        List.iter add_deps results;
        GoalSet.remove deps goal;
        GoalCtx.propagate goal deps;
        let st = Solved (model, deps) in
        GoalCtx.set goal st;
        st
  | None ->
      GoalCtx.invalidate goal;
      let st = Refused in
      GoalCtx.set goal st;
      st

and solve_goal goal =
  match GoalCtx.get goal with
  | Some st -> st
  | None ->
      GoalCtx.set goal In_progress;
      solve_ goal

let solve goals classes axioms defs : ((goal * model) list, goal list) result =
  GoalCtx.init axioms;
  SolverCtx.init classes defs;

  let results = List.map solve_goal goals in
  if List.mem Refused results then Error (GoalCtx.get_refused ())
  else Ok (GoalCtx.get_solved ())
