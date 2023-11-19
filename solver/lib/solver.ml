open Containers
module Graph = CCGraph
module HashSet = CCHashSet

module Logs = struct
  let channel : out_channel option ref = ref None
  let set_channel oc = channel := Some oc

  type log = { printf : 'a. ('a, Format.formatter, unit) format -> 'a }
  [@@unboxed]

  let info msgf =
    match !channel with
    | Some oc ->
        Format.with_out_chan oc (fun fmt ->
            Format.fprintf fmt "%s@."
              "================================================================";
            msgf
              {
                printf =
                  (fun (type a) (s : (a, Format.formatter, unit) format) ->
                    Format.fprintf fmt s);
              };
            Format.fprintf fmt "@.")
    | None -> ()
end

type ty = string list

let raw_sexp_of_ty = List.map Sexp.atom
let sexp_of_ty ty = Sexp.of_list (raw_sexp_of_ty ty)

type goal = { name : string; ty : ty }

module Goal = struct
  type t = goal

  let to_sexp { name; ty } = Sexp.of_variant name (raw_sexp_of_ty ty)
  let pp = Format.map to_sexp Sexp.pp
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
  signs : bool list;
  ty : ty;
  formulas : formulas;
  subgoals : goal list;
}

type model = (string * string) list

let raw_sexp_of_model =
  List.map (fun assn -> Sexp.of_pair (Pair.map_same Sexp.atom assn))

let pp_model =
  Format.map raw_sexp_of_model (List.pp ~pp_sep:Format.space Sexp.pp)

module SolverCtx = struct
  type solver = {
    svr : Z3.Optimize.optimize;
    signs : bool list;
    ty : ty;
    subgoals : goal list;
    tbl : (string, Z3.Expr.expr) Hashtbl.t;
    mutable stats : float list;
    mutable refused : ty list;
  }

  type t = (string, solver) Hashtbl.t

  let solver_ctx : t = Hashtbl.create 1024
  let ctx = Z3.mk_context []
  let sort_tbl : (string, Z3.Sort.sort) Hashtbl.t = Hashtbl.create 1024
  let ty_tbl : (string, Z3.Expr.expr) Hashtbl.t = Hashtbl.create 1024
  let cls_tbl : (string, (string * int) list) Hashtbl.t = Hashtbl.create 1024

  let coer_tbl : (string, string list * string list) Hashtbl.t =
    Hashtbl.create 1024

  let init_class cls =
    let names = List.map fst cls in
    let repr = List.hd names in
    let mk_ctor x =
      Z3.Datatype.mk_constructor_s ctx x
        (Z3.Symbol.mk_string ctx ("is-" ^ x))
        [] [] []
    in
    let ctors = List.map mk_ctor names in
    let sort = Z3.Datatype.mk_sort_s ctx (repr ^ "-class") ctors in
    let get_ctor_expr ctor =
      Z3.Datatype.Constructor.get_constructor_decl ctor
      |> Z3.Expr.mk_const_f ctx
    in
    let exprs = List.map get_ctor_expr ctors in
    Hashtbl.add sort_tbl repr sort;
    Hashtbl.add cls_tbl repr cls;
    Hashtbl.add_iter ty_tbl (List.to_iter (List.combine names exprs))

  let init_coers coers =
    let graph = Graph.of_list ~eq:Equal.string coers in
    let decendants v =
      Graph.Traverse.dfs
        ~tbl:(Graph.mk_table ~eq:Equal.string ~hash:Hash.string 1024)
        ~graph (Graph.Iter.return v)
      |> Graph.Iter.to_list
    in
    let tbl = Hashtbl.map_list (fun k _ -> (k, decendants k)) ty_tbl in
    let ancestors v =
      List.filter_map (fun (k, ds) -> Option.return_if (List.mem v ds) k) tbl
    in
    let tbl = List.map (fun (k, ds) -> (k, (ds, ancestors k))) tbl in
    Hashtbl.add_iter coer_tbl (List.to_iter tbl)

  let find_expr tbl x =
    match Hashtbl.get tbl x with Some e -> e | None -> Hashtbl.find ty_tbl x

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
    Z3.Optimize.add solver.svr [ expr_of_formula solver.tbl f ]

  let add_formulas solver = List.iter (add_formula solver)

  let init_var solver (var, repr) =
    let sort = Hashtbl.find sort_tbl repr in
    let expr = Z3.Expr.mk_const_s ctx var sort in
    Hashtbl.add solver.tbl var expr;
    let cls = Hashtbl.find cls_tbl repr in
    let group = Z3.Symbol.mk_string ctx var in
    let add_cost (name, cost) =
      if cost > 0 then
        let e = expr_of_formula solver.tbl (Not (Eq (var, name))) in
        ignore @@ Z3.Optimize.add_soft solver.svr e (Int.to_string cost) group
    in
    List.iter add_cost cls

  let init_def (name, { vars; signs; ty; formulas; subgoals }) =
    let tbl = Hashtbl.create 1024 in
    let solver =
      {
        svr = Z3.Optimize.mk_opt ctx;
        signs;
        ty;
        subgoals;
        tbl;
        stats = [];
        refused = [];
      }
    in
    List.iter (init_var solver) vars;
    add_formulas solver formulas;
    Logs.info (fun log ->
        log.printf "Created solver for %s@.%s" name
          (Z3.Optimize.to_string solver.svr));
    Hashtbl.add solver_ctx name solver

  let init classes coers defs =
    List.iter init_class classes;
    init_coers coers;
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
  let get_subgoals goal = (Hashtbl.find solver_ctx goal.name).subgoals

  let check (goal : goal) =
    let solver = Hashtbl.find solver_ctx goal.name in
    let svr = solver.svr in
    let fs = mk_ty_eq solver.ty goal.ty in
    Z3.Optimize.push svr;
    add_formulas solver fs;
    let stamp = Unix.gettimeofday () in
    let status = Z3.Optimize.check svr in
    let now = Unix.gettimeofday () in
    solver.stats <- (now -. stamp) :: solver.stats;
    let result =
      match status with
      | SATISFIABLE -> (
          match Z3.Optimize.get_model svr with
          | Some model -> Some (convert_model model solver.tbl)
          | None -> None)
      | UNSATISFIABLE | UNKNOWN -> None
    in
    Logs.info (fun log ->
        log.printf "Finished checking %a@.%s" Goal.pp goal
          (Z3.Optimize.get_statistics svr |> Z3.Statistics.to_string));
    Z3.Optimize.pop svr;
    result

  let rec has_coer signs t1 t2 =
    match (signs, t1, t2) with
    | [], [], [] -> true
    | s :: signs, a1 :: t1, a2 :: t2 ->
        let decendants, ancestors = Hashtbl.find coer_tbl a1 in
        List.mem a2 (if s then decendants else ancestors)
        && has_coer signs t1 t2
    | _, _, _ -> raise (Invalid_argument "arguments have different lengths")

  let goal_has_coer goal1 goal2 =
    if String.(goal1.name = goal2.name) then
      let solver = Hashtbl.find solver_ctx goal1.name in
      has_coer solver.signs goal1.ty goal2.ty
    else false

  let is_refused goal =
    let solver = Hashtbl.find solver_ctx goal.name in
    List.exists (fun ty -> has_coer solver.signs goal.ty ty) solver.refused

  let get_refused () =
    let get_refused1 (name, solver) =
      List.map (fun ty -> { name; ty }) solver.refused
    in
    Hashtbl.to_list solver_ctx |> List.concat_map get_refused1

  let add_refused solver ty =
    let refused =
      List.filter (fun ty' -> not (has_coer solver.signs ty' ty)) solver.refused
    in
    solver.refused <- ty :: refused

  let mk_ty_in x set = Or (List.map (fun y -> Eq (x, y)) set)

  let rec mk_ty_coer signs xs ty =
    match (signs, xs, ty) with
    | [], [], [] -> []
    | s :: signs, x :: xs, a :: ty ->
        let decendants, ancestors = Hashtbl.find coer_tbl a in
        let f = mk_ty_in x (if s then ancestors else decendants) in
        f :: mk_ty_coer signs xs ty
    | _, _, _ -> raise (Invalid_argument "arguments have different lengths")

  let add_refutation name solver signs xs ty =
    let e = expr_of_formula solver.tbl @@ Not (And (mk_ty_coer signs xs ty)) in
    Z3.Optimize.add solver.svr [ e ];
    Logs.info (fun log ->
        log.printf "Added refutation to %s@.%s" name (Z3.Expr.to_string e))

  let refuse goal =
    let solver_refused = Hashtbl.find solver_ctx goal.name in
    add_refused solver_refused goal.ty;
    let refuse1 name solver =
      let may_add_refutation subgoal =
        if String.(goal.name = subgoal.name) then
          add_refutation name solver solver_refused.signs subgoal.ty goal.ty
      in
      List.iter may_add_refutation solver.subgoals
    in
    Hashtbl.iter refuse1 solver_ctx
end

module GoalSet = struct
  include HashSet.Make (Goal)

  let pp = pp Goal.pp
end

(* [Refused] does not appear in the goal context, and it is only used as one of
   the solver results. Refused goals are managed by the solver context
   [SolverCtx.solver.refused]. *)
type goal_state = Given | Refused | In_progress | Solved of model * GoalSet.t
[@@deriving show { with_path = false }]

module GoalCtx = struct
  module Hashtbl = Hashtbl.Make' (Goal)

  type t = goal_state Hashtbl.t

  let pp = Hashtbl.pp Goal.pp pp_goal_state
  let show = Format.to_string pp
  let goal_ctx : t = Hashtbl.create 1024
  let set k v = Hashtbl.replace goal_ctx k v
  let unset k = Hashtbl.remove goal_ctx k
  let get k = Hashtbl.get goal_ctx k

  let init axioms =
    let init1 (name, tys) = List.iter (fun ty -> set { name; ty } Given) tys in
    List.iter init1 axioms

  let propagate goal new_deps =
    let replace_deps goal' = function
      | Solved (_, deps) when GoalSet.mem deps goal ->
          GoalSet.remove deps goal;
          GoalSet.union_mut ~into:deps new_deps;
          Logs.info (fun log ->
              log.printf "Propagated assumptions of %a to %a" Goal.pp goal
                Goal.pp goal';
              log.printf ",@ whose assumptions are now:@.%a" GoalSet.pp deps)
      | _ -> ()
    in
    Hashtbl.iter replace_deps goal_ctx

  let invalidate goal =
    let remove goal' = function
      | Solved (_, deps)
        when GoalSet.exists (fun dep -> SolverCtx.goal_has_coer dep goal) deps
        ->
          Logs.info (fun log ->
              log.printf "Reset %a@ which depends on %a" Goal.pp goal' Goal.pp
                goal);
          None
      | st -> Some st
    in
    Hashtbl.filter_map_inplace remove goal_ctx

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
  Logs.info (fun log -> log.printf "Solving %a" Goal.pp goal);
  match SolverCtx.check goal with
  | Some model ->
      let subgoals =
        List.map (Goal.subst model) (SolverCtx.get_subgoals goal)
      in
      Logs.info (fun log ->
          if not (List.is_empty subgoals) then
            log.printf "%a requires subgoals@.%a" Goal.pp goal (List.pp Goal.pp)
              subgoals);
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
        Logs.info (fun log ->
            if GoalSet.cardinal deps = 0 then
              log.printf "Completely solved %a" Goal.pp goal
            else
              log.printf "Solved %a with assumptions@.%a" Goal.pp goal
                GoalSet.pp deps);
        GoalCtx.propagate goal deps;
        let st = Solved (model, deps) in
        GoalCtx.set goal st;
        st
  | None ->
      Logs.info (fun log -> log.printf "Refused %a" Goal.pp goal);
      SolverCtx.refuse goal;
      GoalCtx.invalidate goal;
      GoalCtx.unset goal;
      Refused

and solve_goal goal =
  match GoalCtx.get goal with
  | Some st -> st
  | None when SolverCtx.is_refused goal -> Refused
  | None ->
      GoalCtx.set goal In_progress;
      solve_ goal

let json_of_stat () : Yojson.Basic.t =
  let atoms k = List.length (Hashtbl.find SolverCtx.solver_ctx k).ty in
  let queries v = List.map (fun x -> `Float x) v in
  let go k solver =
    ( k,
      `Assoc
        [
          ("#atoms", `Int (atoms k));
          ("queries", `List (queries SolverCtx.(solver.stats)));
        ] )
  in
  let stat = Hashtbl.map_list go SolverCtx.solver_ctx in
  let atoms =
    Hashtbl.fold (fun _ v n -> List.length v + n) SolverCtx.cls_tbl 0
  in
  `Assoc [ ("statistics", `Assoc stat); ("#atoms", `Int atoms) ]

let solve goals classes axioms coers defs =
  GoalCtx.init axioms;
  SolverCtx.init classes coers defs;

  let results = List.map solve_goal goals in
  Logs.info (fun log ->
      log.printf "Final goal context@.%a" GoalCtx.pp GoalCtx.goal_ctx);
  Logs.info (fun log ->
      log.printf "Statistics@.%a"
        (Hashtbl.pp String.pp (fun fmt solver ->
             List.pp Float.pp fmt SolverCtx.(solver.stats)))
        SolverCtx.solver_ctx);
  let output =
    if List.mem Refused results then Error (SolverCtx.get_refused ())
    else Ok (GoalCtx.get_solved ())
  in
  (output, json_of_stat ())
