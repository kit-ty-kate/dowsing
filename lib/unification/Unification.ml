(** AC Unification

    Follow the algorithm in
    Competing for the AC-unification Race by Boudet (1993)
*)

module Logs = (val Logs.(src_log @@ Src.create __MODULE__))
let _info = Logs.info
let debug = Logs.debug

module Env = Env
module Subst = Subst

(** {2 A stack of unification pairs} *)
module Stack : sig

  type elt =
    | Var of Variable.t * Type.t
    | Expr of Type.t * Type.t

  type t

  val empty : t
  val pop : t -> (elt * t) option
  val push_quasi_solved : t -> Variable.t -> Type.t -> t
  val push_array2 : Type.t array -> Type.t array -> t -> t

  val[@warning "-32"] pp : string Variable.HMap.t -> t Fmt.t

end = struct

  type elt =
    | Var of Variable.t * Type.t
    | Expr of Type.t * Type.t

  type t = elt list

  let empty : t = []

  let [@inline] pop = function
    | [] -> None
    | h :: t -> Some (h, t)

  (* TODO: introduce some priorities:
     subst first, then quasi solved, then expr. ===> Use a form of deque. *)

  let push l t1 t2 = Expr (t1, t2) :: l
  let push_quasi_solved l v t = Var (v, t) :: l
  let push_array2 a1 a2 stack =
    CCArray.fold2 push stack a1 a2

  let pp_elt namefmt fmt = function
    | Var (v, t) -> Fmt.pf fmt "%a = %a" (Variable.pp namefmt) v (Type.pp namefmt) t
    | Expr (t1, t2) -> Fmt.pf fmt "%a = %a" (Type.pp namefmt) t1 (Type.pp namefmt) t2

  let pp namefmt =
    Fmt.(vbox (list ~sep:cut @@ pp_elt namefmt))

end

(* The [F] unification problem. *)

exception FailUnif of Type.t * Type.t
let fail t1 t2 = raise (FailUnif (t1, t2))

(** Checking for cycles *)

exception FailedOccurCheck of Env.t

(* TO OPTIM/MEASURE *)
let occur_check env : unit =
  debug (fun m -> m "@[<v>Occur check in@,%a@]" Env.pp env);
  let nb_predecessors = Variable.HMap.create 17 in
  let successors = Variable.HMap.create 17 in

  let fill_nb_predecessors x ty =
    let aux y =
      Variable.HMap.incr nb_predecessors y ;
      Variable.HMap.add_list successors x y ;
    in
    begin
      if not @@ Variable.HMap.mem nb_predecessors x then
        Variable.HMap.add nb_predecessors x 0
    end;
    Type.vars ty |> Iter.iter aux
  in
  Variable.Map.iter fill_nb_predecessors (Env.vars env);

  let nb_representatives = Variable.HMap.length nb_predecessors in
  let vars_without_predecessors =
    Variable.HMap.fold
      (fun x count_preds l -> if count_preds = 0 then x :: l else l)
      nb_predecessors []
  in
  debug (fun m -> m "Predecessors: %a"
            (Variable.HMap.pp (Variable.pp @@ Env.var_names env) Fmt.int)
          nb_predecessors);
  debug (fun m -> m "Vars without predecessor: %a"
            (Fmt.Dump.list @@ Variable.pp @@ Env.var_names env)
          vars_without_predecessors);
  
  let rec loop n vars_without_predecessors = match vars_without_predecessors with
    (* We eliminated all the variables: there are no cycles *)
    | _ when n = nb_representatives -> ()
    | [] -> raise @@ FailedOccurCheck env
    | x :: q ->
      let aux l v =
        Variable.HMap.decr nb_predecessors v ;
        let n = Variable.HMap.get_or ~default:0 nb_predecessors v in
        if n = 0 then v :: l
        else l
      in
      let succs_x = Variable.HMap.get_or ~default:[] successors x in
      let q = List.fold_left aux q succs_x in
      loop (n+1) q
  in
  loop 0 vars_without_predecessors

(** Main process *)

(* Alternative unit type.
   Distinguish main loop from side-effecting functions.
*)
type done_ty = Done

let rec process_stack env (stack:Stack.t) : done_ty =
  match Stack.pop stack with
  | Some (Expr (t1, t2), stack) -> insert_rec env stack t1 t2
  | Some (Var (v, t), stack) -> insert_var env stack v t
  | None -> Done

and insert_rec env stack (t1 : Type.t) (t2 : Type.t) : done_ty =
  match t1, t2 with
  (* Decomposition rule
     (s₁,...,sₙ) p ≡ (t₁,...,tₙ) p  --> ∀i, sᵢ ≡ tᵢ
     when p is a type constructor.
  *)
  | Type.Constr (p1, args1), Type.Constr (p2, args2)
    when LongIdent.compare p1 p2 = 0 ->
    let stack = Stack.push_array2 args1 args2 stack in
    process_stack env stack

  (* Two arrows, we apply VA repeatedly
     (a₁,...,aₙ) -> r ≡ (a'₁,...,a'ₙ) -> r'  -->  an equivalent arrow problem
  *)
  | Type.Arrow (arg1, ret1), Type.Arrow (arg2, ret2)->
    let stack, arg1 = variable_abstraction_all env stack arg1 in
    let stack, arg2 = variable_abstraction_all env stack arg2 in
    (* let stack, ret1 = variable_abstraction env stack ret1 in
     * let stack, ret2 = variable_abstraction env stack ret2 in *)
    Env.push_arrow env
      (ArrowTerm.make arg1 ret1)
      (ArrowTerm.make arg2 ret2) ;
    process_stack env stack

  (* Two tuples, we apply VA repeatedly
     (s₁,...,sₙ) ≡ (t₁,...,tₙ) --> an equivalent pure problem
  *)
  | Tuple s, Tuple t ->
    let stack, pure_s = variable_abstraction_all env stack s in
    let stack, pure_t = variable_abstraction_all env stack t in
    Env.push_tuple env pure_s pure_t ;
    process_stack env stack

  | Var v, t | t, Var v ->
    insert_var env stack v t

  (* Clash rule
     Terms are incompatible
  *)
  | Constr _, Constr _  (* if same constructor, already checked above *)
  | (Constr _ | Tuple _ | Arrow _ | Other _),
    (Constr _ | Tuple _ | Arrow _ | Other _)
    ->
    fail t1 t2

(* Repeated application of VA on an array of subexpressions. *)
and variable_abstraction_all env stack a =
  let r = ref stack in
  let f x =
    let stack, x = variable_abstraction env !r x in
    r := stack ;
    x
  in
  !r, Array.map f @@ Type.MSet.as_array a

(* rule VA/Variable Abstraction
   Given a tuple, assign a variable to each subexpressions that is foreign
   and push them on stack.

   Returns the new state of the stack and the substituted expression.
*)
and variable_abstraction env stack t =
  match t with
  (* A nested tuple. We consider that a pure subproblem *)
  | Type.Tuple ts ->
    let stack, all_vars = variable_abstraction_all env stack ts in
    let var = Env.gen env in
    Env.push_tuple env [|Pure.var var|] all_vars;
    stack, Pure.var var
  (* Not a foreign subterm *)
  | Var i -> stack, Pure.var i
  | Constr (p, [||]) -> stack, Pure.constant p
  (* It's a foreign subterm *)
  | Arrow _ | Constr (_, _) | Other _ ->
    let var = Env.gen env in
    let stack = Stack.push_quasi_solved stack var t in
    stack, Pure.var var

and insert_var env stack x s =
  match s with
  | Type.Constr (_, [||])
  | Type.Tuple _ | Type.Constr _ | Type.Arrow _ | Type.Other _ ->
    quasi_solved env stack x s
  | Type.Var y ->
    non_proper env stack x y
  
(* Quasi solved equation
   'x = (s₁,...sₙ)
   'x = (s₁,...sₙ) p
*)
and quasi_solved env stack x s =
  (* Rule representative *)
  match Env.representative env x with
  | V x ->
    attach env x s ;
    process_stack env stack
  (* Rule AC-Merge *)
  | E (_, (Type.Tuple _ as t)) ->
    insert_rec env stack t s
  (* Rule Merge *)
  | E (_, t) ->
    if Measure.size NodeCount t < Measure.size NodeCount s then
      insert_rec env stack t s
    else
      insert_rec env stack s t

(* Non proper equations
   'x ≡ 'y
*)
and non_proper env stack (x:Variable.t) (y:Variable.t) =
  match Env.representative env x, Env.representative env y with
  | V x', V y' when Variable.equal x' y' ->
    process_stack env stack
  | V x', (E (y',_) | V y')
  | E (y',_), V x' ->
    attach env x' (Type.var y') ;
    process_stack env stack
  | E (x', s), E (y', t) ->
    if Measure.size NodeCount s < Measure.size NodeCount t then begin
      attach env y' (Type.var x');
      insert_rec env stack s t
    end
    else begin
      attach env x' (Type.var y');
      insert_rec env stack t s
    end

and attach env v t =
  Env.add env v t;
  occur_check env

let insert env t u : unit =
  let Done = insert_rec env Stack.empty t u in
  ()
let insert_var env x ty : unit =
  let Done = insert_var env Stack.empty x ty in
  ()

let insert_tuple_solution env (_, sol) =
  Variable.HMap.iter
    (fun k v -> insert_var env k (ACTerm.as_tuple v)) sol

(* Elementary AC theory *)
let rec solve_tuple_problems env0 =
  (* Call the AC solver on all tuple problems at once *)
  let rec pop_all_tuples acc env =
    match Env.pop_tuple env with
    | None -> acc
    | Some pb -> pop_all_tuples (pb::acc) env
  in
  AC.solve env0 @@ pop_all_tuples [] env0
  |> Iter.flat_map (try_with_solution env0 insert_tuple_solution)

(* Elementary Arrow theory *)
(* TODO : Solve this properly *)
and solve_arrow_problem env0 {ArrowTerm. left; right } k =
  let f env () =
    insert env left.ret right.ret;
    Env.push_tuple env left.args right.args;
  in
  try_with_solution env0 f () k

and try_with_solution
  : type a. _ -> (Env.t -> a -> unit) -> a -> _
  = fun env f sol k ->
  try
    let env = Env.copy env in
    f env sol;
    solve_loop env k
  with
  | FailUnif (t1, t2) ->
    debug (fun m ->
        m "@[<v>Conflict between:@;<1 2>@[%a@]@ and@;<1 2>@[%a@]@]@.@."
          (Type.pp @@ Env.var_names env) t1
          (Type.pp @@ Env.var_names env) t2
      )
  | FailedOccurCheck env -> 
    debug (fun m ->
        m "@[<v>Failed occur check in env@;%a"
          Env.pp env
      )

and solve_loop env k =
  match Env.is_solved env with
  | Some map ->
    debug (fun m -> m "@[<v2>Solved env:@,%a@]@." Env.pp env) ;
    k map
  | None ->
    debug (fun m -> m "@[<v2>New env:@,%a@]@." Env.pp env) ;
    begin 
      match Env.pop_arrow env with
      | Some pb ->
        solve_arrow_problem env pb k
      | None ->
        solve_tuple_problems env k
    end

let unifiers (tyenv : Type.Env.t) t1 t2 : Subst.t Iter.t =
  let env0 = Env.make tyenv in
  debug (fun m ->
      m {|@[<v>Unify:@ "%a"@ "%a"@]|}
        (Type.pp tyenv.var_names) t1
        (Type.pp tyenv.var_names) t2);
  try
    insert env0 t1 t2; 
    debug (fun m -> m "env0: @,%a" Env.pp env0) ;
    solve_loop env0
  with 
  | FailUnif _ 
  | FailedOccurCheck _
    -> Iter.empty

let unify (env : Type.Env.t) t1 t2 =
  Iter.min ~lt:Subst.lt @@ unifiers env t1 t2

let unifiable (env : Type.Env.t) t1 t2 =
  not @@ Iter.is_empty @@ unifiers env t1 t2
