type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

let rec exp2str : exp -> string
= fun e ->
  match e with
  | CONST n -> string_of_int n
  | VAR x -> x
  | ADD (e1, e2) -> exp2str e1 ^ " + " ^ exp2str e2
  | SUB (e1, e2) -> exp2str e1 ^ " - " ^ exp2str e2
  | MUL (e1, e2) -> exp2str e1 ^ " * " ^ exp2str e2
  | DIV (e1, e2) -> exp2str e1 ^ " / " ^ exp2str e2
  | ISZERO e -> "iszero " ^ exp2str e
  | READ -> "read"
  | IF (e1, e2, e3) -> "if " ^ exp2str e1 ^ " then " ^ exp2str e2 ^ " else " ^ exp2str e3
  | LET (x, e1, e2) -> "let " ^ x ^ " = " ^ exp2str e1 ^ " in " ^ exp2str e2
  | LETREC (f, x, e1, e2) -> "let rec " ^ f ^ "(" ^ x ^ ")" ^ " = " ^ exp2str e1 ^ " in " ^ exp2str e2
  | PROC (x, e) -> "proc (" ^ x ^ ") = " ^ exp2str e
  | CALL (e1, e2) -> "(" ^ exp2str e1 ^ " " ^ exp2str e2 ^ ")"

(* Environment for storing information *)
type env = (var * exp) list

let rec mem : var -> env -> bool
= fun x env ->
  match env with
  | [] -> false
  | (y, e)::tl -> if (y = x) then true else mem x tl

let rec find_env : env -> var -> exp
= fun env x ->
  match env with
  | [] -> raise (Failure ("Not Found : " ^ x))
  | (y, e)::tl -> if (y = x) then e else find_env tl x

let rec extend_env : (var * exp) -> env -> env
= fun (x, exp) env -> (x, exp)::env

let rec remove_env : env -> var -> env
= fun env x ->
  match env with
  | [] -> []
  | (y, e)::tl -> if (y=x) then remove_env tl x else (y,e)::(remove_env tl x)

(* Check a varaible is included in an expression *)
let rec is_used : var -> exp -> bool
= fun x exp ->
  match exp with
  | CONST n -> false
  | VAR x' -> x = x' 
  | ADD (e1, e2) -> (is_used x e1) || (is_used x e2) 
  | SUB (e1, e2) -> (is_used x e1) || (is_used x e2) 
  | MUL (e1, e2) -> (is_used x e1) || (is_used x e2) 
  | DIV (e1, e2) -> (is_used x e1) || (is_used x e2) 
  | ISZERO e -> is_used x e
  | READ -> false
  | IF (e1, e2, e3) -> (is_used x e1) || (is_used x e2) || (is_used x e3)
  | LET (x', e1, e2) -> if x = x' then (is_used x e1) else (is_used x e1) || (is_used x e2) 
  | LETREC (f, x', e1, e2) -> 
    if (x <> x' && x <> f) then (is_used x e1) || (is_used x e2) 
    else if (x <> f) then is_used x e2
    else false
  | PROC (x', e) -> if (x <> x') then is_used x e else false
  | CALL (e1, e2) -> (is_used x e1) || (is_used x e2) 

let rec trans_exp : exp -> env -> exp
= fun exp env ->
  match exp with
  | CONST n -> CONST n
  | VAR x -> if (mem x env) then find_env env x else VAR x
  | ADD (e1, e2) -> ADD (trans_exp e1 env, trans_exp e2 env)
  | SUB (e1, e2) -> SUB (trans_exp e1 env, trans_exp e2 env)
  | MUL (e1, e2) -> MUL (trans_exp e1 env, trans_exp e2 env)
  | DIV (e1, e2) -> DIV (trans_exp e1 env, trans_exp e2 env)
  | ISZERO e -> ISZERO (trans_exp e env)
  | READ -> READ
  | IF (e1, e2, e3) -> IF (trans_exp e1 env, trans_exp e2 env, trans_exp e3 env)
  | LET (x, e1, e2) ->  
    let e1' = trans_exp e1 env in
    let e2' = trans_exp e2 env in
    if (is_used x e2') then trans_exp e2' (extend_env (x, e1') env) else LET (x, e1', e2')
  | LETREC (f, x, e1, e2) -> 
    let e1' = trans_exp e1 (remove_env (remove_env env f) x) in
    LETREC (f, x, e1', trans_exp e2 (remove_env env f))
  | PROC (x, e) -> PROC (x, trans_exp e (remove_env env x))
  | CALL (e1, e2) -> CALL (trans_exp e1 env, trans_exp e2 env)

let expand : exp -> exp 
=fun e -> trans_exp e []