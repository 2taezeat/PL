1.

type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of var * var * exp * var * var * exp * env
and env = (var * value) list

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ List.fold_left (fun s x -> s ^ ", " ^ x) "" (List.map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl



let rec eval : exp -> env -> value
=fun exp env ->
  match exp with
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | CONST n -> Int n
  | TRUE -> Bool true
  | FALSE -> Bool false
  | UNIT -> Unit
  | VAR x1 -> lookup_env x1 env
  | ADD (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | Int n1, Int n2 -> Int (n1+n2)
                        |_ -> raise UndefinedSemantics
                        )
  | SUB (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | Int n1, Int n2 -> Int (n1-n2)
                        |_ -> raise UndefinedSemantics
                        )
  | MUL (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | Int n1, Int n2 -> Int (n1*n2)
                        |_ -> raise UndefinedSemantics
                        ) 
  | DIV (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | Int n1, Int n2 -> Int (n1/n2)
                        |_ -> raise UndefinedSemantics
                        )
  | EQUAL (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | Int n1, Int n2 -> if n1 = n2 then Bool true else Bool false
                        | Bool b1, Bool b2 -> if b1 = b2 then Bool true else Bool false
                        |_ -> raise UndefinedSemantics
                        )
  | LESS (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | Int n1, Int n2 -> if n1 < n2 then Bool true else Bool false
                        |_ -> raise UndefinedSemantics
                        )
  | NOT exp1 -> let value1 = eval exp1 env in
                ( match value1 with
                  | Bool b1 -> if b1 = true then Bool false else Bool true
                  |_ -> raise UndefinedSemantics
                )
  | NIL -> List []
  
  | CONS (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match value2 with
                        | List l1 -> List ( value1 :: l1 )
                        |_ -> raise UndefinedSemantics
                        )
  | APPEND (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match (value1, value2) with
                        | List l1, List l2 -> List ( l1 @ l2 )
                        |_ -> raise UndefinedSemantics
                        )
  | HEAD exp1 -> let value1 = eval exp1 env in
                ( match value1 with
                  | List l1 -> ( match l1 with
                                | h::t -> h 
                                |_ -> raise UndefinedSemantics )
                  |_ -> raise UndefinedSemantics
                )
  | TAIL exp1 -> let value1 = eval exp1 env in
                ( match value1 with
                  | List l1 -> ( match l1 with
                                | h::t -> List t 
                                |_ -> raise UndefinedSemantics )
                  |_ -> raise UndefinedSemantics
                )
  | ISNIL exp1 -> let value1 = eval exp1 env in if value1 = List [] then Bool true else Bool false
                

  | IF (exp1, exp2, exp3) -> let value1 = eval exp1 env in 
                        ( match value1 with
                        | Bool b1 -> if b1 = true then eval exp2 env else eval exp3 env
                        |_ -> raise UndefinedSemantics
                        )
 | LET (x1, exp1, exp2) -> let value1 = eval exp1 env in let et_env = extend_env (x1, value1) env in eval exp2 et_env
 
 | LETREC (f1, x1, exp1, exp2) -> let et_env = extend_env (f1, RecProcedure (f1, x1, exp1, env)) env in eval exp2 et_env
 
 | LETMREC ( (f1, x1, exp1), (g1, x2, exp2), exp3 ) -> let et_env1 = extend_env ( f1, MRecProcedure (f1, x1, exp1, g1, x2, exp2, env)) env in 
                                                                let et_env2  = extend_env ( g1, MRecProcedure (g1, x2, exp2, f1, x1, exp1, env)) et_env1 in 
                                                                      eval exp3 et_env2 
 | PROC (x1, exp1) -> Procedure (x1, exp1, env)
 
 | CALL (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in
                        ( match value1 with
                        | Procedure (x1, exp3, et_env) -> let et_env2 = extend_env (x1, value2) et_env in eval exp3 et_env2
                        | RecProcedure (f1, x1, exp3, et_env) -> let et_env2 = extend_env (x1, value2) et_env in
                                                                      let et_env3 = extend_env ( f1, RecProcedure (f1, x1, exp3, et_env) ) et_env2 in eval exp3 et_env3
                                                                      
                        | MRecProcedure (f1, x1, exp3, g1, x2, exp4, et_env) -> let et_env2 = extend_env (x1, value2) et_env in
                                                                                    let et_env3 = extend_env (f1, MRecProcedure (f1, x1, exp3, g1, x2, exp4, et_env)) et_env2 in
                                                                                        let et_env4 = extend_env (g1, MRecProcedure (g1, x2, exp4, f1, x1, exp3, et_env)) et_env3 in eval exp3 et_env4
                        |_ -> raise UndefinedSemantics
                        )
 | SEQ (exp1, exp2) -> let value1 = eval exp1 env in let value2 = eval exp2 env in value2


 let runml : program -> value
=fun pgm -> eval pgm empty_env
;;
