1. type

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

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty ->
  match e with
    | CONST n -> [(ty, TyInt)]
    | VAR x -> [(TEnv.find tenv x, ty)]
    | ADD (exp1 ,exp2) -> [ (ty, TyInt) ] @ gen_equations tenv exp1 TyInt @ gen_equations tenv exp2 TyInt
    | DIV (exp1 ,exp2) -> [ (ty, TyInt) ] @ gen_equations tenv exp1 TyInt @ gen_equations tenv exp2 TyInt
    | SUB (exp1 ,exp2) -> [ (ty, TyInt) ] @ gen_equations tenv exp1 TyInt @ gen_equations tenv exp2 TyInt
    | MUL (exp1 ,exp2) -> [ (ty, TyInt) ] @ gen_equations tenv exp1 TyInt @ gen_equations tenv exp2 TyInt
    | ISZERO exp1 -> [ (ty, TyBool) ] @ gen_equations tenv exp1 TyInt
    | IF (exp1, exp2, exp3) -> gen_equations tenv exp1 TyBool @ gen_equations tenv exp2 ty @ gen_equations tenv exp3 ty
    | LET (var1, exp1, exp2) -> let newtype1 = fresh_tyvar () in gen_equations tenv exp1 newtype1 @ gen_equations ( TEnv.extend (var1, newtype1) tenv ) exp2 ty
    | PROC (var1, exp1) -> let newtype1 = fresh_tyvar () in let newtype2 = fresh_tyvar () in [ ( ty, TyFun(newtype1, newtype2) ) ] @ gen_equations ( TEnv.extend (var1, newtype1) tenv ) exp1 newtype2
    | CALL (exp1, exp2) -> let newtype1 = fresh_tyvar () in gen_equations tenv exp1 ( TyFun (newtype1, ty) ) @ gen_equations tenv exp2 newtype1
    | READ -> [(ty, TyInt)]
    | LETREC (f1, x1, exp1, exp2) -> let newtype1 = fresh_tyvar () in let newtype2 = fresh_tyvar () in  
                                                      let newtype3 = TyFun (newtype2, newtype1) in
                                                      let et_env1 = TEnv.extend (f1, newtype3) tenv in
                                                      let et_env2 = TEnv.extend (x1, newtype2) et_env1 in
                                                          gen_equations et_env2 exp1 newtype1 @ gen_equations et_env1 exp2 ty
;;

let rec occurcheck tyvar_x1 typ0 =
  match typ0 with
    | TyVar b1 -> if tyvar_x1 = (TyVar b1) then true else false
    | TyFun (t1, t2) -> ( occurcheck tyvar_x1 t1 ) || ( occurcheck tyvar_x1 t2 ) 
    | TyInt -> false
    | TyBool -> false
;;

let rec unify type1 type2 subst0
= match (type1, type2) with
  | ( TyInt, TyInt ) -> subst0
  | ( TyBool, TyBool ) -> subst0
  | ( TyVar x1, TyVar x2 ) -> if ( TyVar x1 = TyVar x2 ) then subst0 else let extend_subst = Subst.extend x1 (TyVar x2) subst0 in extend_subst
  | ( TyVar x1, type0 ) -> if ( occurcheck (TyVar x1) type0 = true ) then raise TypeError else let extend_subst = Subst.extend x1 type0 subst0 in extend_subst
  | ( type0, TyVar x1 ) -> unify (TyVar x1) type0 subst0
  | ( TyFun (t1, t2), TyFun (t3, t4) ) -> let subst1 = unify t1 t3 subst0 in let subst2 = unify (Subst.apply t2 subst1) (Subst.apply t4 subst1) subst1 in subst2
  |_ -> raise TypeError
;; 

let rec unifyall type_equation0 subst0 
= match type_equation0 with
  | [] -> subst0
  | ( (type1, type2) :: (type_equation1) ) -> let subst1 = unify (Subst.apply type1 subst0) (Subst.apply type2 subst0) subst0 in unifyall type_equation1 subst1
;;

let solve : typ_eqn -> Subst.t
=fun eqns -> unifyall eqns []
;;

let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
      print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1);;


------------------------------------------------------------------------------------
2. expand

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

let rec expand : exp -> exp 
=fun e -> 
  ( match e with
    | LET (var1, exp1, exp2) -> ( match exp2 with
                                  | VAR x1 -> let newep1 = trans (VAR x1) exp1 var1 in newep1
                                  | IF (ep1, ep2, ep3) -> let newep1 = trans ep1 exp1 var1 in let newep2 = trans ep2 exp1 var1 in let newep3 = trans ep3 exp1 var1 in
                                                                                    IF (newep1, newep2, newep3)
                                  | ADD (ep1, ep2) -> let newep1 = trans ep1 exp1 var1 in let newep2 = trans ep2 exp1 var1 in
                                                                                    ADD (newep1, newep2)
                                  | SUB (ep1, ep2) -> let newep1 = trans ep1 exp1 var1 in let newep2 = trans ep2 exp1 var1 in
                                                                                    SUB (newep1, newep2)
                                  | DIV (ep1, ep2) -> let newep1 = trans ep1 exp1 var1 in let newep2 = trans ep2 exp1 var1 in
                                                                                    DIV (newep1, newep2)
                                  | MUL (ep1, ep2) -> let newep1 = trans ep1 exp1 var1 in let newep2 = trans ep2 exp1 var1 in
                                                                                    MUL (newep1, newep2)
                                  | CONST n1 -> e
                                  | LET (f1, ep1, ep2) -> let n_exp = (trans ep2 ep1 f1) in let new_expression = LET (var1, exp1, n_exp) in expand new_expression
                                  | LETREC (f1, x1, ep1, ep2) -> e    
                                  | CALL (ep1, ep2) -> let newep1 = trans ep1 exp1 var1 in let newep2 = trans ep2 exp1 var1 in CALL (newep1, newep2)
                                  | PROC (x1, ep1) -> let newep1 = trans ep1 exp1 var1 in PROC (x1, newep1)
                                  | ISZERO ep1 -> let newep1 = trans ep1 exp1 var1 in ISZERO newep1
                                  | READ -> e
                                )
  | ADD (exp1, exp2) -> ADD (expand exp1, expand exp2)
  | SUB (exp1, exp2) -> SUB (expand exp1, expand exp2)
  | MUL (exp1, exp2) -> MUL (expand exp1, expand exp2)
  | DIV (exp1, exp2) -> DIV (expand exp1, expand exp2)
  | ISZERO (exp1) -> ISZERO (expand exp1)
  | CONST n1 -> e
  | READ -> e
  | VAR x1 -> e
  | LETREC (f1, x1, exp1, exp2) -> e
  | IF (exp1, exp2, exp3) -> IF (expand exp1, expand exp2, expand exp3)
  | PROC (f1, exp1) -> PROC (f1, expand exp1)
  | CALL (exp1, exp2) -> CALL (expand exp1, expand exp2)
  )
  
and trans exp0 body var0=
 ( match exp0 with
    | VAR x1 -> if (x1 = var0) then body else exp0   
    | CALL (exp1, exp2) -> CALL ( trans exp1 body var0, trans exp2 body var0 ) 
    | CONST n1 -> CONST n1
    | ADD (exp1, exp2) -> ADD ( trans exp1 body var0, trans exp2 body var0 )
    | SUB (exp1, exp2) -> SUB ( trans exp1 body var0, trans exp2 body var0 )    
    | MUL (exp1, exp2) -> MUL ( trans exp1 body var0, trans exp2 body var0 )    
    | DIV (exp1, exp2) -> DIV ( trans exp1 body var0, trans exp2 body var0 )
    | LETREC (f1, x1, exp1, exp2) -> exp0
    | ISZERO exp1 -> ISZERO (trans exp1 body var0 )
    | READ -> exp0
    | IF (exp1, exp2, exp3) -> IF ( trans exp1 body var0, trans exp2 body var0, trans exp3 body var0 ) 
    | PROC (f1, exp1) -> PROC ( f1, trans exp1 body var0 ) 
    | LET (x1, exp1, exp2) -> let newletexp = LET ( var0, body, (trans exp2 exp1 x1) ) in expand newletexp
)
;;

