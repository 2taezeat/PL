1. B

type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(************************************)
(*      List utility functions      *)
(************************************)
let rec list_length : 'a list -> int
= fun lst ->
  match lst with
  | [] -> 0
  | hd::tl -> 1 + list_length tl

let rec list_exists : ('a -> bool) -> 'a list -> bool
= fun pred lst ->
  match lst with 
  | [] -> false 
  | hd::tl -> if (pred hd) then true else list_exists pred tl

let rec list_fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
= fun func acc lst1 lst2 ->
  match (lst1, lst2) with
  | ([], []) -> acc
  | (hd1::tl1, hd2::tl2) -> list_fold2 func (func acc hd1 hd2) tl1 tl2
  | _ -> raise (Failure "list_fold2 : two lists have different length")

let rec list_fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun func acc lst ->
  match lst with
  | [] -> acc
  | hd::tl -> list_fold func (func acc hd) tl 

(********************************)
(*     Handling environment     *)
(********************************)
let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id, l) -> if (x = id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id, binding) -> if (x = id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []

(***************************)
(*     Handling memory     *)
(***************************)
let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise (Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc, v)::tl -> if (l = loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l, v) mem -> (l, v)::mem

let empty_mem = []

let size_of_mem mem = 
  let add_if_new x l = if list_exists (fun y -> x = y) l then l else x::l in
  let dom = list_fold (fun dom loc -> add_if_new loc dom) [] mem  in
    list_length dom

(***************************)
(*     Handling record     *)
(***************************)
let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
  | [] -> raise(Failure ("field "^ id ^" is not included in record"))
  | (x, l)::tl -> if (id = x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x, l) record -> (x, l)::record

let empty_record = []

(******************)
(* Pretty printer *)
(******************)
let rec value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record r -> "{" ^ record2str r ^ "}" 

and record2str : record -> string
= fun record ->
  match record with
  | [] -> ""
  | [(x, l)] -> x ^ "->" ^ string_of_int l
  | (x, l)::tl-> x ^ "->" ^ string_of_int l ^ ", " ^ record2str tl

let mem2str : memory -> string
= fun mem -> 
  let rec aux mem =
    match mem with
    | [] -> ""
    | [(l, v)] -> string_of_int l ^ "->" ^ value2str v
    | (l, v)::tl -> string_of_int l ^ "->" ^ value2str v ^ ", " ^ aux tl
  in
  "[" ^ aux mem ^ "]"

let rec env2str : env -> string
= fun env -> 
  let rec aux env =
    match env with
    | [] -> ""
    | [binding] -> binding2str binding
    | binding::tl -> binding2str binding ^ ", " ^ aux tl
  in
  "[" ^ aux env ^ "]"

and binding2str : binding -> string
= fun binding ->
  match binding with
  | LocBind (x, l) -> x ^ "->" ^ string_of_int l
  | ProcBind (x, proc) -> x ^ "->" ^ "(" ^ proc2str proc ^ ")"

and proc2str : proc -> string
= fun (xs, e, env) ->  
  let rec args2str xs =
    match xs with
    | [] -> ""
    | [x] -> x
    | x::tl -> x ^ ", " ^ args2str tl
  in
  "(" ^ args2str xs ^ ")" ^ ", E" ^ ", " ^ env2str env

(***************************)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1, mem1) = eval env mem e1 in
  let (v2, mem2) = eval env mem1 e2 in
  match (v1, v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
   let mem = gc env mem in 
  match e with
  | WRITE e -> 
    let (v1, mem1) = eval env mem e in
    let _ = print_endline (value2str v1) in
    (v1, mem1)
  | NUM n -> ( Num n, mem )
  | TRUE -> ( Bool true, mem)
  | FALSE -> ( Bool false, mem )
  | UNIT -> ( Unit, mem )
  | VAR x1 -> let loc1 = lookup_loc_env x1 env in let value1 = lookup_mem loc1 mem in ( value1, mem )
  | ADD (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in 
                        ( match ( value1, value2 ) with
                          | Num n1, Num n2 -> ( Num( n1 + n2 ), mem2 )
                          |_ -> raise UndefinedSemantics
                        )
  | SUB (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in 
                        ( match ( value1, value2 ) with
                          | Num n1, Num n2 -> ( Num( n1 - n2 ), mem2 )
                          |_ -> raise UndefinedSemantics
                        )                        
  | MUL (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in 
                        ( match ( value1, value2 ) with
                          | Num n1, Num n2 -> ( Num( n1 * n2 ), mem2 )
                          |_ -> raise UndefinedSemantics
                        )
  | DIV (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in 
                        ( match ( value1, value2 ) with
                          | Num n1, Num n2 -> ( Num( n1 / n2 ), mem2 )
                          |_ -> raise UndefinedSemantics
                        )
  | EQUAL (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in 
                        ( match ( value1, value2 ) with
                          | Num n1, Num n2 -> if n1 = n2 then ( Bool true, mem2 ) else ( Bool false, mem2 )
                          | Bool b1, Bool b2 -> if b1 = b2 then ( Bool true, mem2 ) else ( Bool false, mem2 )
                          | Unit, Unit -> ( Bool true, mem2 )
                          | Unit, _ -> ( Bool false, mem2 )
                          | _, Unit -> ( Bool false, mem2 )
                          |_ -> raise UndefinedSemantics
                        )  
  | LESS (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in 
                        ( match ( value1, value2 ) with
                          | Num n1, Num n2 -> if n1 < n2 then ( Bool true, mem2 ) else ( Bool false, mem2 )
                          |_ -> raise UndefinedSemantics
                        )
  | SEQ (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let ( value2, mem2 ) = eval env mem1 exp2 in ( value2, mem2 )
                                               
  | NOT exp1 -> let ( value1, mem1 ) = eval env mem exp1 in
                        ( match value1 with
                          | Bool b1 -> if b1 = true then ( Bool false, mem1 ) else ( Bool true, mem1 )
                          |_ -> raise UndefinedSemantics
                        )
  | IF (exp1, exp2, exp3) -> let ( value1, mem1 ) = eval env mem exp1 in
                        ( match value1 with
                          | Bool b1 -> if b1 = true then eval env mem1 exp2 else eval env mem1 exp3 
                          |_ -> raise UndefinedSemantics
                        )
  | WHILE (exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in
                        ( match value1 with
                          | Bool b1 -> if b1 = true then let ( value2, mem2 ) = eval env mem1 exp2 in let ( value3, mem3 ) = eval env mem2 e in ( value3, mem3 ) else ( Unit, mem1 )
                          |_ -> raise UndefinedSemantics
                        ) 
  | RECORD idexplist1 -> if ( idexplist1 = [] ) then ( Unit, mem ) else
                            let valuememlist1 = f_1 (idexplist1) env mem in
                            let recordlist1 =  f_2 idexplist1 in
                            let memorylist1 = f_3 (valuememlist1, recordlist1) in ( Record recordlist1, memorylist1 )
                            
  | ASSIGN (x1, exp1) -> let ( value1, mem1 ) = eval env mem exp1 in let loc1 = lookup_loc_env x1 env in let et_mem1 = extend_mem (loc1, value1) mem1 in (value1, et_mem1)
  
  | ASSIGNF (exp1, x1, exp2) -> let ( record1, mem1 ) = eval env mem exp1 in let ( value1, mem2 ) = eval env mem1 exp2 in
                        ( match record1 with
                          | Record r1 -> let loc1 = lookup_record x1 r1 in let et_mem1 = extend_mem (loc1, value1) mem2 in (value1, et_mem1)
                          |_ -> raise UndefinedSemantics
                        )
  | FIELD (exp1, x1) -> let ( record1, mem1 ) = eval env mem exp1 in 
                        ( match record1 with
                          | Record r1 -> let loc1 = lookup_record x1 r1 in let value1 = lookup_mem loc1 mem1 in (value1, mem1)
                          |_ -> raise UndefinedSemantics
                        )
  | LETV (x1, exp1, exp2) -> let ( value1, mem1 ) = eval env mem exp1 in let new_loc1 = new_location () in 
                                              let et_env1 = extend_env (LocBind (x1, new_loc1)) env in let et_mem1 = extend_mem (new_loc1, value1) mem1 in eval et_env1 et_mem1 exp2
                                              
  | LETF (f1, idlist1, exp1, exp2) -> let proc1 = (idlist1, exp1, env) in let binding1 = ProcBind (f1, proc1) in let et_env1 = extend_env binding1 env in
                                                                let ( value1, mem1 ) = eval et_env1 mem exp2 in (value1, mem1)    
                                                                
  | CALLV (f1, explist1) -> let ( xilist, e1, env1 ) = lookup_proc_env f1 env in let valuememlist1 = f_1_b (explist1) env mem in
                                                              let bindlist1 = f_2_b xilist in
                                                                let et_env1 = list_fold ( fun env0 b0 -> extend_env b0 env0 ) env1 bindlist1 in
                                                                  let binding1 = ProcBind ( f1, (xilist, e1, env1) ) in
                                                                    let et_env2 = extend_env binding1 et_env1 in 
                                                                      let mem_n = f_6 ( reverse valuememlist1 ) in
                                                                        let memorylist1 = f_3_b (valuememlist1, bindlist1) in
                                                                          let et_mem1 = list_fold ( fun mem0 (loc0, value0) -> extend_mem (loc0, value0) mem0 ) mem_n memorylist1 in
                                                                            let ( value1, mem1 ) = eval et_env2 et_mem1 e1 in ( value1, mem1 )
  
  | CALLR (f1, idlist1) -> let ( xilist, e1, env1 ) = lookup_proc_env f1 env in let bindlist1 = f_4 ( xilist, idlist1 ) env in 
                                                        let et_env1 = list_fold ( fun env0 b0 -> extend_env b0 env0 ) env1 bindlist1 in
                                                           let binding1 = ProcBind ( f1, (xilist, e1, env1) ) in
                                                                let et_env2 = extend_env binding1 et_env1 in 
                                                                  let ( value1, mem1 ) = eval et_env2 mem e1 in ( value1, mem1 )

and f_1 (list1) env mem= 
  match list1 with 
    | hd::tl -> ( match hd with
                | (x1, exp1) -> let (valuei, memi) = eval env mem exp1 in [ (valuei, memi) ] @ f_1 tl env memi
                )
    | [] -> []
    
and f_1_b (list1) env mem= 
  match list1 with 
    | hd::tl -> ( match hd with
                | exp1 -> let (valuei, memi) = eval env mem exp1 in [ (valuei, memi) ] @ f_1_b tl env memi
                )
    | [] -> [] 
    
and f_2 (list2) = 
  match list2 with 
    | hd::tl -> ( match hd with
                | (x1, exp1) -> let new_loc1 = new_location() in [( x1, new_loc1 )] @ f_2 (tl)
                )
    | [] -> []
    
and f_2_b (list2) = 
  match list2 with 
    | hd::tl -> ( match hd with
                | xi -> let new_loci = new_location() in let locBind0 = LocBind ( xi, new_loci ) in [ locBind0 ] @ f_2_b (tl)
                )
    | [] -> []
    
and f_3 (listv, listr) = 
  ( match listv with 
    | hv::tv -> ( match hv with
                | (valuei, memi) -> let vi = valuei in 
                                          ( match listr with
                                          | hr::tr -> ( match hr with
                                                        | (xi, locationi) -> let li = locationi in extend_mem ( li, vi ) memi @ ( f_3 ( tv, tr ) )
                                                      )
                                          | [] -> []
                                          )
                )
    | [] -> [] 
  )
and f_3_b (listv, locbindlist) = 
  ( match listv with 
    | hv::tv -> ( match hv with
                | (valuei, memi) -> let vi = valuei in 
                                          ( match locbindlist with
                                          | hb::tb -> ( match hb with
                                                        | LocBind ( xi, locationi ) -> let li = locationi in let memoryi = (li, vi) in [memoryi] @ f_3_b (tv, tb)
                                                        |_ -> raise UndefinedSemantics
                                                      )
                                          | [] -> []
                                          )
                )
    | [] -> [] 
  )
and f_4 (xilist, idlist1) enva = 
  ( match xilist with 
    | hx::tx -> ( match hx with
                | hx -> let xi = hx in ( match idlist1 with 
                                        | hi::ti -> let loci = lookup_loc_env hi enva in let locBind0 = LocBind (xi, loci) in [ locBind0 ] @ f_4 (tx, ti) enva
                                        | [] -> []
                                       )
                )
    | [] -> [] 
  )
and f_6 (list6) = 
  match list6 with 
    | hd::tl -> ( match hd with
                | (valuei, memi) -> let mn = memi in mn
                )
    | [] -> []
    
and reverse l =
match l with
| [] -> []
| hd::tl -> (reverse tl) @ [hd]

and g_1 env =
match env with
| he::te -> ( match he with 
                  | LocBind (xi, li) -> [li] @ g_1 te
                  | ProcBind ( f1, ( xlist1, exp1, env1 ) ) -> g_1 env1 @ g_1 te
            )
| [] -> []

and g_2 r1 = 
( match r1 with
| hr::tr -> ( match hr with 
                  | (xr, lr) -> [lr] @ g_2 tr
            )
| [] -> []
) 
and uniqhelper l m=
  match l with
    | [] -> []
    | h::t -> if h = m then (uniqhelper t m) else h::(uniqhelper t m)
    
and uniq : 'a list -> 'a list
= fun lst -> 
  match lst with
    | [] -> []
    | h::t -> h :: uniq (uniqhelper lst h)

and ismember lst a=
  match lst with
    | h::t -> if h = a then true else ismember t a 
    | [] -> false

and reach (env9, mem9, loc9)
= ( match mem9 with 
    | hm::tm ->  ( match hm with 
                  | (li, Num n) -> let check1 = (ismember loc9 li) in if check1 = true then let u = loc9 @ reach (env9, tm, loc9) in uniq u else reach (env9, tm, loc9)
                  | (li, Bool b) -> let check1 = (ismember loc9 li) in if check1 = true then let u = loc9 @ reach (env9, tm, loc9) in uniq u else reach (env9, tm, loc9)
                  | (li, Unit)  ->  let check1 = (ismember loc9 li) in if check1 = true then let u = loc9 @ reach (env9, tm, loc9) in uniq u else reach (env9, tm, loc9)
                  | (li, Record r1) -> let check1 = (ismember loc9 li) in if check1 = true then let rinl = g_2 r1 in let new1 = loc9 @ rinl in let u = uniq new1 in reach (env9, tm, u) 
                                        else reach (env9, tm, loc9)
                 ) 
    | [] -> []
  )
and ismember2 memlist1 loci =
 (  match memlist1 with
        | hm::tm -> ( match hm with
                      | (li, _ ) -> if (loci = li) then [hm] else (ismember2 tm loci)
                  )  
        | [] -> []
 )
and checkmemlistinrloclist loclist mem =
 match loclist with
   | ( hloc::tloc ) -> ismember2 mem hloc @ checkmemlistinrloclist tloc mem
   | [] -> []
   
and gc : env -> memory -> memory
= fun env mem -> 
let floclist = g_1 env in
let reachableloclist = reach (env, mem, floclist) in let resultmemorylist = checkmemlistinrloclist reachableloclist mem in resultmemorylist
;;

let runb : exp -> value 
= fun exp ->
  let (v, m) = eval empty_env empty_mem exp in
  let _ = print_endline ("memory size: " ^ string_of_int (size_of_mem m)) in
    v;;






