1.
let rec f1 n i =
  if i*i > n then n else if (n mod i = 0) then i else f1 n (i+1);;
  
let smallest_divisor : int -> int
= fun n -> f1 n 2;;

--------------------------------------------------------------------------------
2.
let rec sigma : (int -> int) -> int -> int -> int
= fun f a b -> 
  if a < b then f a + sigma f (a+1) b  else f b
;;

--------------------------------------------------------------------------------
3.
let rec forall : ('a -> bool) -> 'a list -> bool
= fun f lst -> 
  match lst with
    | [] -> true
    | h::t -> if f h then forall f t else false
;;

--------------------------------------------------------------------------------
4.
let rec f1 l m=
  match l with
    | [] -> []
    | h::t -> if h = m then (f1 t m) else h::(f1 t m)
;;


let rec app : 'a list -> 'a list -> 'a list
= fun l1 l2 -> 
  match l2 with
    | [] -> l1
    | h2::t2 -> h2::(app (f1 l1 h2) t2) 
;;

--------------------------------------------------------------------------------
5.
let rec f1 l m=
  match l with
    | [] -> []
    | h::t -> if h = m then (f1 t m) else h::(f1 t m)
;;


let rec uniq : 'a list -> 'a list
= fun lst -> 
  match lst with
    | [] -> []
    | h::t -> h :: uniq (f1 lst h)
;;

--------------------------------------------------------------------------------
6.
exception Exceptional_Situation;;

let rec reduce : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
= fun f xs ys c -> match xs,ys with
          | [],[] -> c
          | [], hy::ty -> raise Exceptional_Situation
          | hx::tx, [] -> raise Exceptional_Situation
          | hx::tx, hy::ty -> reduce f tx ty (f hx hy c)
;;

--------------------------------------------------------------------------------
7.
type graph = (vertex * vertex) list
and vertex = int

let rec f1 (g,v)=
  match g with
    | []->[v]
    | h::t -> match h with
                  | (h1,h2) -> if h1 = v then [h2] @ f1 (t,v) else f1 (t,v)
;;

let rec f2 l m=
  match l with
    | [] -> []
    | h::t -> if h = m then (f2 t m) else h::(f2 t m)
;;

let rec uniq : 'a list -> 'a list
= fun lst -> 
  match lst with
    | [] -> []
    | h::t -> h :: uniq (f2 lst h)
;;

let rec reach : graph * vertex -> vertex list
= fun (g, v) -> let x = f1 (g,v) in uniq (f3 g x)

and f3 g l =
  match l with
  | []->[]
  | h::t -> f1 (g,h) @ f3 g t                       
;;
--------------------------------------------------------------------------------
8.
type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let rec diff : aexp * string -> aexp
= fun (exp, x) -> 
  match exp with
    | Const n -> Const 0
    | Var a -> if x = a then Const 1 else Const 0
    | Power (a,n) -> if x = a then Times [ Power (x,n-1) ; Const n ] else Const 0
    | Times aexplist -> ( match aexplist with
              | [] -> Const 0
              | h::t -> Sum [ Times (diff(h,x)::t) ; Times [ h ; diff (Times (t),x) ] ] )
    | Sum aexplist -> match aexplist with
              | [] -> Const 0
              | h::t -> Sum [ (diff (h,x)) ; (diff (Sum t,x)) ]
;;
--------------------------------------------------------------------------------
9.
type mobile = branch * branch (* left and rigth branches *)
and branch = SimpleBranch of length * weight
		   | CompoundBranch of length * mobile
and length = int
and weight = int

let rec f1 moblie = 
  match moblie with
  | ( SimpleBranch(l1,w1) ,  CompoundBranch(l2,moblie2) ) -> w1 + f1 moblie2
  | ( SimpleBranch(l1,w1) ,  SimpleBranch(l2,w2) ) -> w1 + w2
  | ( CompoundBranch(l1,moblie1), CompoundBranch(l2,moblie2) ) -> f1 moblie1 + f1 moblie2
  | ( CompoundBranch(l1,moblie1), SimpleBranch(l2,w2) ) -> f1 moblie1 + w2
;;

let rec balanced : mobile -> bool
= fun m -> match m with
  | ( SimpleBranch(l1,w1) ,  CompoundBranch(l2,moblie2) ) -> if (l1 * w1) = (l2 * f1 moblie2) then (true && balanced moblie2) else false
  | ( SimpleBranch(l1,w1) ,  SimpleBranch(l2,w2) ) -> if (l1 * w1) = (l2 * w2) then true else false
  | ( CompoundBranch(l1,moblie1), CompoundBranch(l2,moblie2) ) -> if (l1 * f1 moblie1) = (l2 * f1 moblie2) then (true && balanced moblie2 && balanced moblie1) else false
  | ( CompoundBranch(l1,moblie1), SimpleBranch(l2,w2) ) -> if (l1 * f1 moblie1) = (l2 * w2) then (true && balanced moblie1) else false
;;
--------------------------------------------------------------------------------
10.
type exp = X
		 | INT of int
		 | ADD of exp * exp
		 | SUB of exp * exp
		 | MUL of exp * exp
		 | DIV of exp * exp
		 | SIGMA of exp * exp * exp

exception Exceptional_Situation;;

let rec calcul_X exp va
= match exp with
  | INT n -> n
  | ADD (e1,e2) -> calcul_X e1 va + calcul_X e2 va
  | SUB (e1,e2) -> calcul_X e1 va - calcul_X e2 va
  | MUL (e1,e2) -> calcul_X e1 va * calcul_X e2 va
  | DIV (e1,e2) -> calcul_X e1 va / calcul_X e2 va
  | SIGMA (e1,e2,e3) -> let start = (calcul_X e1 va) in let finish = (calcul_X e2 va) in (sigma_function e3 start finish)
  | X -> va
and sigma_function e s f  =
  if s < f then (sigma_function e (s + 1) f) + (calcul_X e s) else (calcul_X e f)
;;

let rec calculator : exp -> int
= fun exp ->
    match exp with
    | INT n -> n
    | ADD (e1,e2) -> calculator e1 + calculator e2
    | SUB (e1,e2) -> calculator e1 - calculator e2
		| MUL (e1,e2) -> calculator e1 * calculator e2
		| DIV (e1,e2) -> calculator e1 / calculator e2
		| SIGMA (e1,e2,e3) -> let start = calculator e1 in let finish = calculator e2 in (sigma_function e3 start finish )
    | X -> raise Exceptional_Situation
;;

--------------------------------------------------------------------------------


