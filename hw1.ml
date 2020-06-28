1.
let rec pascal : int * int -> int
= fun (n, m) ->
  match m with
    | 0 -> 1
    |_  -> match n = m with
          | true -> 1
          | false -> pascal(n-1,m-1) + pascal(n-1,m);;
--------------------------------------------------------------------------------
2.
let rec f1 n a =
    match a with
      | 1 -> true 
      |_  ->  match n mod a with
        | 0 -> false
        |_ -> true && (f1 n (a-1));;

let prime : int -> bool
= fun n -> 
  if n < 2 then false 
  else
    match n with
      | 2 -> true
      |_  -> f1 n (n-1);;
--------------------------------------------------------------------------------
3.
let rec dfact : int -> int
= fun n -> 
  match n with
    | 1 -> 1
    | 2 -> 2
    | 0 -> 1
    |_ -> n * dfact (n-2);;
--------------------------------------------------------------------------------
4.
let rec fastexpt : int -> int -> int
= fun b n ->
  match n with
    | 0 -> 1
    |_ -> match n mod 2 with
        | 1 -> b * (fastexpt b (n-1))
        |_ -> (fastexpt b (n / 2)) * (fastexpt b (n / 2))
;;
--------------------------------------------------------------------------------
5.
let rec iter : int * (int -> int) -> (int -> int)
= fun (n, f) -> 
  match n with
    | 0 -> fun x -> x
    |_ -> fun a -> iter ( (n-1), f ) (f a)
;;
--------------------------------------------------------------------------------
6.
type nat = ZERO | SUCC of nat

let rec natadd : nat -> nat -> nat
= fun n1 n2 -> 
  match n1 with
    |ZERO -> n2
    |SUCC rest -> natadd rest (SUCC n2)
;;


let rec natmul : nat -> nat -> nat
= fun n1 n2 -> 
    match n1 with
    |ZERO -> ZERO
    |SUCC rest -> natadd n2 (natmul rest n2)
;;
--------------------------------------------------------------------------------
7.
type btree =
  | Empty
  | Node of (int * btree * btree)
;;

let rec mem : int -> btree -> bool
= fun n t -> 
  match t with
    | Empty -> false
    | Node (a,l,r) -> if n = a then true else false || mem n l || mem n r
;;
--------------------------------------------------------------------------------
8.
type formula = 
  | True
  | False
  | Not of formula
  | AndAlso of formula * formula
  | OrElse of formula * formula
  | Imply of formula * formula
  | Equal of exp * exp

and exp = 
  | Num of int
  | Plus of exp * exp
  | Minus of exp * exp

let rec calculate : exp -> int
= fun e ->
  match e with
    | Num n -> n
    | Plus (e1,e2) -> calculate e1 + calculate e2
    | Minus (e1,e2) -> calculate e1 - calculate e2
;;

let rec eval : formula -> bool
= fun f -> 
  match f with
    | True -> true
    | False -> false
    | Not f -> if eval f = true then false else true
    | AndAlso (x,y) -> if eval x = true && eval y = true then true else false
    | OrElse (x,y) -> if eval x = false && eval y = false then false else true
    | Imply (x,y) -> if eval x = true && eval y = false then false else true
    | Equal (x,y) -> if calculate x = calculate y then true else false
;;
--------------------------------------------------------------------------------
9.
exception Empty_list;;

let rec max : int list -> int
= fun lst -> 
  match lst with
    | [] -> raise Empty_list
    | [a] -> a
    | h::t -> if h < max t then max t else h
;;
    
let rec min : int list -> int
= fun lst -> 
  match lst with
    | [] -> raise Empty_list
    | [a] -> a
    | h::t -> if h < min t then h else min t
;;
--------------------------------------------------------------------------------
10.
let rec drop : ('a -> bool) -> 'a list -> 'a list
= fun f lst -> match lst with
  | [] -> []
  | h::t -> if f h then drop f t else lst
;;
--------------------------------------------------------------------------------