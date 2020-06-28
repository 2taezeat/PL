4. app


let rec is_mem : 'a -> 'a list -> bool =
  fun e lst ->
    match lst with
      [] -> false
    | hd :: tl -> hd = e || is_mem e tl

let rec app_uniq : 'a list -> 'a list -> 'a list =
  fun l1 l2 ->
    match l1 with
      [] -> l2
    | hd :: tl ->
        if is_mem hd l2 then app_uniq tl l2 else app_uniq tl (l2 @ [hd])
    
let rec app : 'a list -> 'a list -> 'a list =
  fun l1 l2 -> app_uniq l1 (app_uniq l2 [])
;;

--------------------------------------------------------------------------------
7. reach

type graph = (vertex * vertex) list
and vertex = int

(* Input validity checking *)
let rec is_valid : graph * vertex -> bool =
  fun (g, v) ->
    match g with
      [] -> false
    | (s, t) :: tl -> if v = s || v = t then true else is_valid (tl, v)

(* Utility function *)
let rec mem : 'a -> 'a list -> bool =
  fun e lst ->
    match lst with
      [] -> false
    | hd :: tl -> if e = hd then true else mem e tl

(* Main procedure *)
let rec add_vertex : vertex -> vertex list -> vertex list =
  fun v vs -> if mem v vs then vs else v :: vs

let rec next : vertex list -> graph -> vertex -> vertex list =
  fun vs g v ->
    match g with
      [] -> vs
    | (s, t) :: tl ->
        if s = v then next (add_vertex t vs) tl v else next vs tl v

let rec reach_helper : vertex list -> graph -> vertex list =
  fun vs g ->
    let vs' = List.fold_left (fun vs v -> next vs g v) vs vs in
    if vs = vs' then vs' else reach_helper vs' g

let rec reach : graph * vertex -> vertex list =
  fun (g, v) ->
    if is_valid (g, v) then reach_helper [v] g
    else raise (Failure "Invalid Input")
;;


--------------------------------------------------------------------------------