open List
open Printf
open Linda
open ExtList
open ListMonad

let debug = ref false

type 'a equation= 
  | Equal of 'a*'a*int
  | Val of 'a*int
type 'a t = 'a equation
exception Inconsistent

open Cil
type elem =
  | EVarinfo of varinfo
  | EField of fieldinfo
let eq e e' = match e,e' with
  | EVarinfo vi,EVarinfo vi' -> vi.vid = vi'.vid
  | EField fi,EField fi' -> fi.fname = fi'.fname && fi.fcomp.ckey = fi'.fcomp.ckey
  | _ -> false 
let show_elem = function
  | EVarinfo vi -> "(EVarinfo " ^ vi.vname ^ ")"
  | EField fi -> "(EField " ^  fi.fname ^ ")"
let show_elem_eq = function 
  | Equal(a,a',n) -> "(Equal " ^ show_elem a ^ "," ^ show_elem a' ^ "," ^ string_of_int n ^ ")"
  | Val(a,n) -> "(Val " ^ show_elem a ^ "," ^ string_of_int n ^ ")"
let show_elem_n = (fun (elem,n) -> show_elem elem ^ "," ^ string_of_int n)
let eqEquation eeq eeq' = match eeq,eeq' with
  | Val (a,_),Val(a',_) -> 
    eq a a'
  | Equal (a,a2,_),Equal (a',a2',_) -> eq a a' && eq a2 a2'
  | _ -> false
(*vi vi' = vi.vid = vi'.vid*)
let neq vi vi' = not (eq vi vi') 


(*post: s<>s' *)
let simp e = match e with
  | Val _ -> return e
  | Equal(s,s',i) ->
    if neq s s' then return e else
      if i=0 then mzero else 
        raise Inconsistent 

(* pre: e is processed by simp post: occurrences of s is elim'ed *)
let applyVal s i e = match e with
  | Val(s', i') ->
      if (neq s' s || i = i') then return e else
        raise Inconsistent
  | Equal(s', s2', i') ->
      if eq s' s then return (Val(s2', i - i')) else
      if eq s2' s then return (Val(s', i'+ i)) else
        return e
(* pre: e is processed by simp, s<>s2 post: occurrences of s is elim'ed *)
let applyEq s s2 i e = match e with
  | Val(s', i') ->
      if eq s s' then return (Val(s2, i'- i)) else return e
  | Equal(s', s2', i') ->
      if eq s s' then simp (Equal(s2, s2', i'- i)) else
      if eq s s2' then simp (Equal(s', s2, i + i')) else
        return e
let dump l' =
  if !debug then begin
  print_endline "------------------"; 
  iter print_endline (map show_elem_eq l')
  end
let dump_res res =
  if !debug then begin  
  print_endline "--------RES----------"; 
  iter print_endline (map show_elem_n res)
  end
let solve l =
  try
    let rec loop acc = function 
      | [] -> acc
      | x::xs as l' -> begin match pick (function Val _ as x -> Some x | _ -> None) l' with
          | None -> begin match x with
            | Equal(s,s2,i) ->
              let xs' = concatMap (applyEq s s2 i) xs in
              dump (x::xs'); 
              loop acc xs'
            | _ -> failwith "impossible"
            end
          | Some (Val(s,i) as x,rest) ->
            let rest' = concatMap (applyVal s i) rest in
            dump (x::rest');
            loop ((s,i)::acc) rest'
          | _ -> failwith "impossible"
          end in 
     let l' = nubBy eqEquation @$ join @$ map simp l in
     if !debug then dump l';
     let res = nubBy (fun (a,b) (a',b') -> eq a a' && b=b' ) @$ loop [] @$ l' in
     dump_res res;
     Some (res)
  with Inconsistent -> 
    None
 
let test () =
  ()
(*  match solve [Equal("a","b",1);Val("b",2);Val("d",1)] with      *)
(*    | None -> print_endline "Inconsistent"                       *)
(*    | Some l -> print_list (fun (a,b) -> a^":"^string_of_int b) l*)