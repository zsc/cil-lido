open List
open Linda
open ExtList
open StateMonad
open MaybeMonad
open Pretty
open Cil
open Lidoutil
open RankEquation

let debug = ref false

(** We assign each variable a [rank], reflecting its level of reference. 
 A plain integer has rank 0, and a pointer to such integer has rank 1, and so on.
We establish rank by creating a set of rank equations.*)

let rankEqs = ref []
let getType = function 
  | EVarinfo vi -> vi.vtype
  | EField fi -> fi.ftype
let admitField (vi,l) =
  let rec loop a n = function
    | [] -> ()
    | AField fi :: xs ->
      addRefList (Val(a,n)) rankEqs;
      loop (EField fi) 0 xs
    | (AMem|AIndex _)::xs -> loop a (n+1) xs
    | AAddress ::xs ->
        loop a (n + (if isArrayType (getType a) then 0 else -1)) xs       
    | (APlus _|ACastE _) :: xs -> loop a n xs in
  loop (EVarinfo vi) 0 l
let prune (vi,l) =
  let rec loop vi n = function
    | [] -> EVarinfo vi,n
    | AField fi ::_ -> EField fi,n
    | (AMem|AIndex _) ::xs -> loop vi (n+1) xs
    | AAddress :: xs ->
      loop vi (n + (if isArrayType vi.vtype then 0 else -1)) xs 
    | (APlus _|ACastE _) :: xs -> loop vi n xs in
  admitField (vi,l);
  let l = loop vi 0 (rev l) in
  if !debug then print_endline (show_elem_n l); 
  l

let rec markExp n e =
  ignore (chopExp e >>= fun (vi,l) -> mark n (vi,l);return ())
and mark n (vi,l) =
  let (a,n') = prune (vi,l) in
  markL 0 l;
  addRefList (Val(a,n+n')) rankEqs
and markL n l=
  foreach l (function
    | APlus e                                           
    | AIndex e -> markExp n e 
    | _ -> ())
let buildEquation (vi,l) (vi',l') =
(*  markL 0 (l@l');    *)
  let (a,n) = prune (vi,l) in
  let (a',n') = prune (vi',l') in
  addRefList (Equal(a,a',n-n')) rankEqs
  
class collectIndexVisitor = object
  inherit nopCilVisitor
  method vinst inst = match inst with
    | Set (lv,e,_) ->
      let (vi,l) = chopLval lv in
        markL 0 l;
        ignore (chopExp e >>= fun (vi',l') ->
          markL 0 l';
          buildEquation (vi,l) (vi',l');
          return ());
      SkipChildren
    | Call(Some lv,_,_,_) ->
      let (vi,l) = chopLval lv in
        markL 0 l;
      SkipChildren 
    | _ -> SkipChildren
end
let mayEqual rankTable fi fi' =
  Some true <> (assocBy eq (EField fi) rankTable >>= fun r ->
      assocBy eq (EField fi') rankTable >>= fun r' ->
          return (r <> r'))
(** transform union to struct *)
class unionToStructVisitor rankTable = object
  inherit nopCilVisitor
  method vtype ty = match ty with
    | TComp (ci, _) ->
        if not ci.cstruct && hasNoDupesBy (mayEqual rankTable) ci.cfields then begin
          let fnames = map (fun fi -> [fi.fname]) ci.cfields in
          FrontcTrans.unionToStructUnionFieldNames := Some fnames
(*          foreach ci.cfields @$ fun fi ->                                      *)
(*              E.log "%s:%s\n%a\n" fi.fname fi.fcomp.cname d_plaintype fi.ftype;*)
(*              ci.cstruct <- true                                               *)
        end;
        DoChildren
    | _ -> DoChildren
end

let trans file = file 
  |> visitCilFile (new collectIndexVisitor);
  ignore (RankEquation.solve !rankEqs >>= fun rankTable ->
      return (file |> visitCilFile (new unionToStructVisitor rankTable)));
  file

(* for testing *)

let log_access (vi, es) =
  E.log "%s\n" vi.vname;
  foreach es (function
      | AField fi -> E.log "%s\n" fi.fname
      | APlus e -> E.log "APlus %a\nAPlus %a\n" d_exp e d_plainexp e
      | AIndex e -> E.log "AIndex %a\nAIndex %a\n" d_exp e d_plainexp e
      | AMem -> E.log "AMem\n"
      | AAddress -> E.log "AAddress\n"
      | ACastE ty -> E.log "ACastE %a\n" d_plaintype ty
    )

class lidoTestVisitor = object
  inherit nopCilVisitor
  method vinst inst = match inst with
    | Set(lv, e, _)
    (* | Call(Some lv,_,_,_) *)
    ->
        E.log "--------------\n";
        E.log "%a\n" d_instr inst;
        E.log "%a\n" d_plaininstr inst;
        E.log "%a\n" d_lval lv;
        E.log "%a\n" d_plainlval lv;
        
        let (vi, es) = chopLval lv in
            log_access (vi, es);
            ignore @$ prune (vi,es);
        let lv' = unChopLval (vi, es) in
          E.log "%a\n%a\n" d_lval lv' d_plainlval lv';
          E.log "\n";
        ignore (chopExp e >>= fun (vi,es) ->
          log_access (vi, es);
          ignore @$ prune (vi,es);
          return ());
        SkipChildren
    | _ -> SkipChildren
end