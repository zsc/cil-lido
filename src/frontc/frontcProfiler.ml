open Cabs
open Cabsvisit
open List
open Linda
open MaybeMonad
open ExtList
module H = Hashtbl
module E = Errormsg
open Lidoutil
open FrontcUtil


let enable = ref false
let debug = ref true

let int64 = ref "long"
let dumpFilename = ref "stdout"

type 'a range = 'a list option
let inRange e (r:'a range) = maybe true (fun l -> mem e l) r

(*type profileType = PLoop of location | PFunction of string range | PVariable of (string * location) range*)

(* To build a profiler, we construct an array of counters, each of 64-bit, and put this array at the start of file. *)

(*let counters = GText (Printf.sprintf "%s ;\n" !int64 )*)
(*let showCounters =  *)

(* Then at each given location, we insert the counting facility. *)

(* at the end of execution, we dump all counters to a assigned file or to stdout *)
(*let dump = match !dumpFilename with*)
(*  | "stdout" -> output_string "{   *)
(*                                   *)
(*    }"                             *)


let instrFunc = ref true
let instrIf = ref true
let instrLoop = ref true

let counter = ref 0
let getCount () =
  incr counter;
  !counter

let getFlagForFunc fname =
  "__prof_" ^ fname
class instrumenter flagVars = object
    inherit nopCabsVisitor
    method vdef def = match def with
    | FUNDEF ((spec,name),blk,loc,loc') ->
      if !instrFunc then
        let fname = show_plain_cabs_name name in
        let incrFlag = incrVar (getFlagForFunc @$ fname) loc in
        E.log "fn:%s\n" fname;
        addRefList fname flagVars;
          ChangeDoChildrenPost ([def],map (
            function FUNDEF (sn,blk,loc,loc') -> 
              FUNDEF(sn,{blk with bstmts = incrFlag :: blk.bstmts},loc,loc') 
                    | x -> x))
      else
        DoChildren
    | _ -> SkipChildren
end

let dumpStmt fnames loc =
  let flags = map getFlagForFunc fnames in
  call "printf" (string (String.concat "" (map (fun f -> (Printf.sprintf "%%d : %s\n" f)) fnames)) :: map var flags) loc  
(*  let ivarDef = declare_int "i" loc in                                                                                             *)
(*  let flags = map getFlagForFunc fnames in                                                                                         *)
(*  mkBlockStmt                                                                                                                      *)
(*	  [ivarDef;mkLoop (var "i") (integer 0) (integer (length fnames))                                                                *)
(*	    (call "printf" (string (String.concat "" (map (fun f -> (Printf.sprintf "%%d : %s\n" f)) flags)) :: map var flags) loc) loc] *)
(*    loc                                                                                                                            *)
let instrumentFunction cabs = 
  let fnames = ref [] in
  let loc = ref None in
  let cabs' = (visitCabsFile (new firstDefLoc loc)) *@ (visitCabsFile (new instrumenter fnames)) @$ cabs in
  let flagDefs = declare_flags_def [SpecType Tint] (map getFlagForFunc !fnames) (fromSome !loc) in
  (insertOnMainReturn (dumpStmt !fnames) *@
    insertBeforeFirstDef flagDefs) cabs'
  
let instrument cabs = 
  guardTrans !enable (
    guardTrans !instrFunc instrumentFunction) cabs

(*open Linda.Algebra.Rational         *)
(*class iterGlobalVisitor f = object  *)
(*    inherit nopCabsVisitor          *)
(*    val curFreq = ref one           *)
(*    method vdef def = match def with*)
(*      | FUNDEF _ ->                 *)
(*        curFreq := ref one          *)
(*        DoChildren                  *)
(*      | _ ->                        *)
(*end                                 *)