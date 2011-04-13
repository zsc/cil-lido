open Pretty
open Cil
open Lidoutil
open Util

module E = Errormsg
open List
open Linda
open ExtList
open MaybeMonad
open Linda.Algebra

let updateTable h k f =Hashtbl.replace h k @$ f (maybefind Hashtbl.find h k) 
(*let addToTable h k e = *)

let debug = ref true
(*module R = Rational                      *)
(*module V = GroupVector (Rational) (struct*)
(*  type t = location option               *)
(*  let eq = (=)                           *)
(*  let op = dumb2                         *)
(*  let inv = dumb                         *)
(*  let zero = None                        *)
(*  let show a = match a with              *)
(*    | Some l -> showLocation l           *)
(*    | _ -> "C"                           *)
(*  end)                                   *)
(*type equation = V.t                      *)
(*let equations = ref []*)

let viFundecTable : (int,fundec) Hashtbl.t = Hashtbl.create 33 
let fundecPreds : (location,location) Hashtbl.t = Hashtbl.create 33
(*let rec getLocationInstr = function                         *)
(*  | Set(_,_,l) -> l                                         *)
(*  | Call(_,_,_,l) -> l                                      *)
(*  | Asm(_,_,_,_,_,l) -> l                                   *)
(*and getLocationStmt = function                              *)
(*  | {skind = sk} -> getLocationStmtkind sk                  *)
(*and getLocationStmtkind = function                          *)
(*  | Instr il -> getLocationInstr (hd il)                    *)
(*  | Block blk -> getLocationBlock blk                       *)
(*  | Return(_,l)                                             *)
(*  | Goto(_,l)                                               *)
(*  | Break l                                                 *)
(*  | Continue l                                              *)
(*  | If(_,_,_,l)                                             *)
(*  | Switch(_,_,_,l)                                         *)
(*  | Loop(_,l,_,_)                                           *)
(*  | TryFinally(_,_,l)                                       *)
(*  | TryExcept(_,_,_,l) -> l                                 *)
(*and getLocationBlock blk = getLocationStmt @$ hd blk.bstmts *)
(*and getLocationFundec f = getLocationBlock f.sbody          *)
class buildViFundecTableVisitor  = object
  inherit nopCilVisitor
  method vfunc f =
    Hashtbl.add viFundecTable f.svar.vid f;SkipChildren
end
(*let getViFundecTable file =                                      *)
(*  let h = Hashtbl.create 3 in                                    *)
(*  visitCilFileSameGlobals (new buildViFundecTableVisitor h) file;*)
(*  h                                                              *)
(*class lidoFreqnecyVisitor = object                                                                                         *)
(*  inherit nopCilVisitor                                                                                                    *)
(*  method vstmt s =                                                                                                         *)
(*    let loc = getLocationStmt s in                                                                                         *)
(*    addRefList (V.of_list @$ (Some loc,R.mone) :: map (fun s -> (Some (getLocationStmt s),R.one)) s.preds) equations;      *)
(*    (match s.skind with                                                                                                    *)
(*      | If(_,b,b',l) ->                                                                                                    *)
(*        addRefList (V.of_list [Some loc,R.mone;Some (getLocationBlock b),R.one;Some (getLocationBlock b'),R.one]) equations*)
(*      | _ -> ());                                                                                                          *)
(*    DoChildren                                                                                                             *)
(*  method vinst is = (match is with                                                                                         *)
(*    | Call (_,e,_,l) ->                                                                                                    *)
(*      ignore (chopExp e >>= fun (vi,_) ->                                                                                  *)
(*        maybefind Hashtbl.find viFundecTable vi.vid >>= fun fundec ->                                                      *)
(*          Hashtbl.add fundecPreds (getLocationFundec fundec) l;                                                            *)
(*          mzero)                                                                                                           *)
(*    | _ -> ());                                                                                                            *)
(*    SkipChildren                                                                                                           *)
(*end                                                                                                                        *)
        
class findHotStructVisitor = object
  inherit nopCilVisitor
(*  method vstmt*)
end
    
let cntStmt = ref 0
        
class lidoStructPeelWriter = object
  inherit nopCilVisitor
  method vglob gl = match gl with
    GFun(fundec,_) -> E.log "Hi %s\n" fundec.svar.vname;DoChildren
    | _ -> DoChildren
  method vstmt s=
    incr cntStmt;
    DoChildren
end   
  
let structTrans (f:file) =
  Cfg.computeFileCFG f; 
  (visitCilFileSameGlobals (new lidoStructPeelWriter)) f;
  if !debug then E.log "No. of stmts:%d\n" !cntStmt;
  f  