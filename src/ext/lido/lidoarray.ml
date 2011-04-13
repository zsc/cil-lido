open Pretty
open Cil
open Linda
open MaybeMonad
open Lidoutil
open Util
module IH = Inthash

module E = Errormsg
module UD = Usedef  
module VS = Usedef.VS  
  
let debug = ref false
  
type arraySpans = exp list
let arraySpanTable : arraySpans IH.t = IH.create 29


  
class collectGlobalArraysVisitor vs = object
  inherit nopCilVisitor
  method vglob = function 
    GVar(vi,_,_) when (!Cil.lidoWholeProgram || vi.vstorage = Static) 
      && Heapify.containsArray vi.vtype -> 
      vs := VS.add vi !vs;SkipChildren
    | _ -> DoChildren
end     
let collectGlobalArrays f =
  let vs = ref VS.empty in
  ignore (visitCilFileSameGlobals (new collectGlobalArraysVisitor vs) f);
  !vs


class lidoArrayFlattenTransposeWriter = object
  inherit nopCilVisitor    
  method vglob gl = match gl with
    GFun(fundec,_) -> E.log "Hi %s\n" fundec.svar.vname;DoChildren 
    | _ -> DoChildren
(*  method vstmt s =
    match s.skind,getIndexVariable s.skind with
      Loop _,Some idxVi -> ignore (visitCilStmt (new lidoSimpleArrayFinder idxVi) s);SkipChildren
    | _,_ -> DoChildren
 *)
end   
(*class lidoArrayLiftWriter = object
  inherit nopCilVisitor
                 method*) 
(*let handle_alloc trans = visitCilBlock (new instructionStream 2 trans)*)
        
let arrayTrans (f:file) = (visitCilFileSameGlobals (new lidoArrayFlattenTransposeWriter) f);f
(*let arrayLift (f:file) = (visitCilFileSameGlobals (new lidoArrayLiftWriter) f);f*)  
