open Pretty
open Cil
open Linda
open MaybeMonad
open Lidoutil
open Util
module IH = Inthash
module UD = Usedef  
module VS = Usedef.VS

type simpleArrayInfo = SAConst of constant (*constant array*)
  | SAId (* array value always equal to index *)
  | SATop (* content of array is complex *)
  | SABot (* nothing known about array*)
let arraySimpleInfoTable : simpleArrayInfo IH.t = IH.create 31
let mergeSimpleArrayInfo i i2 = match i, i2 with
    SABot, i'
  | i', SABot -> i'
  | SATop, _
  | _, SATop -> SATop
  | SAConst c, SAConst c2 -> if equalConstant c c2 then SAConst c else SATop
  | x, x2 when x = x2 -> x
  | _ -> SATop

let getPattern idxVi = function Const c -> SAConst c
  | Lval(Var vi, NoOffset) when vi.vid = idxVi.vid -> SAId
  | _ -> SATop
let unGetPattern idxVi = function SAConst c -> Some (Const c)
  | SAId -> Some (Lval(Var idxVi, NoOffset))
  | _ -> None
class lidoSimpleArrayFinder idxVi = object
  inherit nopCilVisitor
  method vinst = function
      Set ((Mem (BinOp(IndexPI, Lval(Var arr, NoOffset), _, _) as e), o), e2, loc) ->
        E.log "assign %a with %a at %d line of %s \n" d_plainexp e d_plainexp e2 loc.line loc.file;
        IH.replace arraySimpleInfoTable arr.vid
          (maybe SABot (mergeSimpleArrayInfo (getPattern idxVi e2))
              (maybefind IH.find arraySimpleInfoTable arr.vid));
        SkipChildren
    | _ -> SkipChildren
end
let checkSimpleArray idxVi stmt = ignore (visitCilStmt (new lidoSimpleArrayFinder idxVi) stmt)
let simpleArrayFinder vs = function
    [{ skind = Instr _ } as s1 ;{ skind = Loop _ } as s2] ->
(*      if VS.is_empty (VS.inter vs (snd (UD.computeDeepUseDefStmtKind s2.skind))) then None else*)
        getLoopStruct [s1; s2] >>= fun ls ->
          List.iter (checkSimpleArray ls.vi) ls.body;
          mzero
  | _ -> None
 
let transMemcpy arrs fdec = function
    [Call(None, Lval(Var vi, NoOffset),
  [Lval(Var dst, NoOffset) as e; Lval(Var src, NoOffset); len], _)]
  when vi.vname ="memcpy" -> begin
        maybefind IH.find arraySimpleInfoTable src.vid >>= fun x ->
          guard (VS.mem src arrs) >>= fun _ ->
            let idx = makeTempVar fdec uintType in
            unGetPattern idx x >>= fun p ->
                let assign = Set(shift e (Lval(var idx)), p, locUnknown) in
                let forLoop = expand_loop_struct
                    { vi = idx; init = zero; bound = len; stride = one; body =[mkStmtOneInstr assign]} in
                Some (forLoop)
      end
  | _ -> None

let optimizeSimpleArray file =
  let arrs = collectGlobalArrays file in
  ignore (visitCilFileSameGlobals
        (new statementStream 2 (const (simpleArrayFinder arrs))) file);
  ignore (visitCilFile (new instructionStream 1 (transMemcpy arrs)) file)