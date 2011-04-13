open Pretty
open Cil
open Linda
open List
open ExtList
open MaybeMonad
open Lidoutil
open Util
module IH = Inthash

let shiftr = mkFunction "shiftr" voidType (Some [])
let rotr_till = mkFunction "rotr_till" intType (Some [])

let changeArrayToPointer vi : (typ * exp option) option =
  match vi.vtype with
  | TArray (t, eo, a) -> return (TPtr (t, a), eo)
  | _ -> mzero

let stmtsAtFront : (fundec*stmt list) list ref = ref []

(** Force a local array in function [f] of [vid] to be aligned as [ty]
by converting it to a pointer.*)
let alignArray f vid ty =
  ignore @$ msumRmap f.slocals @$ fun vi ->
    let n = sizeOf ty in
    guard (vi.vid = vid) >> 
	    changeArrayToPointer vi >>= fun (t, eo) ->
	    eo >>= fun e ->
        evalExpr e >>= fun v ->
        guard ( v >= 256L) >>
	      get_pointed_type vi.vtype 1 >>= fun etyp ->
	    let lenNewArray =  divExpr (addExpr (multExpr e (sizeOf etyp)) (predExpr n)) n in
	    let tvi = makeTempVar f (TArray (ulonglongType, Some lenNewArray,[])) in
	    let init = mkStmtOneInstr @$ assign vi (mkAddrOrStartOf (indexArray tvi zero)) in
        vi.vtype <- t;
	      addRefList (f,[init]) stmtsAtFront;
	      return ()
      
let templateRotrTill =
  let j,yy,tmp,tmp2,ll_i = tmap5 (makeVarinfo false "") 
    (intType,ucharPtrType,ucharType,ucharType,ucharType) in
  let yyj = (indexArray yy (viExp j)) in
  let yy0 = (indexArray yy zero) in  
  mkStmtInstrs [assign j zero
                ;assign tmp (Lval yyj)] @
  mkWhile (neqExpr (mkCast (viExp ll_i) intType) (mkCast (viExp tmp) intType)) 
  (mkStmtInstrs[
    mkIncr PlusA (var j) one locUnknown
    ; assign tmp2 (viExp tmp)
    ; assign tmp (Lval yyj)
    ; assignLval yyj (viExp tmp2)
    ]) @
  mkStmtInstrs [assignLval yy0 (viExp tmp)]                   

let transRotateByteArray fdec =
  (*| match with below, also assure yy is char array.*)
(*|       j = 0;
      tmp = yy[j];
      while ( ll_i != tmp ) {
         j++;
         tmp2 = tmp;
         tmp = yy[j];
         yy[j] = tmp2;
      };
      yy[0] = tmp; *)
  function [{ skind = Instr is }                                                                                
    ;{ skind = Loop ({bstmts={skind=If(BinOp(_,ll_i,_,_),_,_,_)}::_},_,_,_)} as s2
    ;{ skind = Instr is3 }] ->
      let is' = lastn 2 is in
      let is3' = take 1 is3 in
      unViExp ll_i >>= fun ll_i_vi ->
(*        if ll_i_vi.vname = "ll_i" then begin*)
      unifyBlock (mkBlock (mkStmtInstrs is'@[s2]@mkStmtInstrs is3')) 
        (mkBlock templateRotrTill) >>= fun l ->
          toMap l >> begin
        match (last is) with
          | Set(_,Lval (Var yy,Index (je,NoOffset)),_) ->
            unViExp je >>= fun j ->
            alignArray fdec yy.vid ulonglongType;
            return @$ mkStmtInstrs @$
                take 2 is 
                @[Call(Some (var j),viExp rotr_till,[viExp yy;ll_i],locUnknown)]
                @drop 1 is3
          | _ -> mzero
        end
(*        end else mzero*)
(*|         for (; j > 3; j -= 4) {
            yy[j]   = yy[j-1];
            yy[j-1] = yy[j-2];
            yy[j-2] = yy[j-3];
            yy[j-3] = yy[j-4];
         }
         for (; j > 0; j--) yy[j] = yy[j-1];
         yy[0] = tmp; *)
  | [{ skind = Loop _ } as s1;{ skind = Loop _ } as s2;{ skind = Instr is3 }] ->
    getLoopStructOneStmt s1 >>= fun ls ->
      getLoopStructOneStmt s2 >>= fun ls2 ->
        guard (ls.vi.vid = ls2.vi.vid) >>
        fullyRoll ls >>= fun body ->
        firstInstr*@ hd @$ body >>= fun instr ->
        firstInstr (hd ls2.body) >>= fun instr' ->
        guard (equalInstr instr instr') >>
        lhs instr >>= fun lv ->
        unViExp (Lval lv) >>= fun (yy) -> begin
          match hd is3 with
(*            | Set ((Mem(BinOp(PlusPI, Lval(Var yy', NoOffset),idx,_)), NoOffset),tmp,_)*)
            | Set((Var yy',Index(idx,NoOffset)),tmp,_) 
                when equalExp idx zero && yy'.vid = yy.vid ->
                  alignArray fdec yy.vid ulonglongType;
                  return @$ [mkStmtOneInstr
                      @$ Call(None,viExp shiftr,[viExp yy;viExp ls.vi;tmp],locUnknown)]
            | _ -> mzero
        end
   | _ -> mzero
 
let optimize file =
  visitCilFile (new statementStream 3 (transRotateByteArray)) file;
  (foreach !stmtsAtFront @$ fun (fdec,stmts) ->
    fdec.sbody.bstmts <- stmts @ fdec.sbody.bstmts);
  file
