open Printf
open List
open Cil
open Linda
open ExtList
open MaybeMonad
open Pretty
module E=Errormsg
module IH=Inthash  
module M=Machdep
module DF=Dataflow
module VS = Usedef.VS
open Expcompare  

let debug = ref true
let lu = locUnknown

let plainCilPrinter = new plainCilPrinterClass
let d_plainblock () x = plainCilPrinter#pBlock () x
let d_plainstmt () x = plainCilPrinter#pStmt () x
let d_plaininstr () x = plainCilPrinter#pInstr () x
let d_plainglob () x = new plainCilPrinterClass#pGlobal () x

class lidoDumpStmtVisitor = object
  inherit nopCilVisitor
  method vglob gl =
    E.log "%a\n" d_plainglob gl;
    SkipChildren
end

let dumpStmtsOfFile file = visitCilFile (new lidoDumpStmtVisitor) file;file

(*| expand utilities *)
let theMachine : M.mach ref = ref M.gcc
(** measured in bytes, we force ILP32 *)
let rec sizeOf_int = function
  | TInt((IChar|ISChar|IUChar), _) -> 1
  | TInt((IShort|IUShort), _) -> !theMachine.M.sizeof_int
  | TInt((IInt|IUInt), _) -> !theMachine.M.sizeof_int
  | TInt((ILong|IULong), _) -> !theMachine.M.sizeof_int
  | TInt((ILongLong|IULongLong), _) -> !theMachine.M.sizeof_longlong
  | TEnum _ -> !theMachine.M.sizeof_enum
  | TFloat(FFloat, _) -> !theMachine.M.sizeof_float 
  | TFloat(FDouble, _) -> !theMachine.M.sizeof_double
  | TFloat(FLongDouble, _) -> !theMachine.M.sizeof_longdouble
  | TNamed (t, _) -> sizeOf_int t.ttype
  | TArray (t, _, _) -> sizeOf_int t
  | TPtr _ | TBuiltin_va_list _ -> !theMachine.M.sizeof_ptr
  | _ -> failwith "NYI"

let ulonglongType = TInt(IULongLong,[])
let longlongType = TInt(ILongLong,[])

let guardTrans bool f = if bool then f else id
let equalConstant c c2 = compareExp (Const c) (Const c2)
  
let notExpr exp = UnOp(LNot,exp,typeOf exp)  
let succExpr exp = BinOp(PlusA,exp,one,typeOf exp)  
let predExpr exp = BinOp(MinusA,exp,one,typeOf exp)

let addExpr a b = BinOp(PlusA,a,b,typeOf a)
let subExpr a b = BinOp(MinusA,a,b,typeOf a)
let negExpr a = subExpr zero a      
let multExpr a b = BinOp(Mult,a,b,typeOf a)
let divExpr a b = BinOp(Div,a,b,typeOf a)
let modExpr a b = BinOp(Mod,a,b,typeOf a)
let borExpr a b = BinOp(BOr,a,b,typeOf a)
let bxorExpr a b = BinOp(BXor,a,b,typeOf a)
let bandExpr a b = BinOp(BAnd,a,b,typeOf a)
let eqExpr a b = BinOp(Eq,a,b,intType)
let neqExpr a b = BinOp(Ne,a,b,intType)
let shiftLeftExpr a b = BinOp(Shiftlt,a,b,typeOf a)
let shiftRightExpr a b = BinOp(Shiftrt,a,b,typeOf a)    
let alignExpr e n =
  let nE = integer n in
  multExpr (divExpr (addExpr e (integer (n-1))) nE) nE
let evalExpr e = match constFold true e with
  | Const (CInt64 (i,_,_)) -> return i
  | _ -> mzero
(*let validUnification res =                         *)
(*  return true = (res >>= fun l -> return (isMap l))*)
let mergeUnification r r' =
    liftM2 (@) r r' >>= fun l ->
      toMap l 
(** unify two exp and produce a mapping between vid of two if unifiable*)
let rec compatibleTyp t t2 =
  t==t2 || 
  match t,t2 with
  | TVoid _,TVoid _-> true
  | TInt(ik,_),TInt(ik',_) -> ik=ik'
  | TFloat(fk,_),TFloat(fk',_) -> fk=fk'
  | (TPtr(t,_)|TArray(t,_,_)),(TPtr(t',_)|TArray(t',_,_)) ->
    compatibleTyp t t'
  | _ -> failwith "NYI"
let rec unifyExp (e1: exp) (e2: exp) : (int*int) list option =
  if e1 == e2 then return [] else
  let res = match e1, e2 with
  | Lval lv1, Lval lv2
  | StartOf lv1, StartOf lv2
  | AddrOf lv1, AddrOf lv2 -> unifyLval lv1 lv2
  | UnOp (uop1, e1,t1), UnOp (uop2, e2,t2) ->
    guard (uop1==uop2 && compatibleTyp t1 t2) >>
     unifyExp e1 e2
  | BinOp(bop1, l1, r1, _), BinOp(bop2, l2, r2, _) ->
      guard (bop1 = bop2) >> 
        mergeUnification (unifyExp l1 l2) (unifyExp r1 r2)
  | CastE(t1, e1), CastE(t2, e2) ->
      guard (compatibleTyp t1 t2) >>
        unifyExp e1 e2
  | _ ->
    isInteger (constFold true e1) >>= fun i1 ->
      isInteger (constFold true e2) >>= fun i2 ->
        guard (i1=i2) >>
        return [] in
(*  if res=mzero then E.log "match failed for %a\n%a\n" d_plainexp e1 d_plainexp e2;*)
  res
and unifyOffset (off1: offset) (off2: offset) =
  match off1, off2 with
  | Field (fld1, off1'), Field (fld2, off2') ->
      guard (fld1 == fld2) >>
      unifyOffset off1' off2'
  | Index (e1, off1'), Index (e2, off2') ->
    mergeUnification (unifyExp e1 e2) (unifyOffset off1' off2')
  | NoOffset, NoOffset -> return []
  | _ -> mzero
and unifyLval (lv1: lval) (lv2: lval) =
  if lv1 == lv2 then return [] else
  match lv1, lv2 with
  | (Var vi1, off1), (Var vi2, off2) ->
    mergeUnification (unifyOffset off1 off2) (return [(vi1.vid,vi2.vid)])
  | (Mem e1, off1), (Mem e2, off2) ->
    mergeUnification (unifyExp e1 e2) (unifyOffset off1 off2)
  | _ -> mzero
let unifyInstr is is2 =
  if is==is2 then return [] else
    match is,is2 with
      | Set(lv,e,_),Set(lv',e',_) ->
        mergeUnification (unifyLval lv lv') (unifyExp e e')
      | Call (lvo,e,es,_),Call (lvo',e',es',_) ->
        fold_left (liftM2 (@)) (return []) @$ [join @$ (liftM2 unifyLval) lvo lvo'
        ; unifyExp e e'] @ zipWith unifyExp es es'
      | _ -> mzero

                
let rec unifyStmt s s2 =
  if s==s2 then return [] else
    match s.skind, s2.skind with
      | Instr is, Instr is' -> 
        fold_left (liftM2 (@)) (return []) @$ zipWith unifyInstr is is'
      | Return (eo,_),Return (eo',_) -> join @$ (liftM2 unifyExp) eo eo'
      | Break _,Break _ -> return []
      | Continue _,Continue _ -> return []
      | If _,If _ -> return []
(*      | If (e,b,b2,_),If(e',b',b2',_) ->                      *)
(*        mergeUnification (unifyExp e e') @$                   *)
(*        mergeUnification (unifyBlock b b') (unifyBlock b2 b2')*)
      | Loop (b,_,_,_),Loop(b',_,_,_) -> unifyBlock b b'
      | Block b,Block b' -> unifyBlock b b'
      | _ -> mzero 
and unifyBlock b b' =
  let l = zipWith unifyStmt b.bstmts b'.bstmts in
  guard (length b.bstmts = length b'.bstmts) >>
  let res = fold_left (liftM2 (@)) (return []) @$ l in
(*  if res = mzero then                                                  *)
(*    E.log "unifyBlock failed\n%a\n%a\n" d_plainblock b d_plainblock b';*)
    res
  

let equalTyp = compareTypes
let equalLval = compareLval
let equalExp = compareExp
let equalExpStripCasts = compareExpStripCasts
let equalInstr is is2 = match is,is2 with
  | Set(lv,e,_),Set(lv',e',_) -> equalLval lv lv' && equalExp e e'
  | Call(lvo,e,es,_),Call(lvo',e',es',_) ->
    equalOptionsBy compareLval lvo lvo' && equalExp e e' && equalBy equalExp es es'
  | _ -> false 
let rec equalStmt s s2 = null s.labels && null s2.labels &&
    match s.skind,s2.skind with
  | Instr is,Instr is' -> all id (zipWith equalInstr is is')
  | Return(eo,_),Return(eo',_) -> equalOptionsBy equalExp eo eo'
  | Break _,Break _ 
  | Continue _,Continue _ -> true
  | If (e,b,b2,_),If(e',b',b2',_) -> equalExp e e' && equalBlock b b' && equalBlock b2 b2'
  | Loop (b,_,_,_),Loop(b',_,_,_) -> equalBlock b b'
  | Block b,Block b' -> equalBlock b b'
  | _ -> false
and equalBlock b b' = equalBy equalStmt b.bstmts b'.bstmts

let rec derefTypeSig i ts =
  if i=0 then Some ts
  else match ts with
    TSArray (ts',_,_) 
    | TSPtr (ts',_) -> derefTypeSig (i-1) ts'
    | _ -> None
(*let is_pointer_type_of t1 t2 = derefTypeSig 1 (typeSig t1) = Some (typeSig t2)*)
let ucharType = TInt(IUChar,[])
let ucharPtrType = TPtr(TInt(IUChar,[]),[])
let mkPointerType typ = TPtr(typ,[])
let rec get_pointed_type typ i = 
  if i=0 then Some typ else
  match unrollType typ with 
    | TPtr(typ',_) -> get_pointed_type typ' (i-1) 
    | TArray(typ',_,_) -> get_pointed_type typ' (i-1) 
    | _ -> E.log "typ: %a\n" d_plaintype typ;None
let viExp vi = Lval(var vi)
let rec unViExp = function
  | Lval (Var vi,_) -> return vi
  | Lval (Mem e,_) -> unViExp e
  | CastE (_,e) -> unViExp e 
  | _ -> mzero
let shiftPointer p i = 
  (Mem(BinOp(IndexPI,Lval p,i,fromSome (get_pointed_type (typeOfLval p) 1))),NoOffset) 

let indexArray a e = Var a,Index(e,NoOffset)
let assign vi e =  Set (var vi, e, locUnknown)
let assignLval lv e =  Set (lv, e, locUnknown)
let assignIndex addr i e = 
  Set ((Mem(BinOp(PlusPI,Lval (var addr),i,typeOfLval (var addr))),NoOffset), e, locUnknown)
let isShift vi i = function
  | Lval(Mem(BinOp(IndexPI,Lval(Var vi',NoOffset),i',_)),NoOffset) -> vi.vid = vi'.vid && i=i'
  | _ -> false 
let mkLoop stmts =
  mkStmt (Loop(mkBlock stmts,locUnknown,None,None))
(*let mkWhileNot ~(break:exp) ~(body: stmt list) : stmt list =             *)
(*  [ mkStmt (Loop (mkBlock (mkStmt (If(break,                             *)
(*                                      mkBlock [ mkStmt (Break lu)],      *)
(*                                      mkBlock [ mkEmptyStmt () ], lu)) ::*)
(*                           body), lu, None, None)) ]                     *)
type array_type_struct = varinfo * exp list (* a[2][1] will have [integer 2;one] here*) 
type array_struct = varinfo * exp list (* a[0][1] will have [zero;one] here*) 

type access = 
  | AIndex of exp
  | APlus of exp
  | AField of fieldinfo
  | AAddress
  | AMem
  | ACastE of typ
let absorbIndex e es = match take 1 (rev es) with
  | [APlus e'] -> trimLast es @[APlus (addExpr e e')]
  | _ -> es@[APlus e] 
  
let rec chopExp = function
  | StartOf lv
  | AddrOf lv ->
    let (vi,es) = chopLval lv in
      return (vi,es@[AAddress])
  | Lval lv -> return @$ chopLval lv
  | CastE (t ,e ) -> 
    chopExp e >>= fun (vi,es) ->
      return (vi,es@[ACastE t])
  | BinOp((PlusPI|IndexPI),addr,e,_) ->
    chopExp addr >>= fun (vi,es) ->
      return (vi,absorbIndex e es)
  | BinOp((MinusPI),addr,e,_) ->
    chopExp addr >>= fun (vi,es) ->
      return (vi,absorbIndex (negExpr e) es)  
  | e ->
(*    E.log "chopExp:%a\n" d_plainexp e;*)
    mzero
and chopLval (lh,off) =
    fromSome (chopLhost lh >>= fun (vi,es) ->
      chopOffset off >>= fun es2 -> 
        return (vi, es @ es2))
and chopLhost = function
  | Var vi ->     
    return (vi, [])
  | Mem e ->
    chopExp e >>= fun (vi,es) ->      
      return (vi, es@[AMem])
and chopOffset = function
  | NoOffset -> return []
  | Index (e,off) ->
    chopOffset off >>= fun es ->
      return @$ (AIndex e) :: es
  | Field(fi,off) ->
    chopOffset off >>= fun es ->
      return @$ AField fi :: es     

let typeOfLhost lh = typeOfLval (lh,NoOffset)
let derefExp e = Lval(Mem e,NoOffset)
let derefLhost lh = Mem(Lval(lh,NoOffset))

let rec unChopLhost lh off l =
  match l with
  | [] -> lh,off
  | AMem ::xs -> unChopLhost (Mem (Lval (lh,off))) NoOffset xs
  | AAddress ::APlus e::AMem::xs ->
    let addr = mkAddrOrStartOf (lh,off) in
      unChopLhost ((Mem(BinOp(PlusPI,addr,e,typeOf addr)))) off xs
  | AAddress ::ACastE ty ::APlus e::AMem::xs ->
    let addr = CastE(ty,mkAddrOrStartOf (lh,off)) in
      unChopLhost ((Mem(BinOp(PlusPI,addr,e,typeOf addr)))) off xs    
  | APlus e::AMem::xs ->
    let addr = Lval(lh,off) in 
    unChopLhost ((Mem(BinOp(PlusPI,addr,e,typeOf addr)))) off xs
  | AIndex e::xs ->
    unChopLhost lh (addOffset (Index(e,NoOffset)) off) xs
  | AField fi::xs -> begin match unrollType @$ typeOfLval (lh,off) with
    | TComp _ -> unChopLhost lh (addOffset (Field(fi,NoOffset)) off) xs
    | TPtr _ -> unChopLhost (Mem(Lval(lh,off))) (Field(fi,NoOffset)) xs
    | _ -> failwith "unChopLhost"
    end
  | _ -> failwith "unChopLhost"
let rec unChopLval (vi,l) = unChopLhost (Var vi) NoOffset l

let test1 f = 
  let tmp = makeVarinfo false "tmp" intPtrType in
  let e = Lval(Mem(BinOp(IndexPI,Lval(Var tmp,NoOffset),integer 3,intPtrType)),NoOffset) in
  E.log "%a\n" d_plainexp e;
  E.log "%a\n" d_exp e

(*let test2 f =                                      *)
(*  visitCilFile (new Union2struct.lidoTestVisitor) f*)

let doTest = test1

let mkIncr op v e loc = Set(v,BinOp(op,Lval v,e,typeOf e),loc)  
let mkBlockStmt res = mkStmt(Block(mkBlock(res)))
let mkStmtInstrs = function [] -> []
      | is -> [mkStmt (Instr is)] 
let mkStmtInstrsMaybe = function [] -> None
      | is -> Some (mkStmt (Instr is))

let mkFunction ?isVarArg: (isVarArg = false) name retType mayArgs : varinfo =
  makeGlobalVar name (TFun(retType, mayArgs,isVarArg, []))

let mkForIncrNoInit ~(iter : varinfo) ~stopat:(past: exp) ~(incr: exp) 
    ~(body: stmt list) : stmt list = 
      (* See what kind of operator we need *)
  let compop, nextop = 
    match unrollType iter.vtype with
      TPtr _ -> Lt, PlusPI
    | _ -> Lt, PlusA
  in
  mkFor 
    []
    (BinOp(compop, Lval(var iter), past, intType))
    [ mkStmt (Instr [(Set (var iter, 
                           (BinOp(nextop, Lval(var iter), incr, iter.vtype)),
                           locUnknown))])] 
    body

(** Recover structure of simple natural loops *)
type loop_struct = {
  vi:varinfo;
  init:exp option;
  bound:exp;
  stride:exp;
  body:stmt list;
}
let expand_loop_struct ls = match ls.init with
  | Some init -> mkForIncr ls.vi init ls.bound ls.stride ls.body
  | None -> mkForIncrNoInit ls.vi ls.bound ls.stride ls.body

let dump_loop_struct ls1 = 
  E.log "vi.vname %s\n init %s\n bound %a\n stride %a\n"
                        ls1.vi.vname (sprint 80 (maybe (text "") (d_plainexp ()) ls1.init))
                        d_plainexp ls1.bound d_plainexp ls1.stride

let loop_struct_compaitble ls1 ls2 = (*too strict TODO*)
    ls1.init = ls2.init 
      && ls1.bound = ls2.bound 
      && ls1.stride = ls2.stride
let findIncr = function
  | Set ((Var vi, NoOffset),
    (BinOp((PlusA | MinusA) as op, Lval (Var vi', NoOffset), e, _)
  | BinOp((PlusA) as op, e, Lval (Var vi', NoOffset), _)), _)
  when vi.vid = vi'.vid ->
      if isSome (unViExp e >>= fun vi'' -> guard (vi''.vid = vi.vid))
      then [] else [vi, if op = PlusA then e else negExpr e]
  | _ -> []
(*let matchIncrOf vi = function                               *)
(*  | Set ((Var vi', NoOffset),                               *)
(*        (BinOp(PlusA, Lval (Var vi'', NoOffset), e, _)      *)
(*        | BinOp(PlusA, e, Lval (Var vi'', NoOffset), _)), _)*)
(*  when vi.vid = vi'.vid && vi.vid = vi''.vid -> Some e      *)
(*  | _ -> None                                               *)

let matchAssignOf vi = function
  | Set ((Var vi', NoOffset), e, _) when vi.vid = vi'.vid -> return e
  | Set ( lv, e, _ ) -> E.log "lv:%a\ne:%a\n" d_plainlval lv d_plainexp e;mzero
  | _ -> mzero


let matchBinOpOf vi = function
  | BinOp(op, e, e2, _) -> 
    mplus (unViExp e >>= fun vi' ->
      guard (vi'.vid=vi.vid) >> 
      return (e2))
      (unViExp e2 >>= fun vi' ->
      guard (vi'.vid=vi.vid) >> 
      return (e))
  | e -> E.log "matchBinOpOf %a\n" d_plainexp e;mzero 

let rec parseExp vi exp = match exp with
  | BinOp (_,_,_,_) -> matchBinOpOf vi exp
  | UnOp(_,e,_) -> parseExp vi e
  | CastE(_,e) -> parseExp vi e
  | _ -> None

let isSelfAssign = function
  | Set ((Var vi', NoOffset), Lval (Var vi,NoOffset), _) -> vi.vid = vi'.vid
  | _ -> false 

let instrsOfStmt = function
  | { skind = Instr is } -> is
  | _ -> []
let findStride stmts = 
  (*TODO: forbid any operation on index*)
  concatMap findIncr @$ concatMap instrsOfStmt stmts
(*  mplus (mapFindFirst (matchIncrOf vi) (rev is)) (mapFindFirst (matchIncrOf vi) is)*)

let getLoopStructOneStmt = function
  | {skind = Loop( { bstmts = {skind = If(cmp , _, _, _)}:: blkTail }, _, _, _)} ->
        E.log "cmp expr: %a\n" d_plainexp cmp;
        msumRmap (rev @$ findStride blkTail) @$ fun (vi,stride) ->
            mplus (unViExp cmp >>= fun vi -> return zero) 
                (parseExp vi cmp) >>= fun (be) ->
                return { vi = vi; init = None; bound = be; stride = stride; body = blkTail }
  | _ -> mzero


let getLoopStruct =
  let findInit vi insts = findFirst (matchAssignOf vi) (rev insts) in
  function
  | [{ skind = Instr insts };s2] ->
        getLoopStructOneStmt s2 >>= fun ls ->
              return {ls with init = mplus ls.init (findInit ls.vi insts)}
(*              return @$                                                             *)
(*                if equalExp ls.init (viExp ls.vi) then {ls with init = init} else ls*)
  | [_;s]
  | [s] -> getLoopStructOneStmt s
  | _ -> mzero

let addStmtsToGlobal stmts gl = match gl with
  | GFun (fundec, l) ->
    fundec.sbody.bstmts <- stmts @ fundec.sbody.bstmts;
    gl
  | _ -> gl

(** A visitor that yeilds [num] instructions to caller, 
and replaces the matched instructions with received when [transform] returns Some x.*)
class lidoStream = object(self) inherit nopCilVisitor
    val currentFundec = ref None
    val stmtsAddToFunctionStart : stmt list ref = ref []
    method vglob gl = match gl with
      GFun (fundec, l) -> 
        currentFundec := Some fundec;
        ChangeDoChildrenPost([gl], map (addStmtsToGlobal !stmtsAddToFunctionStart))
    | _ -> SkipChildren   
end   
class instructionStream 
    num
    (transform: fundec -> instr list-> stmt list option) 
  = object(self) inherit lidoStream
  method vstmt s = 
    let changed = ref false in
    match s.skind with Instr insts -> begin
    let rec proc acc stack = function
      [] -> List.rev acc
      | post ->
        match transform (fromSome !currentFundec) (take num post) with
          Some res -> 
            changed:=true;
            proc (res@mkStmtInstrs (List.rev stack)@acc) [] (drop num post)
      | None -> proc acc (List.hd post::stack) (List.tl post)
    in
    let insts' = proc [] [] insts in
    if !changed then ChangeTo(mkBlockStmt insts') else DoChildren
    end
    |_->DoChildren
end

class statementStream 
    num
    (transform: fundec -> stmt list-> stmt list option) 
  = object(self) inherit lidoStream
    method vblock blk = 
        let changed = ref false in
        let rec loop stk = function 
          [] -> List.rev stk
        | (x::xs) as l -> begin
            match transform (fromSome !currentFundec) (take num l) with 
                Some x' -> changed:=true;loop (x'@stk) (drop num l)
                | None -> loop (x::stk) xs
        end in
        let stmts = loop [] blk.bstmts in
        if !changed then ChangeTo {blk with bstmts = stmts} else DoChildren                      
end        

class loopStream (transform: fundec option -> loop_struct -> stmt list -> stmt list option) 
    = object(self) inherit lidoStream
    method vblock blk =
      let changed = ref false in
      let rec loop stk = function
        | [] -> rev stk
        | x::xs -> begin
          match 
            getLoopStruct (take 1 stk @ [x]) >>= fun ls ->                 
            transform !currentFundec ls (take 1 stk @ [x])
          with
            | Some res ->
                changed := true;
                loop (res@drop 1 stk) xs
            | None -> loop (x::stk) xs
          end in
      let stmts = loop [] blk.bstmts in
      if !changed then ChangeTo {blk with bstmts = stmts} else DoChildren 
end

let iterLoops f file = 
  visitCilFile (new loopStream f) file

let dumpLoops file =
    iterLoops (fun _ ls _ -> dump_loop_struct ls;None) file;
    file
          
let extractCnt = function 
  [Call(_,Lval(Var v,NoOffset),exps,_);
    Set(lv2,_,_)] -> begin
        let e = List.hd exps in
        match v.vname with "calloc" -> Some e
    | "malloc" | "__builtin_alloca" -> 
      get_pointed_type (typeOfLval lv2) 1 >>= fun t -> 
        Some (divExpr e (SizeOf t))
    | _ -> None
  end
  | _ -> None 

(** symbolic eval assuming x-x = zero *)
class symbolicEvalVisitor = object
  inherit nopCilVisitor
  method vexpr e =
    let cancel = function
      | BinOp(MinusA, a, b, _) when equalExp a b -> zero
      | x -> x in
    match e with
    | BinOp(op, a, b, ty) -> ChangeDoChildrenPost (e, cancel)
    | _ -> DoChildren
end
let rec symbolicEval e = visitCilExpr (new symbolicEvalVisitor) (constFold true e)

(** replace expression of value of [vi] by expression [exp] *)
class replaceViExpVisitor vi exp = object
  inherit nopCilVisitor
  method vexpr e = match e with
    | Lval (Var vi',NoOffset) when vi'.vid = vi.vid -> ChangeTo exp
    | _ -> DoChildren
end

(** replace expression of value of [vi] by expression [exp] *)
class decIndexVisitor vi exp = object
  inherit nopCilVisitor
  method vexpr e = match e with
    | Lval (Var vi',NoOffset) when vi'.vid = vi.vid -> 
      ChangeTo (BinOp(MinusA,Lval (Var vi',NoOffset),exp,typeOf exp))
    | BinOp(MinusA,lv,exp2,typ) -> begin
      match (evalExpr exp >>= fun i ->
        evalExpr exp2 >>= fun i2 ->
          return (Int64.to_int @$ Int64.add i2 i)) with
            | None -> DoChildren
            | Some i -> ChangeTo (BinOp(MinusA,lv,integer i,typ))
     end
    | _ -> DoChildren
end

let decIndex vi exp = visitCilStmt (new decIndexVisitor vi exp)

class replaceViLvalVisitor vi lv = object
  inherit nopCilVisitor
  method vlval = function
    | Var vi',NoOffset -> if vi'.vid = vi.vid then ChangeTo lv else DoChildren
    | _ -> DoChildren
end

class replaceViVisitor old_vi new_vi = object(self) inherit nopCilVisitor
    method vvrbl vi = if vi = old_vi then ChangeTo new_vi else DoChildren
end

class simpExpVisitor = object
    inherit nopCilVisitor
    method vexpr = function
      | e -> DoChildren
(*      | BinOp (op,BinOp(op',e',e2') as e,e2,_)   *)
(*      | BinOp (op,e,BinOp(op',e',e2') as e2,_) ->*)     
end

(** unroll a loop n times *)
let unroll ?tailAtFront:(tailAtFront = true) n (ls: loop_struct) : stmt list = 
	let unrollMultiple n body : stmt list =
	  let next idx stride stmt = 
	    visitCilStmt (new replaceViExpVisitor idx (addExpr (viExp idx) stride)) stmt in
	  List.concat *@transpose @$ map (takeNIterate n (next ls.vi ls.stride)) body in
  let nExp = integer n in
  let unrolledBody = unrollMultiple n ls.body in
  if tailAtFront then
    let remainder = (modExpr ls.bound nExp) in
    expand_loop_struct {ls with bound = remainder} @
    expand_loop_struct {ls with init = Some remainder; stride = multExpr ls.stride nExp;
        body = unrolledBody }
  else
    let multiple = multExpr (divExpr ls.bound nExp) nExp in
    expand_loop_struct {ls with bound = multiple; stride = multExpr ls.stride nExp;
        body = unrolledBody } @
    expand_loop_struct {ls with init = Some multiple}
    
let stridedBy idx stride instr instr2 =
  if stride >=0 then (*TODO*) false else
    let stmt = decIndex idx (integer (-stride)) @$ mkStmtOneInstr instr in
    let stmt2 = mkStmtOneInstr instr2 in
    E.log "ia.(i-1) %a\n ia.(i) %a\n" d_plainstmt stmt d_plainstmt stmt2;
  equalStmt stmt stmt2

let roll n (ls : loop_struct) =
  evalExpr ls.stride >>= fun stride ->
  let is = List.rev @$ List.tl @$ List.rev @$ concatMap instrsOfStmt ls.body in
  divMaybe (length is) n >>= fun len ->
  divMaybe (Int64.to_int stride) n >>= fun d ->
  (* only handle simple case *)
  E.log "length is = %d, n = %d, d= %d\n" (length is) n d;
  guard (length is = n) >>
  let check is =
    let ia = Array.of_list is in
    let res = ref true in
    for i =1 to Array.length ia -1 do
(*      E.log "ia.(i-1) %a\n ia.(i) %a\n" d_plaininstr ia.(i-1) d_plaininstr ia.(i);*)
        res := !res &&  stridedBy ls.vi d ia.(i-1) ia.(i)
      done;
      !res
    in
  let r = check is in
  E.log "check = %b\n" r;
  return @$ mkStmtInstrs @$ take 1 is
(*  divMaybe (length is) n >>= fun len ->                                               *)
(*  divMaybe (Int64.to_int stride) n >>= fun d ->                                       *)
(*    let l = transpose (tile len is) in                                                *)
(*    guard (all isTrue @$ map (all isTrue*@deltaBy (stridedBy ls.vi (integer d))) l) >>*)
(*    return @$ mkStmtInstrs @$ take len is                                             *)

let fullyRoll (ls : loop_struct) =
  evalExpr ls.stride >>= fun stride ->
    roll (abs @$ Int64.to_int stride) ls

let firstInstr = function
  | {skind = Instr is} -> return @$ hd is
  | _ -> mzero

let lhs = function
  | Set(lv,_,_) -> Some lv
  | Call(lvo,_,_,_) -> lvo
  | _ -> None

exception FinderFound
class viFinderClass vi = object(self)
  inherit nopCilVisitor      
  method vvrbl vi' =
    if vi.vid = vi'.vid then raise FinderFound else DoChildren
end
let finderFound f=
  try
    ignore (f ());false
  with FinderFound -> true
let exp_has_vi e vi = finderFound (fun _ -> visitCilExpr (new viFinderClass vi) e)
let stm_has_vi e vi = finderFound (fun _ -> visitCilStmt (new viFinderClass vi) e)

let showLocation l = Printf.sprintf "%s %d %d" l.file l.line l.byte

let rec getLocationInstr = function
  | Set(_,_,l) -> l
  | Call(_,_,_,l) -> l
  | Asm(_,_,_,_,_,l) -> l
and getLocationStmt = function
  | {skind = sk} -> getLocationStmtkind sk
and getLocationStmtkind = function
  | Instr il -> getLocationInstr (hd il)
  | Block blk -> getLocationBlock blk 
  | Return(_,l)
  | Goto(_,l)
  | Break l
  | Continue l
  | If(_,_,_,l)
  | Switch(_,_,_,l)
  | Loop(_,l,_,_)
  | TryFinally(_,_,l)
  | TryExcept(_,_,_,l) -> l
and getLocationBlock blk = getLocationStmt @$ hd blk.bstmts 
and getLocationFundec f = getLocationBlock f.sbody 

let mkFunctionVarinfo name = makeGlobalVar name (TFun(TVoid [],None,false,[]))

class insertAtEndVisitor fundec stmt' = object inherit nopCilVisitor
  method vstmt stmt = match stmt.skind with
    | Return (Some e, loc) ->
        let stmts =
          let vi = makeTempVar fundec (typeOf e) in
          [mkStmtOneInstr (Set(var vi, e, loc)); 
          stmt'; 
          mkStmt @$ Return (Some (viExp vi), loc)] in
        ChangeTo(mkBlockStmt stmts)
    | _ -> DoChildren
end
let insertAtEnd stmt fundec =
  let fundec' = visitCilFunction (new insertAtEndVisitor fundec stmt) fundec in
  fundec.sbody.bstmts <- fundec'.sbody.bstmts @ [stmt]
  
let dummyInitinfo = {Cil.init = None}  

class functionsVisitor f : cilVisitor =
  object(self) inherit nopCilVisitor
  method vfunc fundec =
    f fundec;
    SkipChildren
  end 
  
class nullAdderClass all_stmts = object(self)
  inherit nopCilVisitor
  method vstmt s =
    all_stmts := s :: (!all_stmts);
    DoChildren
end

let allStmtsFun (f:fundec) =
  let all_stmts = ref [] in
  ignore (visitCilFunction (new nullAdderClass all_stmts) f);
  !all_stmts
  
let allStmtsFile (fil:file) =
  let all_stmts = ref [] in
  visitCilFileSameGlobals (new nullAdderClass all_stmts) fil;
  !all_stmts

let iterFunctions f (fil:file) =
  visitCilFileSameGlobals (new functionsVisitor f) fil 

let getFunctions (fil:file) =
  let all = ref [] in
  visitCilFileSameGlobals (new functionsVisitor (
    fun fundec -> all := fundec :: !all)) fil;
  !all 

(*let rec get_pointed_type typ i = if i=0 then unrollType typ                       *)
(*    else match unrollType typ with TPtr(typ2,_) -> get_pointed_type typ2 (pred i) *)
(*        | x ->E.log "typ: %a\n" d_plaintype x;assert false                        *)
let is_pointer_type_of typ maybe_pointer_type = 
    match typeSig maybe_pointer_type with TSPtr (ts,_) ->typeSig typ = ts |_-> false
let is_pointer_of typ lval = is_pointer_type_of typ (typeOfLval lval)
let typeSigOfLval x = typeSig (typeOfLval x)
let varinfo_and_level_of_lval =   
  let rec varinfo_and_level_of_lval' acc acc_indices = function
    | Var v2,Index (idx,off) -> 
      varinfo_and_level_of_lval' (succ acc) (idx::acc_indices) (Var v2, off)
    | Var v2,_ -> v2,acc,acc_indices
    | Mem(BinOp(_,Lval lv,idx,_)),_ -> varinfo_and_level_of_lval' (succ acc) (idx::acc_indices) lv
    | Mem(Lval lv),_ -> varinfo_and_level_of_lval' (succ acc) acc_indices lv
    | x-> E.log "lval %a\n" d_plainlval x;failwith "varinfo_of_lval" in varinfo_and_level_of_lval' 0 []

class cleanBlockModifier total_changed =
object(self) inherit nopCilVisitor (*flatten nested blocks*)
  method vblock blk =
    let changed = ref false in
    let bstmts' = List.flatten (List.map (function 
      | { labels = []; skind = Block blk2 } when blk2.battrs =[] ->
        changed := true;
        blk2.bstmts
      | x -> [x]) 
      blk.bstmts) in
    if !changed then (
      E.log "elim a block\n"; 
      total_changed:= true; 
      blk.bstmts <- bstmts'
     );
    DoChildren
end

let till_nochange_clean_block_file (f:file) =
  let changed = ref true in
  while !changed do
    changed := false;
    f.globals <- List.flatten (List.map
          (visitCilGlobal (new cleanBlockModifier changed)) f.globals);
  done

let till_nochange_clean_block_fun (f:fundec) =
  let changed = ref true in
  let res = ref f in
  while !changed do
    changed := false;
    res := visitCilFunction (new cleanBlockModifier changed) !res
  done;
  !res


class globlReadVisitor reads = object (self) inherit nopCilVisitor
    method vlval lv =
    begin
        try
              let vi,n,es = varinfo_and_level_of_lval lv in
(*        E.log "globlReadWriteVisitor: %s %d\n" vi.vname n;*)
              if vi.vglob then Linda.addRefList (vi.vname,n) reads
        with _ -> ()
    end;
      DoChildren
end

let computeGlobalLiveness (fil:file) =
  IH.clear Liveness.LiveFlow.stmtStartData;
  Usedef.onlyNoOffsetsAreDefs := false;
  let all_stmts = allStmtsFile fil in
  List.iter (fun s -> IH.add Liveness.LiveFlow.stmtStartData s.sid VS.empty) all_stmts;
  try
    Liveness.L.compute all_stmts
  with E.Error -> begin
    E.s "Bug in Global Liveness compute"
  end

class arrReadWriteVisitor onlyGlobals reads writes = object (self) inherit nopCilVisitor
  method vinst = function
    | Set (lv, exp, _) -> (
        let vi, n, es = varinfo_and_level_of_lval lv in
        let subReads, subWrites = ref [], ref [] in
        List.iter (fun e -> 
          ignore (visitCilExpr (new arrReadWriteVisitor onlyGlobals subReads subWrites) e))
            (exp::es);
        assert (!subWrites == []);
        reads := !subReads @ !reads;
        if (n > 0) then (
(*            E.log "globlArrReadWriteVisitor: Write %s %d\n" vi.vname n;*)
            if onlyGlobals && vi.vglob || not onlyGlobals then 
              Linda.addRefList (vi, n) writes
          )
        );
        SkipChildren
    | _ -> SkipChildren
  method vlval lv =
    let vi, n, _ = varinfo_and_level_of_lval lv in
    if (n > 0) then (
(*        E.log "globlArrReadWriteVisitor: Read %s %d\n" vi.vname n;*)
        if onlyGlobals && vi.vglob || not onlyGlobals then 
          Linda.addRefList (vi, n) reads
     );
    SkipChildren
end

class arrReadWritePatternVisitor onlyGlobals reads writes = object (self) inherit nopCilVisitor
  method vinst inst =
(*    E.log "%a\n" d_plaininstr inst; *)
    match inst with
    | Set (lv, exp, _) -> (
        let vi, n, es = varinfo_and_level_of_lval lv in
        let subReads, subWrites = ref [], ref [] in
        List.iter (fun e -> 
          ignore (visitCilExpr (new arrReadWritePatternVisitor onlyGlobals subReads subWrites) e))
            (exp::es);
        assert (!subWrites == []);
        reads := !subReads @ !reads;
        if (n > 0) then (
(*            E.log "arrReadWritePatternVisitor: Write %s %d\n" vi.vname n;*)
            if onlyGlobals && vi.vglob || not onlyGlobals then 
              Linda.addRefList (vi, es) writes
          )
        );
        SkipChildren
    | _ -> SkipChildren
  method vlval lv =
    let vi, n, es = varinfo_and_level_of_lval lv in
    if (n > 0) then (
(*        E.log "arrReadWritePatternVisitor: Read %s %d\n" vi.vname n;*)
        if onlyGlobals && vi.vglob || not onlyGlobals then 
          Linda.addRefList (vi, es) reads
     );
    SkipChildren
end

let arrReadWritePatternDeepStmt stmt =
    let reads, writes = ref [], ref [] in
    ignore (visitCilStmt (new arrReadWritePatternVisitor false reads writes) stmt);
    !reads, !writes

let arrReadWriteDeepStmt stmt =
    let reads, writes = ref [], ref [] in
    ignore (visitCilStmt (new arrReadWriteVisitor false reads writes) stmt);
    !reads, !writes

let globlArrReadWrite (fil:file) =
  let reads, writes = ref [], ref [] in
  visitCilFileSameGlobals (new arrReadWriteVisitor true reads writes) fil;
  !reads,!writes

module type USEDEF = sig
  val computeUseDefStmt : stmt -> VS.t * VS.t
  val computeUseDefInstr : instr -> VS.t * VS.t
  end

module LiveFlow(UD: USEDEF) = struct
  let name = "Liveness"
  let debug = ref false
  type t = VS.t
  
  let pretty () vs =
    let fn = Liveness.min_print in
    fn () vs
  
  let stmtStartData = IH.create 32
  
  let funcExitData = VS.empty
  
  let combineStmtStartData (stm: stmt) ~(old: t) (now: t) =
    if not(VS.compare old now = 0)
    then Some(VS.union old now)
    else None
  
  let combineSuccessors = VS.union
  
  let doStmt stmt =
    if !debug then ignore(E.log "looking at: %a\n" d_stmt stmt);
    match stmt.succs with
      [] -> let u, d = UD.computeUseDefStmt stmt in
        if !debug then ignore(E.log "doStmt: no succs %d\n" stmt.sid);
        DF.Done u
    | _ ->
        let handle_stm vs = match stmt.skind with
            Instr _ -> vs
          | _ -> let u, d = UD.computeUseDefStmt stmt in
              VS.union u (VS.diff vs d)
        in
        DF.Post handle_stm
  
  let doInstr i vs =
    let transform vs' =
      let u, d = UD.computeUseDefInstr i in
      VS.union u (VS.diff vs' d)
    in
    DF.Post transform
  
  let filterStmt stm1 stm2 = true
  
end

module ArrayUsedef = struct
  let extract ls =
    let s = ref VS.empty in
    List.iter (fun (a, _) -> s := VS.add a !s) ls;
    !s

  let computeUseDefInstr instr =
    let reads, writes = ref [], ref [] in
    ignore (visitCilInstr (new arrReadWriteVisitor true reads writes) instr);
    extract !reads, extract !writes

  let rec computeUseDefStmt stmt =
    let reads, writes = ref [], ref [] in
    let ve e = ignore (visitCilExpr (new arrReadWriteVisitor true reads writes) e) in 
    (match stmt.skind with
    | Return (None, _) -> ()
    | Return (Some e, _) -> ve e
    | If (e, _, _, _) -> ve e
    | Break _ | Goto _ | Continue _ -> ()
    | Loop (_, _, _, _) -> ()
    | Switch (e, _, _, _) -> ve e
    | Instr il -> 
      let r,w = List.fold_left (
        fun (au,ad) i -> 
          let u,d = computeUseDefInstr i in
          (VS.union u (VS.diff au d),VS.union d ad)
        ) (VS.empty,VS.empty) (List.rev il) in
      VS.iter (fun e -> reads := (e,1) :: !reads) r; (* TODO: WAR*)
      VS.iter (fun e -> writes := (e,1) :: !writes) w (* TODO: WAR*)
    | TryExcept _ | TryFinally _ -> ()
    | Block blk ->
      let r,w = List.fold_left (
        fun (au,ad) stmt -> 
          let u,d = computeUseDefStmt stmt in
          (VS.union u (VS.diff au d),VS.union d ad)
        ) (VS.empty,VS.empty) (List.rev blk.bstmts) in
      VS.iter (fun e -> reads := (e,1) :: !reads) r; (* TODO: WAR*)
      VS.iter (fun e -> writes := (e,1) :: !writes) w (* TODO: WAR*)
(*        List.iter (fun i ->                                                              *)
(*          ignore (visitCilStmt (new globlArrReadWriteVisitor reads writes) i)) blk.bstmts*)
      );
    extract !reads, extract !writes
    
  let computeDeepUseDefStmt stmt =
    let reads, writes = ref [], ref [] in
    ignore (visitCilStmt (new arrReadWriteVisitor true reads writes) stmt);
    extract !reads, extract !writes


end

module ArrayLiveness = struct
  module L = LiveFlow(ArrayUsedef)
  module AL = DF.BackwardsDataFlow(L)

	let computeLiveness fdec =
	  IH.clear L.stmtStartData;
	  let all_stmts = allStmtsFun fdec in
    List.iter (fun s -> IH.add L.stmtStartData s.sid VS.empty) all_stmts;
	  try
	    AL.compute all_stmts
	  with E.Error -> begin
	    ignore(E.log "Liveness failed on function:\n %a\n" d_global (GFun(fdec,locUnknown)));
	    E.s "Bug in Liveness compute"
	  end    

  let computeLivenessFuns (fs: fundec list) =
    IH.clear L.stmtStartData;
    let all_stmts = List.flatten (List.map allStmtsFun fs) in
    List.iter (fun s -> IH.add L.stmtStartData s.sid VS.empty) all_stmts;
      try
        AL.compute all_stmts
      with E.Error -> begin
        E.log "Liveness failed\n";
        E.s "Bug in Liveness compute"
      end    
        
	let computeGlobalLiveness (fil:file) =
	  IH.clear L.stmtStartData;
	  let all_stmts = allStmtsFile fil in
	  List.iter (fun s -> IH.add L.stmtStartData s.sid VS.empty) all_stmts;
	  try
	    AL.compute all_stmts
	  with E.Error -> begin
	    E.s "Bug in Global Liveness compute"
	  end

  let getStmLiveSet stm =
    try IH.find L.stmtStartData stm.sid
    with Not_found -> VS.empty
end

class oneInstrModifier = object
  inherit nopCilVisitor 
  method vstmt s =
    match s.skind with
    | Instr(il) -> begin
            if (List.length il > 1) then 
              let block = mkBlock (List.map mkStmtOneInstr il) in
              s.skind <- Block block;
              ChangeTo(s)
            else
              SkipChildren
      end
    | _ -> DoChildren
end 

let doOneInstrFun (f:fundec) =
  visitCilFunction (new oneInstrModifier) f

(* global cfg *)
module GlobalCFG = struct
    
    (* must be called before entryStmtVisitor *)
    class exitStmtVisitor 
        fname (exitStmtTable : (string,stmt) Hashtbl.t) : cilVisitor = 
      object inherit nopCilVisitor
      method vstmt stm = (match stm.succs with
        | [] -> Hashtbl.add exitStmtTable fname stm
        | _ -> ());
        DoChildren  
    end
    
    let getExitStmt exitStmtTable fname = 
      try Hashtbl.find_all exitStmtTable fname with Not_found -> []
    
    class entryStmtVisitor (entryStmtTable : (string,stmt list) Hashtbl.t) : cilVisitor = 
      object inherit nopCilVisitor
      method vfunc func =
        let so = match func.sbody.bstmts with
          | [] -> []
          | x::xs -> [x] in
         Hashtbl.replace entryStmtTable func.svar.vname so;
        SkipChildren
    end
    
    let getEntryStmt entryStmtTable fname=
      try Hashtbl.find entryStmtTable fname with Not_found -> []
    
    let addListHashtbl h k ls =
      Hashtbl.replace h k ((try Hashtbl.find h k with Not_found -> [])@ls)
    
    class ipaFlowModifier entryStmtTable exitStmtTable
        (newSuccTable:(int,stmt list) Hashtbl.t)
        (newPredTable:(int,stmt list) Hashtbl.t) = 
      object inherit nopCilVisitor
    (*    method vinst = function inst              *)
    (*        | Call (_,Lval(Var(vi),NoOffset),_,_) *)
        method vstmt stmt =
          let getCall = function
            |  Call (_,Lval(Var(vi),NoOffset),_,_) -> [vi.vname]
            | _ -> [] in
          let callees = match stmt.skind with
              | Instr instrs -> List.flatten (List.map getCall instrs)
              | _ -> [] in
          let new_succs = List.flatten (List.map (getEntryStmt entryStmtTable) callees) in
    (*      E.log "new_succs: %d\n" (List.length new_succs);*)
          (match new_succs with
            | [] -> ()
           | _ -> addListHashtbl newSuccTable stmt.sid new_succs);
          List.iter (fun ce -> 
            List.iter (fun entryStmt -> addListHashtbl newPredTable entryStmt.sid [stmt]) 
                (getEntryStmt entryStmtTable ce)) callees;
          let exits = List.flatten (List.map (getExitStmt exitStmtTable) callees) in
    (*      E.log "exits:%d\n" (List.length exits);*)
          let link xs ys newSuccTable newPredTable =
            List.iter (fun y -> List.iter (fun x ->
                addListHashtbl newSuccTable x.sid [y];
                addListHashtbl newPredTable y.sid [x];
              ) xs) ys in
          link exits stmt.succs newSuccTable newPredTable;
          DoChildren
    end
    
    class overideCFGModifier newSuccTable newPredTable = object inherit nopCilVisitor
        method vstmt stmt =
          stmt.succs <- stmt.succs @ (try Hashtbl.find newSuccTable stmt.sid with _ -> []);
          stmt.preds <- stmt.preds @ (try Hashtbl.find newPredTable stmt.sid with _ -> []);
          DoChildren
    end
    
    class debugPrintStmtVisitor = object inherit nopCilVisitor
        method vstmt stmt =
          E.log "%d " stmt.sid;
          DoChildren
    end
    
    let debugPrintStmts (f:file) = 
      E.log "debugPrintStmts\n";
      iterFunctions (fun func ->
        E.log "%s:" func.svar.vname; 
        ignore (visitCilFunction (new debugPrintStmtVisitor) func);
        E.log "\n") f
    
    let debugPrintHashtbl str h =
      E.log "%s:" (str^"\n");
      Hashtbl.iter (fun k v ->
        E.log "%d -> " k;
        List.iter (fun s -> E.log "%d " s.sid) v;
        E.log "\n") h

    let computeGlobalCFG (fs : fundec list) =
      List.iter Cfg.clearCFGinfo fs;
      List.iter (fun f ->
        let n = Cfg.cfgFun f in
        Cfg.start_id := n + !Cfg.start_id) fs;
      let exitStmtTable = Hashtbl.create 3 in
      List.iter (fun func -> 
        ignore (visitCilFunction (
          new exitStmtVisitor func.svar.vname exitStmtTable) func)) fs;
      let entryStmtTable = Hashtbl.create 3 in
      List.iter (fun func ->
        ignore (visitCilFunction (new entryStmtVisitor entryStmtTable) func)) fs;
      let newSuccTable,newPredTable = Hashtbl.create 3,Hashtbl.create 3 in
      List.map (fun f ->
        let f' = visitCilFunction (new ipaFlowModifier entryStmtTable exitStmtTable
            newSuccTable newPredTable) f in
        visitCilFunction (new overideCFGModifier newSuccTable newPredTable) f') fs
    
    let computeGlobalFileCFG (f : file) =
      Cfg.clearFileCFG f;
      Cfg.computeFileCFG f;
    (*  debugPrintStmts f;*)
      let exitStmtTable = Hashtbl.create 3 in
      iterFunctions (fun func -> 
        visitCilFunction (new exitStmtVisitor func.svar.vname exitStmtTable) func) f;
      let entryStmtTable = Hashtbl.create 3 in
      visitCilFileSameGlobals (new entryStmtVisitor entryStmtTable) f;
    (*  Hashtbl.iter (fun k v -> E.log "entryStmtTable: %s " k;*)
    (*    List.iter (fun s -> E.log "%d " s.sid) v;            *)
    (*    E.log "\n") entryStmtTable;                          *)
      let newSuccTable,newPredTable = Hashtbl.create 3,Hashtbl.create 3 in
      visitCilFileSameGlobals (new ipaFlowModifier entryStmtTable exitStmtTable
        newSuccTable newPredTable) f;
    (*  debugPrintHashtbl "newSuccTable" newSuccTable;*)
    (*  debugPrintHashtbl "newPredTable" newPredTable;*)
      visitCilFileSameGlobals (new overideCFGModifier newSuccTable newPredTable ) f
end

class allocLenVisitor allocLenSet = object (self) inherit nopCilVisitor
    method vinst inst = match inst with
      | Call (_, Lval(Var v,NoOffset),exps,_) 
        when List.mem v.vname ["malloc"] ->
          E.log "%a\n" d_plaininstr inst;
          List.iter (fun e -> 
            ignore (visitCilExpr (new allocLenVisitor allocLenSet) e)) exps;
          SkipChildren
      |  _ -> SkipChildren
    method vvrbl vi =
      if not (VS.mem vi !allocLenSet) && vi.vglob 
        then allocLenSet := VS.add vi !allocLenSet;
      SkipChildren
    method vexpr exp = match exp with
      | CastE (_,_) -> DoChildren 
      | BinOp(Mult,_,_,_) -> DoChildren
      | Lval _ -> DoChildren
      | _ -> SkipChildren
end


  
(*class cfgPruneModifier nonZeros changed = object(self)                    *)
(*  inherit lidoStream                                                      *)
(*  method vstmt stm = match stm.skind with                                 *)
(*    | Loop (blk,_,_,_) -> (match (                                        *)
(*      getLoopStructOneStmt stm >>= fun ls ->                              *)
(*        E.log "cfgPrune: %a\n" d_plainstmt stm;                           *)
(*        (match ls.bound with                                              *)
(*        | Lval(Var vi, NoOffset) when VS.mem vi nonZeros && ls.body!=[] ->*)
(*(*		      E.log "cfgPrune:\n";*)                                        *)
(*		      List.iter (E.log "%a\n" d_plainstmt) blk.bstmts;                *)
(*          changed := true;                                                *)
(*          Some (mkBlockStmt (List.tl blk.bstmts))                         *)
(*        | _ -> None)                                                      *)
(*      ) with                                                              *)
(*        | Some stm' -> ChangeTo stm'                                      *)
(*        | None -> DoChildren)                                             *)
(*    | _ -> DoChildren                                                     *)
(*                                                                          *)
(*end                                                                       *)

class cfgPruneModifier nonZeros changed = object(self)
  inherit nopCilVisitor
  method vstmt stm = match stm.skind with
    | Loop (blk,_,_,_) when blk.bstmts != [] ->
      let x = List.hd blk.bstmts in
      if (VS.exists (stm_has_vi x) nonZeros) then (  
(*          E.log "cfgPrune:\n";                            *)
(*          List.iter (E.log "%a\n" d_plainstmt) blk.bstmts;*)
          changed := true;
          ChangeTo (mkBlockStmt (List.tl blk.bstmts))    
      ) else DoChildren
    | _ -> DoChildren

end

let cfgPrune nonZeros (f:fundec) =
  let changed = ref true in
  let res = ref f in
  while !changed do
    changed := false;
    res := visitCilFunction (new cfgPruneModifier nonZeros changed) !res
  done;
  !res

let set_of_list l =
  let r = ref VS.empty in
  List.iter (fun e -> r := VS.add e !r) l;
  !r