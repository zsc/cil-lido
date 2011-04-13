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

let debug = ref false

let optimizeSimpleArray = ref false
let unionToStruct = ref false
let unionToStructUnionFieldNames = ref None
let heuristicFrequency = ref false
let printCabs = ref false
let allocaToMalloc = ref false
    
class nonStaticGlobals nonstatics = object
    inherit nopCabsVisitor
    method vdef def= match def with 
      | DECDEF ((spec,inl),_) when not (mem (SpecStorage STATIC) spec) ->
        iter (fun s -> nonstatics := s:: !nonstatics) 
            (map (fun ((x,_,_,_),_) -> x) inl);
        SkipChildren
      | _ -> SkipChildren
end

(** Recognition of constant array and 'id' arrays and simplification *)

type simpleArrayInfo = SAConst of int (*constant array*) 
  | SAId (* array value always equal to index *)
  | SATop (* content of array is complex *)
  | SABot (* nothing known about array*)
let string_of_simpleArrayInfo = function
  | SAConst i -> "SAConst "^string_of_int i
  | SAId -> "SAId"
  | SATop -> "SATop"
  | SABot -> "SABot"
let arraySimpleInfoTable : (string,simpleArrayInfo) H.t = H.create 31 
let mergeSimpleArrayInfo i i2 = match i,i2 with  
  SABot,i'
  | i', SABot -> i'
  | SATop,_
  | _,SATop -> SATop
  | SAConst c,SAConst c2 -> if c=c2 then SAConst c else SATop
  | x,x2 when x=x2 -> x  
  | _ -> SATop

let getPattern idx = function 
  | UNARY(MINUS,CONSTANT (CONST_INT s)) -> SAConst (-(int_of_string s))
  | CONSTANT (CONST_INT s)  -> SAConst (int_of_string s)
  | VARIABLE _ as v when v=idx -> SAId
  | x -> if !debug then E.log "failed getPattern for %s\n" (show_plain_cabs_expression x);SATop
let unGetPattern idx = function SAConst c -> Some (integer c)
  | SAId -> Some idx
  | _ -> None

class simpleArrayFinder = object
    inherit nopCabsVisitor
    method vexpr = function
      (*We require there are no type casting here, because in transMemcpy we rely on the fact that*)
      (* array is visited with its natural type.*)
      | BINARY(ASSIGN,INDEX(VARIABLE arr,i),e) ->
        if !debug then E.log "writing array %s\n" arr;
        ignore (
          let oldpat = maybe SABot id (maybefind Hashtbl.find arraySimpleInfoTable arr) in
          let pat = getPattern i e in
          let v = mergeSimpleArrayInfo oldpat pat in
          if !debug then E.log "update for %s in table with %s merging %s with %s\n" arr (string_of_simpleArrayInfo v)
            (string_of_simpleArrayInfo oldpat) (string_of_simpleArrayInfo pat);   
          Some (H.replace arraySimpleInfoTable arr v)
        );
        SkipChildren
      | _ -> SkipChildren
end

class transMemcpy nonstatics = object
  inherit nopCabsVisitor
  method vstmt stmt = match stmt with
    | COMPUTATION(CALL(VARIABLE v,[(*VARIABLE dstName as*) origDst;src;origLen]),loc)
        when v="memcpy" && Hashtbl.mem arraySimpleInfoTable (nameOfExp src)
        && not (mem (nameOfExp src) nonstatics) ->
      let srcName = nameOfExp src in
      let dst = stripCast origDst in
      let len = extractLength origLen in
      let idxName = newTemp () in
      let idx = VARIABLE idxName in
      let pat = Hashtbl.find arraySimpleInfoTable srcName in
      if !debug then E.log "%s\n" (show_plain_cabs_expression dst);
      if !debug then E.log "%s\n" (show_plain_cabs_expression len);
      if !debug then E.log "Invoke transMemcpy for %s with pattern %s\n" srcName (string_of_simpleArrayInfo pat);
      (match unGetPattern idx pat with
        | Some e2 ->
          let stmt = assign (index dst idx) e2 loc in  
          let loop = mkLoop idx (integer 0) len stmt loc in 
          ChangeTo [mkBlockStmt [declare_int idxName loc;loop] loc]
        | None -> DoChildren
      )
    | _ -> DoChildren
end

let simplifyArrayTrans cabs =
  let nonstatics = ref [] in
  ignore (visitCabsFile (new nonStaticGlobals nonstatics) cabs);
  cabs |> visitCabsFile (new simpleArrayFinder)
  |> guardTrans !optimizeSimpleArray (visitCabsFile (new transMemcpy !nonstatics))
let field_group_names (_,l) = map (fun x -> let (y,_,_,cloc) = fst x in
    (Filename.chop_extension cloc.filename,y)) l 
class unionToStructVisitor cabs = object
    inherit nopCabsVisitor
    method vtypespec = function
      | Tunion (s,Some fl,al) ->
        if map field_group_names fl = maybe [] 
            (map (map (fun x -> (Filename.chop_extension (fst cabs),x)))) 
            !unionToStructUnionFieldNames  then begin 
(*            E.log "%s\n%s\n" (fst cabs) @$                                                     *)
(*                String.concat ";" (map (String.concat ",") (map field_group_names fl));        *)
            ChangeTo (Tstruct (s,Some fl,al))
          end
        else DoChildren
      | _ -> DoChildren
end

let unionToStructTrans cabs =
  cabs |> guardTrans !unionToStruct (visitCabsFile (new unionToStructVisitor cabs))
      
class heuristicFrequencyVisitor cabs = object
    inherit nopCabsVisitor
    method vblock blk =
      DoChildren
    method vstmt s = match s with
      | DOWHILE(_,_,cl)
      | WHILE(_,_,cl)
      | FOR(_,_,_,_,cl)
      | BREAK(cl)
      | CONTINUE(cl)
      | RETURN(_,cl)
      | SWITCH(_,_,cl)
      | CASE(_,_,cl)
      | CASERANGE(_,_,_,cl)
      | DEFAULT(_,cl)
      | LABEL(_,_,cl)
      | GOTO(_,cl)
      | COMPGOTO(_,cl)
      | IF(_,_,_,cl) ->
        E.log "%s" (show_cabsloc cl);
        DoChildren
      | _ -> DoChildren
end     
let heuristicFrequencyTrans cabs =
  guardTrans !heuristicFrequency (visitCabsFile (new heuristicFrequencyVisitor cabs)) cabs

class plainPrinter = object
    inherit nopCabsVisitor
    method vdef def = 
      E.log "%s" @$ show_plain_cabs_def def;
      SkipChildren
end

let plainPrint cabs = guardTrans !printCabs (visitCabsFile (new plainPrinter)) cabs        

let allocaBzeroTrans vars = function
 | [COMPUTATION(BINARY(ASSIGN,VARIABLE v,CAST(specDecl,SINGLE_INIT(CALL(VARIABLE call,[
      (BINARY(MUL,n,(TYPE_SIZEOF _ as size)) | BINARY(MUL,(TYPE_SIZEOF _ as size),n)) as len
      ])))),loc)
   ;COMPUTATION(CALL(VARIABLE call',[PAREN(CAST(_,SINGLE_INIT (VARIABLE v')));CONSTANT (CONST_INT zero);PAREN len']),loc')]
    when call = "__builtin_alloca" && len = len' && zero = "0" && v = v' ->
      addRefList v vars;
      return [assign (VARIABLE v) (CAST(specDecl,SINGLE_INIT(CALL(VARIABLE "calloc",[n;size])))) loc
      ;assign (VARIABLE (v^"__alloced_flag")) (integer 1) loc']
 | [COMPUTATION(BINARY(ASSIGN,VARIABLE v,CAST(specDecl,SINGLE_INIT(CALL(VARIABLE call,[len])))),loc)]
    when call = "__builtin_alloca" ->
      addRefList v vars;
      return [assign (VARIABLE v) (CAST(specDecl,SINGLE_INIT(CALL(VARIABLE "malloc",[len])))) loc]
 | _ -> mzero

let mkFreeStmts vars loc' = 
  mkBlockStmt (map 
    (fun v -> IF(VARIABLE (v ^ "__alloced_flag"),mkCall "free" [VARIABLE v] loc',NOP loc',loc')) vars) loc'
class transAlloca = object
  inherit nopCabsVisitor
  val vars = ref []
  val curSpec = ref None
  method vdef def = match def with
    | FUNDEF ((spec,_),blk,loc,loc') ->
      vars := [];
      curSpec := Some spec;
      let def' = visitCabsDefinition (new statementStream 2 (allocaBzeroTrans vars)) def in
      let allocFlagVars = map (fun s -> s ^ "__alloced_flag" ) !vars in
      let allocFlagVarsDef = declare_flags [SpecType Tint] allocFlagVars loc in
      let def'' =
        if null !vars then def' else 
        concatMap (visitCabsDefinition (new insertOnReturn (mkFreeStmts !vars))) def' in
      ChangeDoChildrenPost (def'',map (
        function FUNDEF (sn,blk,loc,loc') when not (null !vars) -> 
          FUNDEF(sn,{blk with bstmts = allocFlagVarsDef :: blk.bstmts},loc,loc') 
                | x -> x))
    | _ -> SkipChildren
(*  method vstmt stmt = match stmt with                                            *)
(*    | RETURN (e,loc) ->                                                          *)
(*      if null !vars then SkipChildren else                                       *)
(*        let freeStmts = mkFreeStmts !vars loc in                                 *)
(*        ChangeTo (match e with                                                   *)
(*          | NOTHING | VARIABLE _ -> freeStmts@[stmt]                             *)
(*          | _ ->                                                                 *)
(*		        let ret = "__retvar" in                                              *)
(*		        let retDef = declare_spec ret (fromSome !curSpec) loc in             *)
(*		        let compRet = assign (var ret) e loc in                              *)
(*	          [mkBlockStmt (retDef::compRet::freeStmts@[RETURN(var ret,loc)]) loc])*)
(*    | _ -> DoChildren                                                            *)
end

let allocaToMallocTrans cabs = 
  guardTrans !allocaToMalloc (visitCabsFile (new transAlloca)) cabs
