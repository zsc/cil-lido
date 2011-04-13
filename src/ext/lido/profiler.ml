open Linda
open Cil
open Lidoutil
module E = Errormsg
open Linda

let dumpFileName = "__counter_dump"

let dump fname f = 
  let oc = open_out fname in
  iterGlobals f (fun g ->
    match g with GFun(fd,_) ->
      Cfg.printCfgChannel oc fd
    | _ -> ());
    close_out oc      

class cfgVisitor f = object inherit nopCilVisitor
method vstmt stmt = match stmt.succs with
  | []
  | [_] -> DoChildren
  | l ->  
    ChangeDoChildrenPost (stmt, fun stmt -> f stmt)
    end

let profileFun counterVi stmt =
    let countBlock block =
      let stmt = 
        mkStmtOneInstr @$ 
                mkIncr PlusA (indexArray counterVi (integer stmt.sid)) one locUnknown in
      block.bstmts <- stmt :: block.bstmts;
      block in
        match stmt.skind with
          | If (e,tb,fb,loc) ->
          {stmt with skind = If (e,countBlock tb,countBlock fb,loc)}
        | _ -> stmt                      
(*class profiler id counterVi = object inherit nopCilVisitor                         *)
(*method vstmt stmt = match stmt.succs with                                          *)
(*  | []                                                                             *)
(*  | [_] -> DoChildren                                                              *)
(*  | l ->                                                                           *)
(*    let countBlock block =                                                         *)
(*      let stmt =                                                                   *)
(*        mkStmtOneInstr @$                                                          *)
(*                mkIncr PlusA (indexArray counterVi (integer !id)) one locUnknown in*)
(*      incr id;                                                                     *)
(*      block.bstmts <- stmt :: block.bstmts;                                        *)
(*      block in                                                                     *)
(*    ChangeDoChildrenPost (stmt,fun stmt ->                                         *)
(*	    match stmt.skind with                                                        *)
(*	      | If (e,tb,fb,loc) ->                                                      *)
(*          {stmt with skind = If (e,countBlock tb,fb,loc)}                          *)
(*        | _ -> stmt                                                                *)
(*          )                                                                        *)
(*end                                                                                *)


let mkDumper counterVi n =
  let fundec = makeFundec (makeGlobalVar "__dump_counters" (TFun(voidType,None,false,[]))) in
  let vi = makeTempVar fundec intType in
  let fp = makeTempVar fundec voidPtrType in
  fundec.sbody <- mkBlock @$ mkStmtOneInstr (mkFopen (var fp) dumpFileName "w") 
    :: mkForIncr vi zero n one [mkStmtOneInstr @$
    mkFPrint fp "%d\n" [Lval(indexArray counterVi (viExp vi))]];
  fundec

let profile f = 
  Cfg.clearFileCFG f;
  Cfg.computeFileCFG f;
(*  Cfg.printCfgFilename "" *)
(*  dump "out" f;*)
  let counterVi = makeGlobalVar "__counter" (TArray(intType,None,[])) in
(*  let id = ref 0 in*)
(*  visitCilFile (new profiler id counterVi) f;*)
  visitCilFile (new cfgVisitor (profileFun counterVi)) f;
  counterVi.vtype <- TArray(intType,Some (integer (!Cfg.numNodes)),[]);
  let dumper = mkDumper counterVi (integer !Cfg.numNodes) in
  f.globals <- GVar(counterVi,dummyInitinfo,locUnknown) ::GFun(dumper,locUnknown) :: f.globals;
  f.globals <- List.map (
    function GFun(fundec,loc) when fundec.svar.vname = "main" -> 
        insertAtEnd (mkStmtOneInstr @$ Call(None,viExp @$ dumper.svar,[],locUnknown)) fundec;
        GFun(fundec,loc)
    | g -> g) f.globals;
(*  print_endline @$ IntList.show !counters;*)
  f    

let optimizeFun counts stmt =
(*    let countBlock block =                                            *)
(*      let block' =                                                    *)
(*        if counts.(!id)=0 then {block with bstmts =[]} else block in  *)
(*(*      incr id;*)                                                    *)
(*      block' in                                                       *)
        match stmt.skind with
          | If (e,{bstmts = s::_},fb,loc) ->
            if counts.(s.sid)=0 then mkStmt @$ Block fb else stmt
          | If (e,tb,{bstmts = s::_},loc) ->
            if counts.(s.sid)=0 then mkStmt @$ Block tb else stmt
          | _ -> stmt      

let optimize f =
  let counts = Array.map int_of_string @$ Array.of_list @$ ExtString.lines @$ ExtUnix.readFile dumpFileName in 
  Cfg.clearFileCFG f;
  Cfg.computeFileCFG f;
  visitCilFile (new cfgVisitor (optimizeFun counts)) f;
  f