open Linda
open Cil
open Lidoutil
module E = Errormsg

let enable = ref false

class globalVarVisitor h = object inherit nopCilVisitor
    method vglob glob = match glob with
      | GFun(fundec,loc) ->
        if fundec.svar.vname = "main" then begin
          let vi = mkFunctionVarinfo "BOP_Init" in
          let vi' = mkFunctionVarinfo "BOP_End" in
          fundec.sbody.bstmts <- 
            mkStmtOneInstr (Call (None,Lval(var vi),[],loc)) :: fundec.sbody.bstmts;
          insertAtEnd (mkStmtOneInstr (Call (None,Lval(var vi'),[],loc))) fundec;
          ChangeDoChildrenPost ([GFun(fundec,loc)],id)
        end else DoChildren
      | GVar(vi,ii,loc) ->
        let vi' = makeGlobalVar (vi.vname^"_GccMonk_P") (TPtr(vi.vtype,[])) in
                Hashtbl.add h vi vi';
        ChangeTo [GVar(vi',ii,loc)]
            | _ -> DoChildren
    method vlval lv = match lv with
            | Var vi,off ->
                if Hashtbl.mem h vi then begin
                    let vi' = Hashtbl.find h vi in
                    Errormsg.log "here %s => %s \n" vi.vname vi'.vname;
                    ChangeTo (Mem(Lval(Var vi',NoOffset)),off)
                    end
                else SkipChildren
          | _ -> DoChildren 
end 

open List
let trans file =
  let h = Hashtbl.create 3 in
  visitCilFile (new globalVarVisitor h) file;
  let f = makeGlobalVar "BOP_PutLNCData" (TFun(TPtr(TVoid [],[]),
    Some ["",TInt(IUInt,[]),[];
    "",TPtr(TInt(IChar,[]),[]),[];
    "",TPtr(TInt(IChar,[]),[]),[]],false,[])) in
  let fname' = file.fileName in
  let body = {battrs = [];
  bstmts = [{dummyStmt with skind = Instr (map (fun (vi,vi') ->
     Call(Some(var vi'),viExp f,[SizeOf vi.vtype;
        mkString vi'.vname;
        mkString fname'],locUnknown)) @$ HashMap.to_list h)}]} in
  let gptrInitVi = makeVarinfo true 
        ("GccMonk_GPtr_Init_"^Filename.chop_extension file.fileName) 
            (TFun(TVoid [],None,false,[])) in
  let gptrInit = GFun ({
    svar = gptrInitVi;
    sformals = [];
    slocals = [];
    smaxid = 0;
    sbody = body;
    smaxstmtid = None;
    sallstmts =[]
    },locUnknown) in
  file.globals <- file.globals@[gptrInit];
  file