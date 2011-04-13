(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(* 
 * Heapify: a program transform that looks over functions, finds those
 * that have local (stack) variables that contain arrays, puts all such
 * local variables into a single heap allocated structure, changes all
 * accesses to such variables into accesses to fields of that structure
 * and frees the structure on return. 
 *)
open Cil
open Printf
open Expcompare
open Reachingdefs
(*open Deadcodeelim*)
(*open Liveness*)
open Callgraph
module AVLE = Availexps
module L=List
module A=Array
module H=Hashtbl
module E=Errormsg
module VS = Usedef.VS
open Linda
(*open Lidoutil*)

(* utilities that should be in Cil.ml *)
(* sfg: this function appears to never be called *)
let mkSimpleField ci fn ft fl =
  { fcomp = ci ; fname = fn ; ftype = ft ; fbitfield = None ; fattr = [];
    floc = fl }

let (<<) f g = fun x -> let x' = g x in f x'
let (>>) g f = fun x -> let x' = g x in f x'
(*(f << g) x = f (g x) = (g >> f) x *)
let range n = 
	let rec range' i = if i <= 0 then [] else pred i::(range' (pred i)) in
	L.rev (range' n)
let get_keys h = let acc = ref [] in
	H.iter (fun x y -> acc:= x::!acc) h;
	!acc
let get_values h = let acc = ref [] in
	H.iter (fun x y -> acc:= y::!acc) h;
	!acc
exception Cant_split
let list_split n ls = 
	let rec list_split' i pre post = 
		if i = 0 then L.rev pre,post else
			match post with hd::tl -> list_split' (pred i) (hd::pre) tl
				| [] -> raise Cant_split
	in list_split' n [] ls 

let exp_add a b = if a =zero then b else 
	if b = zero then a else BinOp(PlusA,a,b,uintType)
let exp_mult a b = if a = one then b else
	if b = one then a else
	if a = zero || b = zero then zero else 
	BinOp(Mult,a,b,uintType)
let get_op = function "<" -> Lt |"<=" -> Le |">" -> Gt |">=" -> Ge |"==" -> Eq|"&&" -> LAnd |"||" -> LOr 
	| _->assert false
let exp_op op a b = let op' = get_op op in BinOp(op',a,b,uintType)

class stripAllCastsVisitor = object inherit nopCilVisitor 
  method vexpr = function CastE(t,e) -> ChangeDoChildrenPost(e,fun x->x)
		|_->DoChildren
end
let stripAllCasts = visitCilExpr (new stripAllCastsVisitor)
(* actual Heapify begins *)

let heapifyNonArrays = ref false

let recogDotProduct = ref false

let doStructPeel = ref false

let swapAndCollapseFloatArray = ref false

let mergeLoop = ref false

let assumeDistinct = ref ""

(* Does this local var contain an array? *)
let rec containsArray (t:typ) : bool =  (* does this type contain an array? *)
  match unrollType t with
    TArray _ -> true
  | TComp(ci, _) -> (* look at the types of the fields *)
      List.exists (fun fi -> containsArray fi.ftype) ci.cfields
  | _ -> 
    (* Ignore other types, including TInt and TPtr.  We don't care whether
       there are arrays in the base types of pointers; only about whether
       this local variable itself needs to be moved to the heap. *)
   false

let same_lv = Util.equals
let extract_cnt lval exps = function 
	"calloc" -> L.hd exps
	|"malloc" -> let Some pointed_type = Lidoutil.get_pointed_type (typeOfLval lval) 1 in
		(match L.hd exps with 
		BinOp(Mult,SizeOf typ,exp,_) |BinOp(Mult,exp,SizeOf typ,_) -> 
		assert (typeSig typ=typeSig pointed_type);exp
		| e -> BinOp(Div,e,SizeOf  pointed_type, TInt(IUInt,[]))
		)
	| x -> failwith ("extract_cnt "^x)
class heapifyAnalyzeVisitor_read_vis refer_vis = object(self) inherit nopCilVisitor
	method vvrbl vi = H.replace refer_vis vi ();SkipChildren
end
let refer_vis_of_exp e = let refer_vis = H.create 30 in
	ignore (visitCilExpr (new heapifyAnalyzeVisitor_read_vis refer_vis) e);
	refer_vis
let exp_refer_vi e vi = H.mem (refer_vis_of_exp e) vi
let stmts_refer_vis stmts = let refer_vis = H.create 100 in
	ignore(visitCilBlock (new heapifyAnalyzeVisitor_read_vis refer_vis) (mkBlock stmts));
	refer_vis
class heapifyAnalyzeVisitor_written_vi written_vis = object(self) inherit nopCilVisitor
	method vinst = function
		Call(Some lv,_,exps,_) ->
			let vi,_,_ = Lidoutil.varinfo_and_level_of_lval lv in H.replace written_vis vi ();
			L.iter (fun vis -> H.iter (fun vi d -> if vi.vaddrof then H.replace written_vis vi ()) vis) (L.map refer_vis_of_exp exps);
			DoChildren
		|Call(None,_,exps,_) ->
			L.iter (fun vis -> H.iter (fun vi d -> if vi.vaddrof then H.replace written_vis vi ()) vis) (L.map refer_vis_of_exp exps);
			DoChildren
		|Set(lv,_,_) -> 
			let vi,_,_ = Lidoutil.varinfo_and_level_of_lval lv in H.replace written_vis vi ();DoChildren
		|_->DoChildren
end
let stmts_written_vis stmts = let written_vis = H.create 100 in
	ignore(visitCilBlock (new heapifyAnalyzeVisitor_written_vi written_vis) (mkBlock stmts));
	written_vis
exception Intersected
let hashtbl_intersect h1 h2 = try H.iter (fun k d -> if H.mem h2 k then raise Intersected) h1;false
	with Intersected -> true
let involve_io vi = L.mem vi.vname ["fprintf";"fscanf";"printf";"scanf"]
let stmt_blk_dependent stmts stmts2 = 
	let refer_vis,refer_vis2 =stmts_refer_vis stmts,stmts_refer_vis stmts2 in
	let written_vis,written_vis2 =stmts_written_vis stmts,stmts_written_vis stmts2 in
	hashtbl_intersect written_vis written_vis2 ||	
	hashtbl_intersect written_vis refer_vis2 ||
	hashtbl_intersect written_vis2 refer_vis ||
	L.exists involve_io (get_keys refer_vis) ||
	L.exists involve_io (get_keys refer_vis2)
let stmt_blk_written_dependent stmts stmts2 = 
	let written_vis,written_vis2 =stmts_written_vis stmts,stmts_written_vis stmts2 in
	hashtbl_intersect written_vis written_vis2

(*Q is linear of P, hence can be replace by P*)
let replace_table = let h = H.create 20 in 
(*    H.add h ("__anonstruct_f1_neuron_19","Q") "P";*) (*TODO:*)
    h

(*life time of W and U does not overlap*)
(*let reuse_table = let h = H.create 20 in            *)
(*(*	H.add h ("__anonstruct_f1_neuron_19","W") "U";*)*)
(*(*	H.add h ("__anonstruct_f1_neuron_19","V") "U";*)*)
(*(*	H.add h ("__anonstruct_f1_neuron_19","X") "U";*)*)
(*	h                                                 *)
(*X is linear of U, R is linear of U and P*)
(*let (linear_list:(string,(varinfo*exp)list) H.t) = 
	let h = H.create 20 in H.add h "R" ["U",one;"P",Const(CReal(0.11,FDouble,None))];h *)

(*DLower flattens lowest \i dimensions *)
type lower_type = DLower of int*(exp option array) | LFuture
type inlinee_state = IChanged | INotChanged
(*let to_inline = H.create 20(*let h = H.create 20 in H.add h "simtest" None;H.add h "weightadj" None;H.add h "match" None;H.add h "reset_nodes" None;H.add h "reset_nodes2" None;H.add h "find_match" None;h(* "train_match" None;h*)*)*)
(*let (dadic_peel_actions:int option) = let h = H.create 20 in H.add h "I" None;h*)

let rec prod_of_exps = function [Some exp] -> exp
	| exp::tl -> BinOp(Mult,prod_of_exps [exp],prod_of_exps tl,TInt(IUInt,[]))
	| _-> failwith "prod_of_vis"
let rec gen_index (idx_lst:exp list) exps = 
	(*with a[idx0][idx1] and spans as exp0 exp1, give exp of idx0*exp1+idx1*)
	E.log "gen_index: %d %d\n" (L.length idx_lst) (L.length exps) ;
	match idx_lst,exps with [idx],[Some exp] -> idx 
		| (hd::tl),(_::exps_tl) -> 
			BinOp(PlusA,BinOp(Mult,hd,prod_of_exps exps_tl,TInt(IUInt,[])),gen_index tl exps_tl,TInt(IUInt,[]))
		| _ -> failwith "gen_index" 
let rec gen_dim = function 
	| [Some exp] -> exp
	| (Some exp)::tl -> BinOp(Mult,exp,gen_dim tl,TInt(IUInt,[]))
	| _-> failwith "gen_dim"
let gen_dim_exp exps typ = BinOp(Mult,gen_dim exps,SizeOf typ,TInt(IUInt,[]))
(*general visitor*)
class heapifyModifyVisitor (*yeild num_instr instructions to caller, replace yielded with received*)
(is_interesting:instr list->bool) num_instr (transform:instr list-> stmt list option) = object(self) inherit nopCilVisitor
  method vstmt s = 
	let changed = ref false in
	match s.skind with Instr insts -> (
	let rec proc post stack acc_stmt_list = 
		try
			let first_n ,tl = list_split num_instr post in
			if is_interesting first_n then
				let transformed = L.rev (match transform first_n with Some res -> changed:=true;res 
					| None ->[mkStmt(Instr first_n)]) in
				(match stack with [] -> proc tl [] (transformed@acc_stmt_list)
				| _-> proc tl [] (transformed@((mkStmt(Instr(L.rev stack)))::acc_stmt_list)))
			else (*forward one step*)
				proc (L.tl post) (L.hd post::stack) acc_stmt_list
		with Cant_split ->
			(match L.rev stack@post with [] -> acc_stmt_list
			|x -> mkStmt(Instr x)::acc_stmt_list)
	in
		let res = proc insts [] [] in
		if !changed then ChangeTo(mkStmt(Block(mkBlock(L.rev res)))) else DoChildren
	)
	|_->DoChildren
end

let handle_alloc_is_interesting = function [Call (Some _, Lval(Var v,NoOffset),_,_);(Set(_,_,_))]
		when List.mem v.vname ["malloc";"calloc";"realloc"] -> true
		|_-> false 
let handle_alloc trans = visitCilBlock (new heapifyModifyVisitor handle_alloc_is_interesting 2 trans)
let handle_dual_sets_is_interesting = function [Set _;Set _] -> true
		|_-> false 
let handle_dual_sets trans = visitCilBlock (new heapifyModifyVisitor handle_dual_sets_is_interesting 2 trans)

let del_field_table = let h = H.create 20 in 
    (*H.add h "node" ["ident"];*) (* mcf may use this*)
    h
class heapifyModifyVisitor_del_field del_field_table (f:file)= object inherit nopCilVisitor 
  method vglob gl = 
	match gl with
  | GCompTag (ci, loc) -> (
		try
			let del_list = H.find del_field_table ci.cname in 
			ci.cfields <- L.filter (fun fi -> not (L.mem fi.fname del_list)) ci.cfields;
			DoChildren
		with Not_found -> DoChildren
	)
	|_->DoChildren
end

class heapifyModifyVisitor_replace_field (replace_table:(string*string,string) H.t)
      = object(self) inherit nopCilVisitor 
  method vlval l = 
	match l with 
    | lh, Field (fi,ofst) ->
		(try let new_fname = H.find replace_table (fi.fcomp.cname,fi.fname) in
			E.log "replace %s with %s\n" fi.fname new_fname;
			fi.fname <- new_fname;
			let new_lval = lh, Field (fi,ofst) in
			ChangeTo(new_lval)
		with Not_found -> DoChildren)
  | _ -> DoChildren 
end

class heapifyModifyVisitor_del_lhs (del_table:(string*string,string) H.t)
     = object(self) inherit nopCilVisitor 
  method vstmt s = 
	match s.skind with 
	Instr insts -> 
		let should_keep = 
			function Set((lh,Field(fi,ofst)),exp,loc)-> not (H.mem del_table (fi.fcomp.cname,fi.fname))
					| _-> true
		in s.skind <- Instr (L.filter should_keep insts);DoChildren
	|_->DoChildren
end
type visit_type =  VBad | VOnce of exp
let currentGlobalsWritten = H.create 30
let gw_tainted = H.create 30 (*written with non-constant offset*)
class gwModifyClass : cilVisitor = object (self) (*assume no use of uninit'ed lval*)
  inherit nopCilVisitor
	method vexpr = function
		Lval ((Var vi,_)as lv) -> (try (match H.find currentGlobalsWritten lv with 
				VOnce e2 -> if H.mem gw_tainted vi.vid || vi.vaddrof then DoChildren else ChangeTo (e2)
				| VBad -> DoChildren)
			with Not_found -> DoChildren)
		|_->DoChildren
end
let constant_off = function NoOffset -> true
	|Index(idx,NoOffset)-> isConstant idx 
	|Field _->true
	|_->false
class gwVisitorClass : cilVisitor = object (self) (*a lval assigned once is constant*)
  inherit nopCilVisitor
  method vinst = function
    Set ((Var vi,off) as lv, e, _) ->
			if constant_off off then (
				(try (match H.find currentGlobalsWritten lv with 
					VOnce e2 -> H.replace currentGlobalsWritten lv VBad
					| VBad -> ())
				with Not_found -> (
					if isConstant e then (
						if vi.vglob then (
						E.log "found constant %a %a\n" d_plainlval lv d_plainexp e;
						H.replace currentGlobalsWritten lv (VOnce e)))
					else H.replace currentGlobalsWritten lv VBad)
				);SkipChildren)
			else (H.add gw_tainted vi.vid ();
				SkipChildren)
		| Call (Some lv, _, _, _) -> (*give up*) H.replace currentGlobalsWritten lv VBad;SkipChildren
    | _ -> DoChildren
end

class globlDSEVisitor toKill = object inherit nopCilVisitor
method vinst inst = match inst with
  | Set(lv,_,_) -> begin
(*	    try*)
	      let vi,n,es = Lidoutil.varinfo_and_level_of_lval lv in
	      if Linda.HashSet.mem toKill (vi.vname,n) then begin
	            E.log "[globlDSEVisitor]: elim %s %d\n" vi.vname n;
	            ChangeTo []
	      end else
	        SkipChildren
(*	    with _ -> SkipChildren*)
    end
  | _ -> SkipChildren
end        
(*loop opt*)
(*let pretty stm =
	let prettyprint didstmh stmdat () (_,s,iosh) = L.iter (fun (vid,ios) ->
		L.iter (fun io ->
		match io with Some i -> 
		let stm = IH.find didstmh i in E.log "stmt: %a\n" d_stmt stm
		|None -> ()) ios) (IH.tolist iosh)
		in
    let ivih = IH.find ReachingDef.stmtStartData stm.sid in
    prettyprint ReachingDef.defIdStmtHash ReachingDef.stmtStartData () ivih
*)

let prettyprint didstmh stmdat () (_,s,iosh) =
  L.iter (fun (vid,ios) ->
		E.log "pretty vid %d\n" vid;
      IOS.fold (fun io d -> match io with
  None -> ()
 | Some i ->
		E.log "pretty io %d\n" i;
    let stm = IH.find didstmh i in
		E.log "pretty stm %a\n" d_stmt stm;
    match getDefRhs didstmh stmdat i with
      None -> ()
    | Some(RDExp(e),_,_) ->
        E.log "pretty exp %a\n" d_exp e
    | Some(RDCall(c),_,_) ->
        E.log "pretty instr %a\n" d_instr c
			)
      ios ())
    (IH.tolist iosh)

let pretty = prettyprint ReachingDef.defIdStmtHash ReachingDef.stmtStartData

let pretty_sid sid = let ivih = IH.find ReachingDef.stmtStartData sid in
    pretty () ivih
class heapifyAnalyzeVisitor_loop = object(self) inherit nopCilVisitor 
  method vglob gl = (*E.log "global:\n%a\n" d_shortglobal gl;*) match gl with
    GFun(fundec,funloc) -> 
		(*computeRDs fundec;
		ppFdec fundec;
		elim_dead_code_fp fundec;*)
		Cfg.clearCFGinfo fundec;
		ignore (Cfg.cfgFun fundec);
		(*computeLiveness fundec;
		print_everything();*)
		computeRDs fundec;
		(*ReachingDef.debug := true;	*)
		DoChildren
	|_->DoChildren

  method vstmt s = 
	match s.skind with 
	Loop(_,loc,_,_)-> 
		E.log "a loop at line %d\n%a\n" loc.line d_stmt s;
		pretty_sid s.sid;
		let u,d = Usedef.computeDeepUseDefStmtKind s.skind in
		E.log "Used: ";
		Usedef.VS.iter (fun vi -> E.log "%s " vi.vname) u	;
		E.log "\n";
		DoChildren
	|_->DoChildren
end

class heapifyModifyVisitor_replace_vi old_vi new_vi = object(self) inherit nopCilVisitor
	method vvrbl vi = if vi = old_vi then ChangeTo new_vi else DoChildren
end
class replace_lv_with_exp old_lv e changed = object(self) inherit nopCilVisitor
	method vexpr = function Lval lv when same_lv lv old_lv -> 
		(*E.log "replace_lv_with_exp: %a => %a\n" d_plainlval old_lv d_plainexp e;*)
		changed:=true;
		ChangeTo e
	|_->DoChildren
end
let replace_blk_vi vi nvi =  visitCilBlock (new heapifyModifyVisitor_replace_vi vi nvi)
(*simplify index*)
let rec sym_diff exp1 exp2 = 
	(*E.log "sym_diff %a\n%a\n" d_plainexp exp1 d_plainexp exp2;*)
	match exp1,exp2 with
	| BinOp(op,x,y,_),BinOp(op2,x2,y2,_) when op=op2 -> 
		(match sym_diff x x2 with Some zero -> sym_diff y y2
		|None->None)
	| BinOp(Mult,x,y,_),BinOp(Mult,x2,y2,_) -> 
		(match sym_diff x x2 with Some res when res = zero -> Some zero
		|Some res -> Some(BinOp(Mult,x,res,uintType))
		|None -> None
		)
	| Lval(Var vi,NoOffset),Lval(Var vi2,NoOffset) -> if vi = vi2 then Some zero else None
	| Const(CInt64(x,k,_)),Const(CInt64(x2,k2,_)) when k=k2 -> Some (integer (Int64.to_int x-Int64.to_int x2))
	| _,_ -> None
let rec try_split expr = function 
	hd::tl -> 
		(match sym_diff expr hd with Some res -> Some(hd,res)
		|None -> try_split expr tl
		)
	| [] -> None
class heapifyModifyVisitor_simplify_index = object(self) inherit nopCilVisitor
	val mutable bases = ([]:exp list)
	val bases_to_temp_map = (H.create 30:(exp,varinfo) H.t)
	val mutable currentFundec = (None:fundec option)
	method vglob = function GFun(dec,funloc) -> (currentFundec <- Some dec;DoChildren)
		|_->SkipChildren
	method vlval = function Mem e,NoOffset ->
			(match e with BinOp(IndexPI,Lval(Var vi,NoOffset),new_idx,uintType) ->
				(match try_split e bases with None ->
					E.log "find base %a\n" d_plainexp e;
					bases <- e::bases;
					(match currentFundec with Some fundec -> 
						H.replace bases_to_temp_map e (makeTempVar fundec (typeOf e))
					|_->assert false);
					SkipChildren
				|Some(base,res) -> 
					E.log "replace %a with %a\n" d_plainexp e d_plainexp res;
					try
						let temp = var (H.find bases_to_temp_map base) in
						ChangeTo(Mem(BinOp(IndexPI,Lval temp,res,uintType)),NoOffset)
					with Not_found -> assert false
				)
			|_-> SkipChildren
			)
		|_->SkipChildren
	method vblock blk = 
		(*L.flatten (L.map find_index_bases blk.bstmts);*)
		DoChildren

(*		let changed = ref false in
		let bstmts' = merge_loop changed blk.bstmts in
		if !changed then (E.log "merge loop\n";blk.bstmts <- bstmts';DoChildren) else DoChildren
*)
end

(*loop fusion*)
type loop_struct = {vi:varinfo;lower:exp;upper:exp;stride:exp;body:stmt list;prologue:stmt option}
let expand_loop_struct ls = mkForIncr ls.vi ls.lower ls.upper ls.stride ls.body
let show_loop_struct ls1 = E.log "vi.vname %s\n lower %a\n upper %a\n stride %a\n"
						ls1.vi.vname d_plainexp ls1.lower
						d_plainexp ls1.upper d_plainexp ls1.stride
let loop_struct_compaitble ls1 ls2 = (*too strict TODO*)
	ls1.vi.vid = ls2.vi.vid && ls1.lower = ls2.lower && ls1.upper = ls2.upper && ls1.stride = ls2.stride
(*let normalize_cmp = function 
	BinOp(Lt,_,exp2,_) as x -> x
	|BinOp(Le,exp1,exp2,_) -> BinOp(Lt,exp1,BinOp(PlusA,exp2,one,uintType))
	|x-> E.log "normalize_cmp %a\n" d_plainexp x;assert false*)
let get_init = function Instr insts -> 
	(match (L.rev insts) with Set(lv,exp,_)::tl -> 
			if tl = [] then Some (lv,exp,None) else Some(lv,exp,Some(mkStmt(Instr(L.rev tl))))
		|_->None
	) |_->None
let get_upper = function If(BinOp(op,Lval lv,exp,_) as e,_,_,_) -> 
	(match op with Lt -> Some(lv,exp)
		|Le->Some(lv,BinOp(PlusA,exp,one,uintType))
		|_->E.log "get_upper %a\n" d_plainexp e;None
	) |_->None
let get_stride = function Instr insts ->
	(match L.hd (L.rev insts) with Set(lv,BinOp(PlusA,Lval lv2,stride,_),_) -> 
		if lv = lv2 then Some (lv,stride) else None
	|_->None
	) |_->None
let trim_last x = let pre,_ = list_split (L.length x-1) x in pre
let last_n ls n = L.rev (A.to_list (A.sub (A.of_list (L.rev ls)) 0 n))
let get_body blk = (*remove the first 'break' and last 'incr'*)
	match L.tl blk.bstmts with (_::_) as x -> 
		(match list_split (L.length x-1) x with pre,[{skind=Instr insts} as last] ->
			let trailing = match trim_last insts with [] -> [] 
				|insts' -> [{last with skind = Instr insts'}] in
			pre@trailing
		|_->assert false)
	|[] -> []
class viFinderClass_by_name name br = object(self)
  inherit nopCilVisitor
  method vvrbl vi' = 
    if name = vi'.vname
    then (br := true; SkipChildren)
    else DoChildren
end
let block_has_vi_name name blk =
  let br = ref false in
  let vis = new viFinderClass_by_name name br in
  ignore(visitCilBlock vis blk);
  !br
let stmt_has_vi_name name i =
  let br = ref false in
  let vis = new viFinderClass_by_name name br in
  ignore(visitCilStmt vis i);
  !br

let rec get_loop_struct(s1,s2)= 
			match s1.skind,s2.skind with Instr insts,Loop(blk,_,_,_) ->
				if L.length blk.bstmts>=1 then
					match get_init s1.skind,get_upper (L.hd blk.bstmts).skind,get_stride (L.hd (L.rev blk.bstmts)).skind
						with Some(lv1,lower,tl),Some(lv2,upper),Some(lv3,stride) ->
							if lv1=lv2 && lv2=lv3 then 
								match lv1 with Var vi,_ -> 
									let res = {vi=vi;lower=lower;upper=upper;stride=stride;
												body=get_body blk;prologue=tl} in
(*									show_loop_struct res;*)
									Some res
								|_->None
							else (E.log "lv1!=lv2 or lv2!=lv3\n";None)
						(*|None,_,_ -> (match s2.skind with Loop _-> E.log "init stmt %a\n" d_stmt s1|_-> ());None*)
						|_->None
				else (E.log "infinite loop?\n";None)
			|_-> None
let process_prologue = function Some tl -> [tl]
	|None -> []

let isInstrSetZero instr = match instr with
  | Set (_,e,_) -> (match e with
    | Const (CReal (0.0,_,_)) -> true
    | Const (CInt64 (x,_,_)) when x=Int64.zero -> true
    | _ -> false
    )
  | _ -> false

exception Found
let stmtPatternCheck stmts stmts' =
  let getRW stmts =
    let r,w = Lidoutil.arrReadWritePatternDeepStmt stmts in
    List.filter (function (vi,_) when vi.vglob && vi.vname= !assumeDistinct -> false 
        | _ -> true) @$
    (r@w) in
  let p1 = ExtList.nub (ExtList.concatMap getRW stmts) in
  let p2 = ExtList.nub (ExtList.concatMap getRW stmts') in
  let hasConflict l l' =
    let toTable l = 
	    let h = Hashtbl.create 3 in
	    List.iter (fun (vi,es) -> 
	      if Hashtbl.mem h vi.vname then (
          let oes = Hashtbl.find h vi.vname in
          if not (ExtList.equalBy Expcompare.compareExp es oes) then (
          E.log "stmtPatternCheck:%s\n" vi.vname;
          List.iter (E.log "%a " d_exp) es;
          E.log "\n";
          List.iter (E.log "%a " d_exp) oes;
          E.log "\n"; 
          raise Found
          ))
	      else Hashtbl.replace h vi.vname es) l;
	    h in
    try
      let h,h' = toTable l,toTable l' in
	    Hashtbl.iter (fun k v -> 
	      try let v' = Hashtbl.find h' k in
	        if not (ExtList.equalBy Expcompare.compareExp v v') then (
            E.log "stmtPatternCheck:%s\n" k;
            raise Found)
	      with Not_found -> ()) h;
      false
    with Found -> true in
  not (hasConflict p1 p2)

let rec merge_loop changed stmts= 
	let rec merge_loop' acc = function stm1::stm2::stm3::stm4::tl -> 
		(match get_loop_struct(stm1,stm2),get_loop_struct(stm3,stm4) with Some ls1,Some ls2 ->
			let prog1 = process_prologue ls1.prologue in
			let prog2 = process_prologue ls2.prologue in
			if loop_struct_compaitble ls1 ls2 
(*				&& not (stmt_has_vi_name "ARCHmatrixcol" stm4) (*TODO*)   *)
(*				&& not (stmt_has_vi_name "smvp" stm3) (*TODO*)            *)
(*				&& ((false && not (stmt_blk_dependent (ls1.body) (prog2)) *)
(*				&& not (stmt_blk_written_dependent (ls1.body) (ls2.body)))*)
(*				|| (stmt_has_vi_name "disp" stm2) (*TODO*) )              *)
       && not (stmt_blk_dependent (ls1.body) (prog2))
(*      && not (ExtList.all id @$ List.map isInstrSetZero     *)
(*        @$ ExtList.concatMap Lidoutil.instrsOfStmt ls1.body)*)
(*       && not (stmt_blk_written_dependent (ls1.body) (ls2.body))*)
       && stmtPatternCheck ls1.body ls2.body
				then 
				(changed:=true;
				merge_loop' acc (prog1@prog2@(expand_loop_struct 
					{ls1 with body = (ls1.body@ls2.body)})@tl)
				) 
			else merge_loop' (stm2::stm1::acc) (stm3::stm4::tl) 
			|_->merge_loop' (stm1::acc) (stm2::stm3::stm4::tl) 
		)
		|[]->L.rev acc
		| hd::tl ->merge_loop' (hd::acc) tl in
	merge_loop' [] stmts 

class heapifyModifyVisitor_loop = object(self) inherit nopCilVisitor (*do syntactical merge*)
	method vblock blk = 
		let changed = ref false in
		let bstmts' = merge_loop changed blk.bstmts in
		if !changed then (E.log "merge loop\n";blk.bstmts <- bstmts';DoChildren) else DoChildren
end
(*art's tds loop reduce*)
let loop_triger (transform:stmt*stmt->stmt list option) repetitive = 
	let changed = ref false in
	let rec loop_triger' acc = function stm1::stm2::tl ->
		(match get_loop_struct (stm1,stm2) with Some ls->
			(match transform(stm1,stm2) with Some res -> 
				if repetitive then (changed:=true;loop_triger' acc (res@tl))
				else (changed:=true;loop_triger' (L.rev res@acc) tl)
			|None->loop_triger' (stm2::stm1::acc) tl)
		|None -> loop_triger' (stm1::acc) (stm2::tl))
	| hd::tl -> loop_triger' (hd::acc) tl
	| [] -> if !changed then Some (L.rev acc) else None in
	loop_triger' []
let loop_reduce_trans(stm1,stm2) = match get_loop_struct (stm1,stm2) with Some ls-> (
		match ls.body with [{skind = If (e,tb,{bstmts=[]},_)}] ->
			E.log "loop_reduce_trans\n";
			(match e with BinOp(Eq,Lval(Var v, NoOffset),Lval(Var v2,NoOffset),_) ->
				if ls.vi = v then (
					let e_var = Lval(Var v2, NoOffset) in
					let tb' = replace_blk_vi v v2 tb in
					let nest2 = mkStmt(If(exp_op "<=" ls.lower e_var,tb',mkBlock [],locUnknown)) in
					let nest1 = mkStmt(If(exp_op "<" e_var ls.upper,mkBlock[nest2],mkBlock [],locUnknown)) in
					Some [stm1;nest1]
				) else None
			|_->None)
		|_->None)
	|None -> assert false	
class heapifyModifyVisitor_loop_reduce = object(self) inherit nopCilVisitor
	method vblock blk = match loop_triger loop_reduce_trans false blk.bstmts with Some res -> 
		ChangeTo {blk with bstmts=res}
	|None -> DoChildren
end

type arrayInfo = {
  mutable arrAllUsed : VS.t;
  mutable arrAllDefed : VS.t;
  mutable arrMayUsed : VS.t;
  mutable arrMayDefed : VS.t;
  }  

let getEmptyArrayInfo () = {
  arrAllUsed = VS.empty;
  arrAllDefed = VS.empty;
  arrMayUsed = VS.empty;
  arrMayDefed = VS.empty;
  }

let loop_array_info_collect (stm1,stm2) = 
  match get_loop_struct (stm1,stm2) with 
    | Some ls-> (
        
        None
      )
    | None -> assert false

class arrayUseDefVisitorClass ai : cilVisitor = object(self) inherit nopCilVisitor
    method vblock blk = match loop_triger loop_array_info_collect false blk.bstmts with 
      | Some res -> DoChildren
    |None -> DoChildren
end
   
let computeArrayUseDefStmt stmt =
  let ai = getEmptyArrayInfo () in 
  ignore (visitCilStmt (new arrayUseDefVisitorClass ai) stmt);
  ai

(*lift pure calls out of loop*)
exception NonPure
let pure_calls = 
	let pure_intrinsics = ["sin";"cos"] in
	let h = H.create 300 in
	L.iter (fun x -> H.replace h x None) pure_intrinsics;
	h
class heapifyAnalyzeVisitor_is_pure_call fundec = object(self) inherit nopCilVisitor (*do syntactical merge*)
	method vvrbl vi = if vi.vglob && not (isFunctionType vi.vtype) then raise NonPure;DoChildren
  method vinst inst = 
		let check_lv lv = let vi,_,_ = Lidoutil.varinfo_and_level_of_lval lv in 
			if vi.vglob || L.mem vi fundec.sformals then raise NonPure in
		let check_call vname = if not (H.mem pure_calls vname) then raise NonPure in
		(match inst with Set (lv,_, _) -> check_lv lv
			|Call(Some lv,Lval (Var vi,NoOffset),_,_)-> check_lv lv;check_call vi.vname
			|Call(None,Lval (Var vi,NoOffset),_,_)-> check_call vi.vname
			|_->());
		DoChildren
end
class heapifyAnalyzeVisitor_find_pure_call = object(self) inherit nopCilVisitor
	method vglob = function GFun(fundec,funloc) ->
		(try 
			ignore(visitCilBlock (new heapifyAnalyzeVisitor_is_pure_call fundec) fundec.sbody);
			H.replace pure_calls fundec.svar.vname (Some fundec);SkipChildren
		with NonPure -> SkipChildren)
		|_->SkipChildren
end
class heapifyModifyVisitor_find_pure_call written_vis lift_insts= object(self) inherit nopCilVisitor
	method vinst = function (Call(Some lv,Lval(Var vi,NoOffset),exps,_)) as inst 
		when H.mem pure_calls vi.vname ->
		E.log "heapifyModifyVisitor_find_pure_call\n";
		let refer_vis = H.create 30 in
			L.iter (fun e -> ignore (visitCilExpr (new heapifyAnalyzeVisitor_read_vis refer_vis) e)) exps;
		E.log "pure_call %s refers " vi.vname;
		L.iter (fun vi -> E.log "%s " vi.vname) (get_keys refer_vis);
		E.log "\n";
		if (L.exists (H.mem written_vis) (get_keys refer_vis)) then (
			L.iter (fun vi2 -> E.log "%s prevent lifting %s\n" vi2.vname vi.vname) (L.filter (H.mem written_vis) (get_keys refer_vis));
			DoChildren)
		else (lift_insts:= inst::!lift_insts;ChangeTo [])
	|_->SkipChildren
end
let loop_lift_pure_call_trans(stm1,stm2) = match get_loop_struct (stm1,stm2) with Some ls-> (
		let written_vis = H.create 30 in
		match stm2.skind with Loop (blk,loc,os1,os2) -> 
			ignore (visitCilBlock (new heapifyAnalyzeVisitor_written_vi written_vis) blk);
			E.log "written_vis ";
			L.iter (fun vi -> E.log "%s " vi.vname) (get_keys written_vis);
			E.log "\n";
			E.log "blk length %d\n" (L.length blk.bstmts);
			let lift_insts = ref [] in
				let blk' = visitCilBlock (new heapifyModifyVisitor_find_pure_call written_vis lift_insts) blk; in
				if !lift_insts <> [] then 
					let lifted = [mkStmt (Instr !lift_insts)] in
					Some(lifted@[stm1]@[{stm2 with skind = Loop (blk',loc,os1,os2)}])
				else None
			|_->assert false
		)
		(*L.iter2 (fun stm idx -> 
			match stm.skind with Instr insts ->
			L.iter2 (fun inst idx2 ->
				match inst with Call(Some lv,Lval(Var vi,NoOffset),exps,_) when H.mem pure_calls vi.vname ->
					if any (L.map (fun vi -> any (L.map (AVLE.exp_has_vi vi) exps)) (get_keys written_vis)) then ()
					else H.replace mark_for_del (idx,idx2) inst	
				|_->()
			) insts (range (L.length insts))
			|_-> ()
		) ls.body (range (L.length ls.body));
		Some ([stm1;mkStmt(Instr(get_values mark_for_del));stm2]))*)
	|None -> assert false	
class heapifyModifyVisitor_lift_pure_call = object(self) inherit nopCilVisitor
	method vblock blk = 
	match loop_triger loop_lift_pure_call_trans false blk.bstmts with Some res -> 
		ChangeTo {blk with bstmts=res}
	|None -> DoChildren
end
(*kernel_misc_opt*)
let rec kernel_misc_opt = function Set(lv,e,loc) as inst1 ::(Set(lv2,e2,loc2) as inst2)::tl ->
		if same_lv lv lv2 then (
			E.log "kernel_misc_opt eq lv %a\nlv2 %a\n" d_plainlval lv d_plainlval lv2;
			let changed = ref false in
			let insts = visitCilInstr (new replace_lv_with_exp lv e changed) inst2 in
			if !changed then kernel_misc_opt (insts@tl) else inst1::(kernel_misc_opt (inst2::tl))
		) else (
      E.log "kernel_misc_opt ne lv %a\nlv2 %a\n" d_plainlval lv d_plainlval lv2;
			inst1::(kernel_misc_opt (inst2::tl)))
	|hd::tl -> 
		(match hd with Set(lv,e,loc) -> E.log "kernel_misc_opt not_dual_set lv %a\n" d_plainlval lv;
			if tl<>[] then E.log "next stmt: %a\n" d_stmt (mkStmtOneInstr (L.hd tl)) else E.log "tail empty\n"
		|_->());
		hd::kernel_misc_opt tl
	|[]-> []
let rec compact_stmts = function {skind=Instr insts1;labels=[]}
		::{skind=Instr insts2;labels=[]}::tl -> 
		E.log "compact_stmts\n";
		compact_stmts ({skind=Instr (insts1@insts2);labels=[];sid=(-1);succs=[];preds=[]}::tl)
	|hd::tl-> hd::compact_stmts (tl)
	|[]->[]
class modifier_merge_insts = object(self) inherit nopCilVisitor
	method vblock blk = blk.bstmts <- compact_stmts blk.bstmts;
		DoChildren (*ChangeTo {blk with bstmts = compact_stmts blk.bstmts} *)
end
class modifier_kernel_misc_opt f = object(self) inherit nopCilVisitor
	method vstmt stmt = match stmt with {skind = Instr insts} -> 
		ChangeTo({stmt with skind = Instr(kernel_misc_opt insts)})
	|_->DoChildren
end
(*array regroup*)
let regroup_actions = let h = H.create 30 in
	(*H.add h "M" ["M";"C";"M23";"C23";"V23"];
	H.add h "C" ["M";"C";"M23";"C23";"V23"];
	H.add h "M23" ["M";"C";"M23";"C23";"V23"];
	H.add h "C23" ["M";"C";"M23";"C23";"V23"];
	H.add h "V23" ["M";"C";"M23";"C23";"V23"];
	H.add h "M" ["M";"C"];
	H.add h "C" ["M";"C"];
	H.add h "M23" ["M23";"C23";"V23"];
	H.add h "C23" ["M23";"C23";"V23"];
	H.add h "V23" ["M23";"C23";"V23"];*)
	h
let regroup_trans fundec new_aggrs mallocs_built = 
	function [Call(Some lv,Lval(Var v,NoOffset),exps,loc);Set((Var vi,NoOffset) as lv2,exp2,loc2)] ->
		let vname = vi.vname in
		if H.mem regroup_actions vname then (
			let ci,a_vi = H.find new_aggrs vi.vname in
			let aggr_name = a_vi.vname in
			if not(H.mem mallocs_built aggr_name) then
				let cnt_exp = extract_cnt lv2 exps v.vname in
				let Some etype = Lidoutil.get_pointed_type a_vi.vtype 1 in
				let size_exp = exp_mult cnt_exp (SizeOf etype) in
				H.replace mallocs_built aggr_name ();
				let exp2' = match exp2 with CastE(_,e) -> CastE(a_vi.vtype,e)|x->x in
				Some (L.map mkStmtOneInstr [Call(Some lv,Lval(var v),[size_exp],loc);Set(var a_vi,exp2',loc2)])
			else Some [])
		else None
	|_->None

class heapifyModifyVisitor_regroup_array file = object(self) inherit nopCilVisitor
	val new_aggrs = H.create 30
	val info_collected = H.create 30
	val mallocs_built = H.create 30
	method vexpr e = match stripNopCasts e with 
		BinOp(Eq,Lval(Var vi,NoOffset),e2,ty) 
		|BinOp(Eq,CastE(_,Lval(Var vi,NoOffset)),e2,ty) ->
			if H.mem regroup_actions vi.vname then
				(try let ci,a_vi = H.find new_aggrs vi.vname in
					ChangeTo(BinOp(Eq,Lval(Var a_vi,NoOffset),e2,ty))
				with Not_found -> DoChildren)
			else DoChildren
		|_->DoChildren
	method vlval = function Var vi,Index(idx,NoOffset)
		|Mem(BinOp(IndexPI,Lval(Var vi,NoOffset),idx,_)),NoOffset -> 
		(try let ci,a_vi = H.find new_aggrs vi.vname in
			ChangeTo(Mem(BinOp(IndexPI,Lval(var a_vi),idx,uintType)),Field((getCompField ci vi.vname),NoOffset))
(*			ChangeTo (Var a_vi,Index(idx,Field((getCompField ci vi.vname),NoOffset)))*)
		with Not_found -> DoChildren)
		|_->DoChildren
	method vglob = function
		GVarDecl(vi,_) 
		| GVar(vi,{init=None},_) ->
			(try let siblings = H.find regroup_actions vi.vname in
				E.log "heapifyModifyVisitor_regroup_array\n";
				H.replace info_collected vi.vname vi;
				if ExtList.all id (L.map (H.mem info_collected) siblings) then (
					let sibling_vis = L.map (H.find info_collected) siblings in
					let aggr_name = L.fold_left (^) "" siblings in
					let aggr_typ_name = aggr_name^"_struct" in
					let ci = mkCompInfo true aggr_typ_name 
						(fun _ -> L.map (fun fvi -> 
							(fvi.vname,fromSome 
              (Lidoutil.get_pointed_type fvi.vtype 1),None,[],locUnknown)) sibling_vis) [] in
					let aggr_vi = makeGlobalVar aggr_name (TPtr(TComp(ci,[]),[])) in
					L.iter (fun name -> H.replace new_aggrs name (ci,aggr_vi)) siblings;
					file.globals <- file.globals@[GCompTag(ci,locUnknown);GVarDecl(aggr_vi,locUnknown)];
					ChangeTo [GCompTag(ci,locUnknown);GVarDecl(aggr_vi,locUnknown)]
				) else ChangeTo []
			with Not_found -> SkipChildren)
		|GFun(fundec,funloc) -> 
			fundec.sbody <- handle_alloc (regroup_trans fundec new_aggrs mallocs_built) fundec.sbody;
			DoChildren
		|_->DoChildren
end

(*DADIC stands for Dynamic Array DImension Collapsing. Also performs dimension transposition.
	1. gather spans at alloc, as in dadic_get_dim_trans
	2. make the 0-dim alloc larger, and del >0-dim alloc's, as in dadic_alloc_trans
	3. update indices, as in heapifyModifyVisitor_dadic_update_index
*)

(*count of collaped dimensions and the span to calculate the index*)
type transpose_type = MapTo of int list| Keep
type dadic_action = transpose_type*lower_type

class collectMultiArrayVisitor viLevelTable =
  object(self) inherit nopCilVisitor
  method vlval lv = 
    let vi,level,_ = Lidoutil.varinfo_and_level_of_lval lv in
    if level>1 && vi.vglob && (match Lidoutil.get_pointed_type vi.vtype level 
        with Some (TFloat(_,_)) -> true 
        | _ -> false) then (
      let ol =  try Hashtbl.find viLevelTable vi
                with Not_found -> 0 in
      Hashtbl.replace viLevelTable vi (max ol level) 
    );
    DoChildren
  end

let collectMultiArray (f:file) =
  let viLevelTable = Hashtbl.create 3 in
  visitCilFileSameGlobals (new collectMultiArrayVisitor viLevelTable) f;
  E.log "collectMultiArray\n";
  Hashtbl.iter (fun vi lv -> E.log "%s %d\n" vi.vname lv) viLevelTable;
  let t_ls = List.map (fun (k,v) -> k.vname,MapTo (List.rev (ExtList.range 0 v)) 
    ) @$ ExtHashtbl.to_list viLevelTable in
  let ls = List.map (fun (k,v) -> k.vname,v
    ) @$ ExtHashtbl.to_list viLevelTable in
  let h = H.create 40 in let h2 = H.create 40 in
  L.iter (fun name ->
      let dim = L.assoc name ls in
      H.add h name (if L.mem_assoc name t_ls then L.assoc name t_ls else Keep);
      H.add h2 name (DLower(dim-1,A.make dim None))) (fst (L.split ls));
  h,h2
(*let transpose_actions,dadic_actions =                                                   *)
(*	let t_ls =                                                                            *)
(*     ["bus",MapTo [1;0];"tds",MapTo [1;0];"f1_layer_I",MapTo [1;0];"cimage",MapTo [1;0]]*)
(*    in                                                                                  *)
(*	let ls = ["bus",2;"tds",2;"f1_layer_I",2;"cimage",2]                                  *)
(*(*;"M",2;"C",2;"M23",2;"C23",2;"V23",2;"vel",2]                                         *)
(*	@["ARCHcoord",2]*)                                                                    *)
(*(*"ARCHvertex",2;*)                                                                     *)
(*	in                                                                                    *)
(*	let h = H.create 40 in let h2 = H.create 40 in                                        *)
(*	L.iter (fun name ->                                                                   *)
(*		let dim = L.assoc name ls in                                                        *)
(*		H.add h name (if L.mem_assoc name t_ls then L.assoc name t_ls else Keep);           *)
(*		H.add h2 name (DLower(dim-1,A.make dim None))) (fst (L.split ls));                  *)
(*	h,h2                                                                                  *)

let transpose_dims transpose_actions dadic_actions idxs arr_name = try (
	match H.find transpose_actions arr_name with 
	Keep -> idxs
	| MapTo lst -> let arr = A.of_list idxs in for i = 0  to A.length arr-1 do
		arr.(i)<-L.nth idxs (L.nth lst i) done;A.to_list arr )
	with Not_found -> idxs

(*in fact not a trans, get the span symbols*)
let dadic_get_dim_trans dadic_actions = function [Call(Some lv,Lval(Var v,NoOffset),exps,loc);(Set(lv2,exp2,loc2))] ->( 
		(try 
			E.log "lval %a\n" d_plainlval lv2;
			let v2,level,indices = Lidoutil.varinfo_and_level_of_lval lv2 in
			match H.find dadic_actions v2.vname with DLower(i,arr)-> (
				let exp = extract_cnt lv2 exps v.vname in
				E.log "add dim%d for %s, exp\n%a\n" level v2.vname d_exp exp; 
				(*if not (isConstant exp) then assert false;*) (*may be a flow constant*)
				arr.(level)<-Some exp
			) |_->()
		with Not_found ->());
		None
	)
	|_->assert false

let dadic_alloc_trans dadic_actions = function [Call(Some lv,Lval(Var v,NoOffset),exps,loc);(Set(lv2,exp2,loc2))] ->( 
		try 
			let v2,level,indices = Lidoutil.varinfo_and_level_of_lval lv2 in
				E.log "level = %d stmt:%a\n" level d_plainlval lv2;
			match H.find dadic_actions v2.vname with DLower(i,span_exps)-> (
				(match level with 0 ->
				let Some etype = Lidoutil.get_pointed_type v2.vtype (succ i) in
				let petype = TPtr(etype,[]) in
        let dim = gen_dim_exp (A.to_list span_exps) etype in 
				let hd' = Call(Some lv,Lval(Var v,NoOffset),[dim],loc) in
				let hd2' = Set((Var(v2),NoOffset),CastE(petype,Lval lv),loc2) in
				v2.vtype<-petype;
				Some [mkStmt(Instr [hd';hd2'])]
				|_-> E.log "del stmt of %s\nlval %a\n" v2.vname d_plainlval lv2;(Some ([]:stmt list)))
			) |_-> None
		with Not_found -> None
	)
	|_->assert false

let calc_index transpose_actions dadic_actions indices arr_exps vi =
	let idxs = transpose_dims transpose_actions dadic_actions indices vi.vname in
  let exps = transpose_dims transpose_actions dadic_actions 
    (A.to_list arr_exps) vi.vname in
	let exps' = if L.length exps > L.length idxs then (E.log "calc_index shorten\n";last_n exps (L.length idxs)) else exps in
  let new_idx = gen_index idxs exps' in
  E.log "idx new\n%a\n" d_plainexp new_idx;
	BinOp(IndexPI,Lval(Var vi,NoOffset),new_idx,uintType)
	(*mkAddrOf (Var vi,Index(new_idx,NoOffset))*)
(*  E.log "current base %a\n" d_plainexp !base;
  let res = BinOp(IndexPI,Lval(Var vi,NoOffset),new_idx,uintType) in
	match sym_diff res !base with Some diff -> BinOp(IndexPI,!base,diff,uintType)
	| None -> base:= res;res*)
class heapifyModifyVisitor_dadic_update_index transpose_actions dadic_actions is_lowest
	(*update the indices after array lowering and transposition*)
      = object(self)
  inherit nopCilVisitor  
	(*method vinst = function (Call(_,Lval(Var vi,NoOffset),exps,_)) as inst ->
			let () = elim_middle<-true in DoChildren
			(*elim_middle <- false;ChangeDoChildrenPost([inst],fun x->elim_middle<-elim_middle_in;x)*)
		|_-> let _ = elim_middle<-elim_middle_in in DoChildren*)
	method vexpr e = match stripAllCasts e with
		|BinOp(IndexPI,Lval l,e3,_)-> (
			let v,level,indices = Lidoutil.varinfo_and_level_of_lval l in
			try
			match H.find dadic_actions v.vname with DLower(i,exps) -> ( 
			match level  with x when (x <> succ i && x<> 0) -> (
			let indices' = indices@[e3] in
      let new_e = calc_index transpose_actions dadic_actions indices' exps v in
			E.log "plus new\n%a\n" d_plainexp new_e;
			ChangeTo(new_e)
			)|_->DoChildren
			)|_->DoChildren
			with Not_found -> DoChildren
		)
		(*|BinOp(Eq,CastE(_,Lval l),e3,_)*)
		|BinOp(Eq,Lval l,e3,_)
		|BinOp(Eq,e3,Lval l,_)-> (
			E.log "equal %a\n" d_plainexp e;
			let v,level,indices = Lidoutil.varinfo_and_level_of_lval l in
			E.log "level %d\n" level;
			if H.mem dadic_actions v.vname then 
				match level  with 0 -> (
				E.log "do it\n";
				ChangeTo(integer 0)
				)|_->DoChildren
			else DoChildren
		)
		| Lval l -> (
	  match l with 
	(*as we use ChangeTo, we are at the top level of a nested indirect reference*)
    | lv,ofst -> (
	try (
		let v,level,indices = Lidoutil.varinfo_and_level_of_lval l in
		match H.find dadic_actions v.vname with DLower(i,exps) -> ( 
		(match level  with x when (x = succ i)  -> ( (* a for a[][]*)
			E.log "arr\n%a\n" d_plainlval l;
      let new_e = calc_index transpose_actions dadic_actions  indices exps v in
			let new_lval = Mem new_e,NoOffset (*match new_e with AddrOf x -> x |_->assert false*) in 
			E.log "arr new\n%a\n" d_plainlval new_lval;
			ChangeTo (Lval new_lval))
			|0 -> DoChildren
			|_-> 
				let indices' = if is_lowest then indices else indices@(L.map (fun x-> zero) (range (A.length exps - L.length indices))) in
				let new_e = calc_index transpose_actions dadic_actions indices' exps v in 
				E.log "no such dim level %d\n%a\n" level d_plainlval l;
				E.log "no such dim level typ %a\n" d_plaintype (typeOf (stripNopCasts e));
				(match typeOf (stripNopCasts e) with TPtr _ -> ChangeTo new_e (*(AddrOf (Mem new_e,NoOffset))*)
				|_ -> ChangeTo (Lval (Mem new_e,NoOffset)))
			(*|_->
				if elim_middle  then 
					(E.log "no such dim level %d\n%a\n" level d_plainlval l;ChangeTo(AddrOf l))
				else DoChildren*)
		)) |_-> DoChildren
		) with Not_found -> DoChildren
	)
	)
		|_->DoChildren
  (*| _ -> DoChildren *)
end
class collect_call_actuals graph call_actuals = object(self) inherit nopCilVisitor 
	method vinst = function (Call(_,Lval(Var vi,NoOffset),exps,_))->
		H.add call_actuals vi.vname exps;
		SkipChildren
	|_-> SkipChildren
end
let rec actual_base_name = 
	function Lval lv |StartOf lv |AddrOf lv |BinOp(IndexPI,Lval lv,_,_)
		-> let vi,_,_ = Lidoutil.varinfo_and_level_of_lval lv in 
		E.log "actual_base_name %s\n" vi.vname;vi.vname
	|Lval(Mem (BinOp(IndexPI,base,_,_)),_) -> actual_base_name base
	|x-> E.log "actual_base_name err %a\n" d_plainexp x;""
let flatten_pointer_ty ty = 
	let rec flatten_pointer_ty' = function TPtr(ty,_) -> flatten_pointer_ty' ty | x -> x in
	TPtr(flatten_pointer_ty' ty,[])
(*class modify_callee_array call_actuals dadic_actions = object(self) inherit nopCilVisitor          *)
(*  method vglob gl =                                                                                *)
(*  match gl with                                                                                    *)
(*  | GFun(fundec,funloc) -> (                                                                       *)
(*		let name = fundec.svar.vname in                                                                *)
(*		try let actuals_list = H.find_all call_actuals name in                                         *)
(*			if L.length actuals_list =1 then ( (*simple minded, really should check if constant actuals*)*)
(*				let actuals = L.hd actuals_list in                                                         *)
(*					let mydadic_actions = H.create 30 in                                                     *)
(*					let formals' = A.of_list fundec.sformals in                                              *)
(*					A.iteri (fun i a -> try let act = H.find dadic_actions (actual_base_name a) in           *)
(*						H.replace mydadic_actions (L.nth fundec.sformals i).vname act;                         *)
(*						formals'.(i).vtype <- flatten_pointer_ty formals'.(i).vtype                            *)
(*						with Not_found -> E.log "%s not found\n" (actual_base_name a);()) (A.of_list actuals); *)
(*						E.log "modify_callee_array mydadic_actions size %d\n" (H.length mydadic_actions);      *)
(*						fundec.sbody <-                                                                        *)
(*							(visitCilBlock (new heapifyModifyVisitor_dadic_update_index mydadic_actions true)    *)
(*							fundec.sbody);                                                                       *)
(*						setFormals fundec (A.to_list formals');                                                *)
(*						ChangeTo([GFun(fundec,funloc)])                                                        *)
(*			) else SkipChildren                                                                          *)
(*		with Not_found -> SkipChildren)                                                                *)
(*  | _ -> SkipChildren                                                                              *)
(*end                                                                                                *)


(* peel
	1. create extra variables (only suport global) and build peel_varinfo_map as in heapifyModifyVisitor_peel_add_gloal_vars
	2. add alloc's for new vars as in peel_trans
	3. update peeled field access
	4. update the struct type as in heapifyModifyVisitor_peel_type
*)
let (peel_actions:(varinfo*string,varinfo) H.t) = H.create 20
let get_peeled_varinfo orig_var field_name = try H.find peel_actions (orig_var,field_name)
	with Not_found -> assert false

class activeStructureVisitor activeStructures = object inherit nopCilVisitor
    method voffs off = match off with
      | Field (fi, _) ->
        Hashtbl.replace activeStructures fi.fcomp ();
        DoChildren
      | _ -> DoChildren
end

let getActiveStructures (f:file) =
  let activeStructures = Hashtbl.create 3 in
  visitCilFileSameGlobals (new activeStructureVisitor activeStructures) f;
  ExtHashtbl.keys activeStructures 

let (peel_type_map:(string,string list) H.t) = let h = H.create 20 in 
(*	H.add h "__anonstruct_f1_neuron_19" ["W";"X";"V";"U";"P";"Q";"R";"I"];*)
	(*H.add h "node_t" ["W";"X";"V";"U";"P";"Q";"R";"I"];*)
	h

let preparePeelActiveStructures (f:file) =
  let activeStructures = getActiveStructures f in
  let field_names ci = List.map (fun fi -> fi.fname) ci.cfields in
  List.iter (fun ci -> Hashtbl.add peel_type_map ci.cname (field_names ci)) 
    @$ List.filter (fun ci -> List.length ci.cfields > 7) (*TODO: can we relax this*) 
    @$ activeStructures

let get_pointed_type_name ty = match unrollType ty with
    | TPtr(TNamed(ti,_),_) -> 
			(match ti.ttype with TComp(ci,_)-> ci.cname | _->"")
		| x-> E.log "get_pointed_type_name %a\n" d_plaintype x;""

let peeled_new_globals = ref VS.empty

class heapifyModifyVisitor_peel_add_gloal_vars = object inherit nopCilVisitor 
  method vglob gl = 
	match gl with
	| GVarDecl (vi,loc)
	| GVar (vi,_,loc) -> (
	try
		(*E.log "ti type %s\n" (match ti.ttype with TComp(ci,_)-> ci.cname);*)
		match unrollType vi.vtype with TPtr(TNamed({ttype=TComp(ci,_)},_),_) -> (
		let peel_fields = H.find peel_type_map ci.cname in
	  let new_global_vis = L.map (fun vname -> 
			let fi = getCompField ci vname in
			let f_vi = makeGlobalVar (vi.vname^"_"^vname) (TPtr(fi.ftype,[])) in 
			H.replace peel_actions (vi,fi.fname) f_vi;f_vi) peel_fields
		in
    List.iter (fun vi -> peeled_new_globals := VS.add vi !peeled_new_globals) 
        new_global_vis;
	  let new_globals = L.map (fun vi ->GVarDecl (vi,loc)) new_global_vis in
	  E.log "old gvar: %a\n" d_global gl;
	  E.log "gvar: %a\n" d_global (L.hd new_globals);
		ChangeTo(gl::new_globals)
		)|_->DoChildren
 	with Not_found -> DoChildren
	)
	|_->DoChildren
end
let create_malloc malloc_v size_exp fundec =
	let temp = makeTempVar fundec voidPtrType in
	temp,mkStmt(Instr [Call(Some(Var temp,NoOffset),Lval(Var malloc_v,NoOffset),[size_exp],locUnknown)])

let rec exp_sum = function hd::tl -> exp_add hd (exp_sum tl)
	| [] -> zero
let exp_partial_sum exps = let rexps = L.rev exps in
	let rec exp_partial_sum' = function hd::tl -> let s_tl = exp_partial_sum' tl in 
		(exp_add (L.hd s_tl) hd)::s_tl
		|[]-> [zero] in
	L.rev (exp_partial_sum' rexps)
let peel_trans = fun fundec -> 
		function [Call(Some lv,Lval(Var v,NoOffset),exps,loc) as hd;(Set(lv2,exp2,loc2) as hd2)] ->( 
		try 
			match lv2 with Var vi2,NoOffset ->(
			match unrollType vi2.vtype with TPtr(TNamed({ttype=TComp(ci,_)},_),_) -> (
			let peel_fields = H.find peel_type_map ci.cname in
			let f_vis = L.map (fun fname -> H.find peel_actions (vi2,fname)) peel_fields in 
			assert (v.vname = "malloc");
			(*we layout the peel'ed fields continuously to lessen cache conflict*)
			let cnt_exp = extract_cnt lv2 exps v.vname in
			let exps = L.map (fun vi -> SizeOf (fromSome (Lidoutil.get_pointed_type vi.vtype 1))) f_vis in
			let size_exps = L.map (exp_mult cnt_exp) exps in
			let assign_fields = L.map2 (fun vi size_exp -> 
			let temp = makeTempVar fundec (TPtr(TVoid [],[])) in
			mkStmt(Instr [Call(Some(Var temp,NoOffset),Lval(Var v,NoOffset),[size_exp],loc);
					Set((Var vi,NoOffset),Lval (Var temp,NoOffset),loc)])	
			) f_vis size_exps in
			let struct_residue_mallocs = 
				(
(*          if L.length peel_fields = L.length ci.cfields then [] else *)
          [mkStmt(Instr [hd;hd2])]) in
			Some (assign_fields@struct_residue_mallocs)
			) |_-> None
			) |_-> None
		with Not_found -> None
	)
	|_->assert false

class heapifyModifyVisitor_update_peel_field (*update fields in the peel list*)
   peel_actions = object(self)
  inherit nopCilVisitor  
  method vlval l = match l with
  | Mem(BinOp(op,Lval(Var vi,NoOffset),idx,typ)), Field (fi,ofst) ->
	(try 
	let f_vi = H.find peel_actions (vi,fi.fname) in
	let new_lval = Mem(BinOp(op,Lval(Var f_vi,NoOffset),idx,f_vi.vtype)),NoOffset in
	ChangeDoChildrenPost(new_lval, (fun l -> l))
	with Not_found -> DoChildren)
  | _ -> DoChildren (* ignore other lvalues *)
end

class heapifyModifyVisitor_peel_type peel_type_map = object inherit nopCilVisitor 
  method vglob gl = 
	match gl with
  | GCompTag (ci, loc) -> (
	try
		let peel_fields = H.find peel_type_map ci.cname in
		let aux_fields,major_fields = L.partition (fun fi -> L.mem fi.fname peel_fields ) ci.cfields in
		(
(*      match major_fields with [] -> ChangeTo([])*)
(*		|_->                                        *)
      ci.cfields <- major_fields; ChangeTo([GCompTag(ci,loc)]))
	with Not_found -> DoChildren
	)
	|_->DoChildren
end

(* discover reuse pairs *)
 
class checkReuse arrs (conflicts:(varinfo,VS.t) Hashtbl.t) : cilVisitor = 
  object(self) inherit nopCilVisitor
    method vstmt stm = 
(*      E.log "%d LIVES\n" (VS.cardinal (Lidoutil.ArrayLiveness.getStmLiveSet stm));*)
(*      E.log "size of lv is %d\n" (VS.cardinal (getStmLiveSet stm));*)
(*    VS.iter (fun e -> E.log "checkReuse:%s %d\n" e.vname e.vid) (getStmLiveSet stm);*)
      let ls = VS.inter arrs (Lidoutil.ArrayLiveness.getStmLiveSet stm) in
      VS.iter (fun e -> 
          let vs =  
            VS.remove e 
          (VS.union (try Hashtbl.find conflicts e with Not_found -> VS.empty) ls) in
           if vs != VS.empty then Hashtbl.replace conflicts e vs
        ) ls;
      DoChildren
end
 
let findReuses arrs (fil:file) =
  let allocLenSet = ref VS.empty in
  visitCilFileSameGlobals (new Lidoutil.allocLenVisitor allocLenSet) fil;
  E.log "allocLenSet:";
  VS.iter (fun vi -> E.log "%s " vi.vname) !allocLenSet;
  E.log "\n";
(*  computeGlobalFileCFG fil;*)
(*  Lidoutil.globlArrReadWrite fil;*)
  VS.iter (fun vi -> E.log "arrs: %s -> %d\n" vi.vname vi.vid) arrs;
  let conflicts = Hashtbl.create 3 in

  let funs = List.map (fun _f ->
(*        Lidoutil.doOneInstrFun @$*)
        Lidoutil.cfgPrune !allocLenSet @$
        copyFunction _f (_f.svar.vname^"_") 
    ) @$ Lidoutil.getFunctions fil in
  let funs' = Lidoutil.GlobalCFG.computeGlobalCFG funs in
  Lidoutil.ArrayLiveness.computeLivenessFuns funs';
(*  List.iter (fun f -> dumpGlobal defaultCilPrinter stdout (GFun(f,locUnknown))) funs';*)
  List.iter (fun f -> ignore (visitCilFunction (new checkReuse arrs conflicts) f)) funs';
  E.log "checkReuse done\n";
  
  Hashtbl.iter (fun k v -> 
    E.log "conflicts: %d => " k.vid; 
    VS.iter (fun e -> E.log "%d "e.vid) v;
    E.log "\n") conflicts;
  let replaceTable = Hashtbl.create 3 in
  let reduce vs conflicts replaceTable =
    let toSet = Hashtbl.create 3 in
    let getSet k =
      try Hashtbl.find toSet k
      with Not_found ->
        let r = VS.singleton k in
        Hashtbl.replace toSet k r;
        r in
    let join vi vi' =
      let ns = VS.union (getSet vi) (getSet vi') in
      Hashtbl.replace toSet vi ns;
      Hashtbl.replace toSet vi' ns
      in
    let hasConflict vi vi' =
      let s,s' = getSet vi,getSet vi' in
      VS.exists (fun vi ->
        not @$ VS.is_empty @$
        VS.inter
            (try Hashtbl.find conflicts vi
            with Not_found -> VS.empty)
            s'
        ) s in 
    VS.iter (fun vi ->
      VS.iter (fun vi' ->
        if not (hasConflict vi vi') then
          join vi vi'
        ) vs
      ) vs;
    Hashtbl.iter (fun k v ->
      let v' = VS.choose v in
      if v'.vid != k.vid then
          Hashtbl.replace replaceTable k v') toSet
  in
  let arrs = Lidoutil.set_of_list @$ ExtHashtbl.keys conflicts in (*TODO:*)
  reduce arrs conflicts replaceTable;
  Hashtbl.iter (fun k v -> E.log "replaceTable : %s => %s\n" k.vname v.vname) replaceTable;
  replaceTable

(*LITA stands for Linked lIst To Array: a global array-based linked list can be made an array. pointer become indices. resever index 0 for null-pointer*)
(* 1. find the base pointer for a type. create a global base_pointer
   2. update pointers to be indices.
	 3. modify the pointer fields in the struct.
   4. peel the new struct array.
*)
let lita_actions = let h = H.create 30 in 
	H.replace h "node_t" None;
	h
exception Not_named_pointer
let get_deref_ty_name = function TPtr(TNamed(ti,_),_) -> ti.tname
	|_->raise Not_named_pointer
let lita_interesting_ty ty = 
	try H.mem lita_actions (get_deref_ty_name ty)
	with not_named_pointer -> false
let typedef_name =  let h = H.create 30 in 
	H.replace h "node" "node_t";
	h
let lita_interesting_ci ci = 
	try H.mem lita_actions (H.find typedef_name ci.cname)
	with Not_found -> false
let lita_new_bases = H.create 30
class lita_tran = object(self)
  inherit nopCilVisitor  
	method vlval = function Mem addr,off when lita_interesting_ty (typeOf addr) ->
		E.log "lita: found pointer %a\n" d_plainexp addr;
		let name = get_deref_ty_name (typeOf addr) in
		E.log "lita: name %s\n" name;
		(match H.find lita_actions name with Some base ->
			let base_e = Lval(var base) in
			ChangeDoChildrenPost((Mem(BinOp(IndexPI,base_e,addr,typeOf base_e)),off),fun x->x)
		|_-> E.log "None\n";assert false)
	|_->DoChildren
(*	method vexpr e =
		if lita_interesting_ty (typeOf e) then
			let name = get_deref_ty_name (typeOf e) in
			E.log "lita: name %s\n" name;
			(match H.find lita_actions name with Some base ->
(*				(match e with BinOp(IndexPI,Lval(Var base2,NoOffset),_,_) when base2.vid <> base.vid ->
					let base_e = Lval(var base) in
					let idx = BinOp(MinusPP,e,base_e,uintType) in
					ChangeDoChildrenPost(BinOp(IndexPI,base_e,idx,typeOf base_e),fun x->x)
				|_->SkipChildren)*)
				(match e with BinOp(IndexPI,Lval(Var base2,NoOffset),_,_) when base2.vid <> base.vid ->
					let base_e = Lval(var base) in
					let idx = BinOp(MinusPP,e,base_e,uintType) in
					ChangeTo(BinOp(IndexPI,base_e,idx,typeOf base_e))
				|_->SkipChildren)
			|_-> E.log "None\n";assert false)
		else DoChildren
*)
	method vglob = function GCompTag(ci,loc) when lita_interesting_ci ci ->
			E.log "lita: %s\n" ci.cname;
			(*L.iter (fun fi -> if lita_interesting_ty fi.ftype then fi.ftype <- uintType) ci.cfields;*)
			DoChildren
		| GType (ti,loc) as gl when H.mem lita_actions ti.tname -> 
			let new_decls = try [GVarDecl(H.find lita_new_bases ti.tname,locUnknown)] with Not_found -> [] in
			ChangeTo([gl]@new_decls)
		|_-> DoChildren
end
let lita_find_base_trans = 
	function [Call(Some lv,Lval(Var vi,NoOffset),exps,loc);Set(lv2,exp2,loc2)] as insts ->
		let ty = typeOfLval lv2 in
		if lita_interesting_ty ty then (
			let tname = get_deref_ty_name ty in
			let base = makeGlobalVar (tname^"_global_base") ty in
			let alloc_base = Set(var base,exp2,loc2) in
			H.replace lita_new_bases tname base;
			H.replace lita_actions tname (Some base);
			Some [mkStmt(Instr (insts@[alloc_base]))])
		else None
	|_->None
(*recognize dotproduct*)
let doublepointerType = TPtr(doubleType,[])

let recog_one_d_array = 
	function Lval(Mem(BinOp(IndexPI,Lval base,Lval(Var idx_vi,NoOffset),_)),NoOffset) ->
		Some(Lval base,idx_vi)
	| Lval(Mem(BinOp(IndexPI,Lval base,BinOp(PlusA,off,Lval(Var idx_vi,NoOffset),_),ty)),NoOffset) ->
		Some(BinOp(IndexPI,Lval base,off,ty),idx_vi)
	| _->None
let dotproduct_recog_trans dotproduct_call_vi (stm1,stm2) = match get_loop_struct (stm1,stm2) with Some ls-> (
		match ls.body with [{skind=Instr [Set(lval,exp,loc)]}] -> (
			if not (exp_refer_vi (Lval lval) ls.vi) then
				match exp with BinOp(PlusA,Lval lval,BinOp(Mult,exp1,exp2,_),_)
					|BinOp(PlusA,BinOp(Mult,exp1,exp2,_),Lval lval,_) ->
						E.log "exp1,exp2: %a\n %a\n" d_plainexp exp1 d_plainexp exp2;
						(match recog_one_d_array exp1,recog_one_d_array exp2 with 
							Some(base,idx_vi),Some(base2,idx_vi2) 
								when idx_vi.vid = ls.vi.vid && idx_vi2.vid = ls.vi.vid ->
									Some[stm1;mkStmtOneInstr(Call(Some lval, Lval(var dotproduct_call_vi),[
										base;base2;BinOp(MinusA,ls.upper,ls.lower,uintType)],locUnknown));
										mkStmtOneInstr(Set(var ls.vi,ls.upper,locUnknown))]
							|_->None)
					| _->None
			else None
		) |_-> None
		)
	|None -> assert false	
class dotproduct_recog dotproduct_call_vi = object(self) inherit nopCilVisitor
	method vblock blk = 
	match loop_triger (dotproduct_recog_trans dotproduct_call_vi) false blk.bstmts with Some res -> 
		ChangeTo {blk with bstmts=res}
	|None -> DoChildren
end

(*inlining*)
let (to_inline:(string,fundec option) H.t) = let h = H.create 20 in 
	(*H.add h "smvp" None;*)
	h 

class heapifyModifyVisitor_mod_inlinee vi_exp_map break_out_stmt ret = object inherit nopCilVisitor 
  method vlval lv = (*replace formal args*)
	match lv with Var vi,NoOffset -> (
	try
		let exp = L.assoc vi vi_exp_map in
		(match stripNopCasts exp with Lval lv2 ->	ChangeTo(lv2)
		|BinOp(IndexPI,base,idx,_)  -> ChangeTo (Mem exp,NoOffset)
		|_->E.log "heapifyModifyVisitor_instantiate_args %a\n" d_plainexp exp;assert false
		)
	with Not_found -> DoChildren
	)
	|_->DoChildren

	method vstmt s = 
	match s.skind with Return(eo,loc) -> (
		match eo,ret with Some e,Some lval -> 
			ChangeTo(mkStmt(Block(mkBlock([mkStmtOneInstr(Set(lval,e,loc));
				mkStmt(Goto (ref break_out_stmt,loc))]))))
		|None,None -> ChangeTo(mkStmt(Goto (ref break_out_stmt,loc)))
		|_->assert false
	)
	|_-> DoChildren
end

let inline_trans = fun fundec -> 
	function [Call (ret_val, Lval(Var(v),NoOffset), exps,loc)] ->
		let inliner_name = fundec.svar.vname in
  	let inlinee = copyFunction
			(match H.find to_inline v.vname with Some x -> x | _-> failwith "no fundec") "" in
		let vi_exp_map = L.combine inlinee.sformals exps in
		let break_out_stmt = 
			{(mkEmptyStmt()) with labels = [Label((sprintf "exit_%s_%d" inliner_name loc.line),loc,false)]} in
		let _ = inlinee.sbody <- 
			visitCilBlock (new heapifyModifyVisitor_mod_inlinee vi_exp_map break_out_stmt ret_val) inlinee.sbody in
		L.iter (fun vi -> vi.vname <- sprintf "%s_%d" vi.vname loc.line) inlinee.slocals;
		fundec.slocals <-fundec.slocals @ inlinee.slocals;
		Some [mkStmt(Block inlinee.sbody);break_out_stmt]
	|_->assert false
let handle_inline_is_interesting = 
	function [Call (_, Lval(Var(v),NoOffset), exps,loc)] -> H.mem to_inline v.vname
					|_->false
let handle_inline trans = visitCilBlock (new heapifyModifyVisitor handle_inline_is_interesting 1 trans)

class heapifyModifyVisitor_remove_uncalled graph
     = object(self) inherit nopCilVisitor 
  method vglob gl = 
  match gl with
  | GFun(fundec,funloc) ->
		let name = fundec.svar.vname in
		if name <> "main" && IH.length (H.find graph name).cnCallers=0 then(
			E.log "del uncalled %s\n" name;
    	ChangeTo([])
		)
		else SkipChildren
  | _ -> DoChildren
end

class heapifyModifyVisitor_inliner 
     = object(self) inherit nopCilVisitor 
  method vglob gl = 
  match gl with
  | GFun(fundec,funloc) ->
   	fundec.sbody <- handle_inline (inline_trans fundec) fundec.sbody;
    ChangeTo([GFun(fundec,funloc)])
  | _ -> DoChildren
end

class heapifyAnalyzeVisitor_inliner (*collect the inlinee's body*)
     = object(self) inherit nopCilVisitor 
  method vglob gl = 
  match gl with
  | GFun(fundec,funloc) ->
  	if H.mem to_inline fundec.svar.vname then 
			H.replace to_inline fundec.svar.vname (Some (fundec));
		SkipChildren
  | _ -> DoChildren
end
class heapifyAnalyzeVisitor4 transpose_actions dadic_actions f= object 
  inherit nopCilVisitor 
  method vglob gl = (*E.log "global:\n%a\n" d_shortglobal gl;*) match gl with
    GFun(fundec,funloc) -> 
		fundec.sbody <-
      visitCilBlock (new heapifyModifyVisitor_dadic_update_index transpose_actions dadic_actions false)
					(handle_alloc (dadic_alloc_trans dadic_actions) fundec.sbody);
        ChangeTo([GFun(fundec,funloc)])
		|_->DoChildren
end
(*put in different passes to ensure order*)
class heapifyAnalyzeVisitor3 transpose_actions dadic_actions f= object 
  inherit nopCilVisitor 
  method vglob gl = (*E.log "global:\n%a\n" d_shortglobal gl;*) match gl with
    GFun(fundec,funloc) -> 
		fundec.sbody <- (
						(handle_alloc (dadic_get_dim_trans dadic_actions))
			 )fundec.sbody;
        ChangeTo([GFun(fundec,funloc)])
		|_->DoChildren
end
class heapifyAnalyzeVisitor2 f= object 
  inherit nopCilVisitor 
  method vglob gl = (*E.log "global:\n%a\n" d_shortglobal gl;*) match gl with
    GFun(fundec,funloc) -> 
		fundec.sbody <-
						visitCilBlock (new heapifyModifyVisitor_update_peel_field peel_actions) @$
           handle_alloc (peel_trans fundec) @$ 
           visitCilBlock (new heapifyModifyVisitor_replace_field replace_table) @$
           fundec.sbody;
        ChangeTo([GFun(fundec,funloc)])
		|_->DoChildren
end

class heapifyAnalyzeVisitor f= object 
  inherit nopCilVisitor
  method vglob gl = (*E.log "global:\n%a\n" d_shortglobal gl;*) match gl with
    GFun(fundec,funloc) -> 
		fundec.sbody <- (
						(visitCilBlock (new heapifyModifyVisitor_del_field del_field_table f))>>
(*						(visitCilBlock (new heapifyModifyVisitor_replace_field reuse_table))>>*)
						(visitCilBlock (new heapifyModifyVisitor_del_lhs replace_table))
						) fundec.sbody;

        ChangeTo([GFun(fundec,funloc)])
		|_->DoChildren
end

(*let till_nochange_merge_loop f =
	let changed = ref true in
	while !changed do
		changed := false;
		f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_loop )) f.globals);
	done
	*)
let exist_indirect h =
	let is_indirect = function NIIndirect _ -> true |_->false in
	H.fold (fun k d v -> is_indirect d.cnInfo || v) h false
  
class replaceVariableModifier replaceTable =
  object inherit nopCilVisitor
  method vvrbl vi =
    if Hashtbl.mem replaceTable vi then
      ChangeTo (Hashtbl.find replaceTable vi) else SkipChildren 
  end
  
let heapify (f : file) (alloc : exp) (free : exp)  =
	(*  visitCilFile (new heapifyModifyVisitor_remove_uncalled graph) f;*)
  let globalReadWrites = ref [] in 
  visitCilFile (new Lidoutil.globlReadVisitor globalReadWrites) f;
  let toKill =
    let h = ExtHashtbl.of_list @$ !globalReadWrites in
    HashSet.of_list @$
        List.filter (fun (v,i) -> ExtList.all id @$ 
        List.map (fun e -> e<=i) @$ Hashtbl.find_all h v) @$
        List.concat @$
        List.filter (function [_] -> true | _ -> false) @$
            ExtList.group @$ List.sort Pervasives.compare !globalReadWrites in
  f.globals <- L.flatten (L.map (visitCilGlobal (new globlDSEVisitor toKill)) f.globals);
  visitCilFile (new gwVisitorClass) f;
	E.log "gwVisitorClass complete\n";
  f.globals <- L.flatten (L.map (visitCilGlobal (new gwModifyClass)) f.globals);
	visitCilFile (new heapifyAnalyzeVisitor_find_pure_call) f;
	H.iter (fun k _ -> E.log "pure call: %s\n" k) pure_calls;
  visitCilFile (new heapifyAnalyzeVisitor_inliner) f;
  visitCilFile (new heapifyModifyVisitor_inliner) f; 
	L.iter (function GFun(fundec,_) -> 
			fundec.sbody <- (handle_alloc (lita_find_base_trans) fundec.sbody)
		|_-> ()) f.globals;
	f.globals <- L.flatten (L.map (visitCilGlobal (new lita_tran)) f.globals);
	Lidoutil.till_nochange_clean_block_file f;
	E.log "inline done\n";
  
  if !doStructPeel then (
    preparePeelActiveStructures f;
	   f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_peel_add_gloal_vars)) f.globals);
    );
  visitCilFile (new heapifyAnalyzeVisitor f) f;
  visitCilFile (new heapifyAnalyzeVisitor2 f) f;
  if !doStructPeel then (
	  let replaceTable = findReuses !peeled_new_globals f in
	  visitCilFile (new replaceVariableModifier replaceTable) f);
  if !swapAndCollapseFloatArray then (
  let transpose_actions,dadic_actions = collectMultiArray f in
  visitCilFile (new heapifyAnalyzeVisitor3 transpose_actions dadic_actions f) f;
  visitCilFile (new heapifyAnalyzeVisitor4 transpose_actions dadic_actions f) f);
(*  iterFunctions (findReuses !peeled_new_globals) f;*)
(*	let graph:callgraph = computeGraph f in*)
(*	if not (exist_indirect graph) then (                                   *)
(*		let call_actuals = H.create 30 in                                    *)
(*	  visitCilFile (new collect_call_actuals graph call_actuals) f;        *)
(*	  visitCilFile (new modify_callee_array call_actuals dadic_actions) f);*)
	f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_peel_type peel_type_map)) f.globals);
	f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_loop_reduce)) f.globals);
	f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_regroup_array f)) f.globals);
	(*f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_simplify_index)) f.globals);*)
	Cfg.clearFileCFG f;
  Cfg.computeFileCFG f;
  (*visitCilFile (new heapifyAnalyzeVisitor_loop) f;*)
  if !mergeLoop then
	   f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_loop )) f.globals);
	f.globals <- L.flatten (L.map (visitCilGlobal (new heapifyModifyVisitor_lift_pure_call)) f.globals);
	f.globals <- L.flatten (L.map (visitCilGlobal (new modifier_merge_insts)) f.globals);
	f.globals <- L.flatten (L.map (visitCilGlobal (new modifier_kernel_misc_opt f)) f.globals);
  if !recogDotProduct then begin
		let ty = TFun(doubleType,Some ["a",doublepointerType,[];
				"b",doublepointerType,[];"len",uintType,[]],false,[]) in
		let dotproduct_call_vi = makeGlobalVar "dotproduct" ty in
		f.globals <- (*GText dotproduct_text::*) GVarDecl(dotproduct_call_vi,locUnknown)::
			(L.flatten (L.map (visitCilGlobal (new dotproduct_recog dotproduct_call_vi)) f.globals));
  end;
	Lidoutil.till_nochange_clean_block_file f;
  f

(* heapify code ends here *)

let default_heapify (f : file) =
  let alloc_fun = emptyFunction "malloc" in
  let free_fun = emptyFunction "free" in
  let alloc_exp = (Lval((Var(alloc_fun.svar)),NoOffset)) in
  let free_exp = (Lval((Var(free_fun.svar)),NoOffset)) in
  ignore (heapify f alloc_exp free_exp);
    
(* StackGuard clone *)

class sgModifyVisitor restore_ra_stmt = object
	inherit nopCilVisitor
  method vstmt s = match s.skind with (* also rewrite the return *)
    Return(_,loc) -> let new_block = mkBlock [restore_ra_stmt ; s] in 
			ChangeTo(mkStmt (Block(new_block)))  
	| _ -> DoChildren (* ignore other statements *)
end

class sgAnalyzeVisitor f push pop get_ra set_ra = object
  inherit nopCilVisitor
  method vfunc fundec = 
    let needs_guarding = List.fold_left 
	(fun acc vi -> acc || containsArray vi.vtype) 
	false fundec.slocals in
    if needs_guarding then begin
      let ra_tmp = makeLocalVar fundec "return_address" voidPtrType in
      let ra_exp = Lval(Var(ra_tmp),NoOffset) in 
      let save_ra_stmt = mkStmt (* save the current return address *)
	  (Instr [Call(Some(Var(ra_tmp),NoOffset), get_ra, [], locUnknown) ;
		   Call(None, push, [ra_exp], locUnknown)]) in
      let restore_ra_stmt = mkStmt (* restore the old return address *)
	  (Instr [Call(Some(Var(ra_tmp),NoOffset), pop, [], locUnknown) ;
		   Call(None, set_ra, [ra_exp], locUnknown)]) in
      let modify = new sgModifyVisitor restore_ra_stmt in
      fundec.sbody <- visitCilBlock modify fundec.sbody ;
      fundec.sbody.bstmts <- save_ra_stmt :: fundec.sbody.bstmts ;
      ChangeTo(fundec)  (* done! *)
    end else DoChildren
end
          
let stackguard (f : file) (push : exp) (pop : exp) 
    (get_ra : exp) (set_ra : exp) = 
  visitCilFileSameGlobals (new sgAnalyzeVisitor f push pop get_ra set_ra) f;
  f
    (* stackguard code ends *)
    
let default_stackguard (f : file) =
  let expify fundec = Lval(Var(fundec.svar),NoOffset) in
  let push = expify (emptyFunction "stackguard_push") in
  let pop = expify (emptyFunction "stackguard_pop") in
  let get_ra = expify (emptyFunction "stackguard_get_ra") in
  let set_ra = expify (emptyFunction "stackguard_set_ra") in
  let global_decl = 
"extern void * stackguard_get_ra();
extern void stackguard_set_ra(void *new_ra);
/* You must provide an implementation for functions that get and set the
 * return address. Such code is unfortunately architecture specific.
 */
struct stackguard_stack {
  void * data;
  struct stackguard_stack * next;
} * stackguard_stack;

void stackguard_push(void *ra) {
  void * old = stackguard_stack;
  stackguard_stack = (struct stackguard_stack *)
    malloc(sizeof(stackguard_stack));
  stackguard_stack->data = ra;
  stackguard_stack->next = old;
}

void * stackguard_pop() {
  void * ret = stackguard_stack->data;
  void * next = stackguard_stack->next;
  free(stackguard_stack);
  stackguard_stack->next = next;
  return ret;
}" in
    f.globals <- GText(global_decl) :: f.globals ;
    ignore (stackguard f push pop get_ra set_ra )
      
      
let feature1 : featureDescr = 
  { fd_name = "stackGuard";
    fd_enabled = Cilutil.doStackGuard;
    fd_description = "instrument function calls and returns to maintain a\n\t\t\t\tseparate stack for return addresses" ;
    fd_extraopt = [];
    fd_doit = (function (f: file) -> default_stackguard f);
    fd_post_check = true;
  } 
let feature2 : featureDescr = 
  { fd_name = "heapify";
    fd_enabled = Cilutil.doHeapify;
    fd_description = "move stack-allocated arrays to the heap" ;
    fd_extraopt = [
      "--heapifyAll", Arg.Set heapifyNonArrays,
      " When using heapify, move all local vars whose address is taken,\n\t\t\t\tnot just arrays.";
      "--recogDotProduct", Arg.Set recogDotProduct,
      " Whether to recognize dot products of double float and turn them into calls to library functions.";
      "--doStructPeel",  Arg.Set doStructPeel,
      " Peel active structures.";
      "--assumeFieldsEqual",  Arg.String (fun s ->
            let [a;b;c] = ExtString.splitChar s '-' in
            H.add replace_table (a,b) c),
      " Assume the given fields are always equal.";
      "--swapAndCollapseFloatArray", Arg.Set swapAndCollapseFloatArray,
      " Whether to swap and collapse dimensions of float arrays.";
      "--mergeLoop", Arg.Set mergeLoop,
      " Merge loops (experimental).";
      "--assumeDistinct", Arg.String (fun s -> assumeDistinct := s),
      " Ignore the dependency caused by global variable of given name.";
    ];
    fd_doit = (function (f: file) -> default_heapify f);
    fd_post_check = true;
  } 
      





