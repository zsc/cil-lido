open Linda
open Cil
open Lidoutil
module E = Errormsg
open Linda

class findCallee fundec callRelations = object inherit nopCilVisitor
method vinst inst = match inst with
  | Call (_,Lval (Var vi,NoOffset),_,_) ->
    addRefList (fundec.svar.vname,vi.vname) callRelations;
    SkipChildren
  | Call _ ->
    E.log "[findCallee]:%a\n" d_plaininstr inst;
    SkipChildren
  | _ -> SkipChildren

end

class buildCallGraph callRelations = object inherit nopCilVisitor
method vglob glob = match glob with
  | GFun(fundec,_) 
(*  when List.mem "Status" (List.map (fun vi -> vi.vname) fundec.sformals) *)
  ->
    let callRelations' = ref [] in
    ignore @$ visitCilFunction (new findCallee fundec callRelations') fundec;
    callRelations := !callRelations' @ !callRelations;
    SkipChildren
  | _ -> SkipChildren  
end   

let rev_hashmap h =
  let h' = HashMap.create 3 in
  Hashtbl.iter (fun k v -> HashMap.set h' v k) h;
  h'

let toOrderList l =
  let h = HashMap.create 3 in
  let cnt = ref 0 in
  let add e = try ignore (HashMap.get h e) with Not_found -> HashMap.set h e !cnt;incr cnt in
  List.iter (fun (a,b) -> add a;add b) l;
  let s = HashSet.create 3 in
  List.iter (fun (a,b) -> HashSet.add s (HashMap.get h a,HashMap.get h b)) l;
  HashSet.to_list s,rev_hashmap h

let to_list h =
  let l = ref [] in
  Hashtbl.iter (fun k v -> addRefList (k,v) l) h;
  !l

let transitiveClosure l =
  let h = Hashtbl.create 3 in
  let add (a,b) =
    HashMap.set h a @$ IntSet.add b (try HashMap.get h a with Not_found-> IntSet.empty) in   
  List.iter add l; 
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun k v ->
      let k_succs = HashMap.get h k in
      let s = IntSet.diff v k_succs in
      if not @$ IntSet.is_empty s then begin
        IntSet.iter (fun v -> add (k,v)) s;
        changed := true
      end) h
    done;
  h

let elements assocList = 
  let l = ref [] in
  List.iter (fun (a,b) -> addRefList a l;addRefList b l) assocList;
  !l

let testDag f =
  let callRelations = ref [] in
  visitCilFile (new buildCallGraph callRelations) f;
  print_endline @$ show_list ~sep:"\n" (show_pair id id) !callRelations;
  let orders, table = toOrderList !callRelations in
  begin
	  match PartialOrder.TransitiveClosure.ofPartialOrder @$ PartialOrder.of_list @$ orders 
	     with
	    | Some _ -> print_endline "verified to be a DAG"
	    | None -> print_endline "not DAG"
  end;
  let tc = transitiveClosure orders in
  let recs = List.filter 
    (fun k -> not @$ 
      try not @$ IntSet.mem k @$ HashMap.get tc k 
      with Not_found -> true) @$ elements orders in
  List.iter (fun k -> Printf.printf "rec:%s\n" @$ Hashtbl.find table k) @$ ExtList.nub recs; 
  f    

let matcher vname' =
  let vname = "Status" in
  ExtString.endsWith ~needle:vname vname' && vname' <> "RgnStatus" 

class replaceDeref vname vi' = object inherit nopCilVisitor
method vfunc fundec =
  fundec.slocals <- List.filter (fun vi -> vname <> vi.vname) fundec.slocals;
  fundec.sformals <- List.filter (fun vi -> not @$ matcher vi.vname) fundec.sformals;
  DoChildren   
method vlval = function
  | Mem(Lval(Var vi,NoOffset)),NoOffset when matcher vi.vname->
    ChangeTo (Var vi',NoOffset)
  | _ -> DoChildren
method vtype = function
  | TFun (t,Some l,b,al) ->
    ChangeTo (TFun (t,Some (List.filter (fun (n,_,_) -> not @$ matcher n) l),b,al))
  | _ -> DoChildren
end
class clean vname = object inherit nopCilVisitor
method vinst = function
  | Call (lvo,e,es,loc) ->
    let es' = List.filter (function 
      | CastE (_,Lval (Var vi,NoOffset))
      | CastE (_,AddrOf (Var vi,NoOffset))
      | AddrOf (Var vi,NoOffset)
      | Lval (Var vi,NoOffset) -> not @$ matcher vi.vname 
      | _ -> true) es in
    ChangeTo [Call(lvo,e,es',loc)]
  | _ -> SkipChildren
  end  
let promoteVar vname f =
  let new_vi = makeGlobalVar vname (TInt(IInt,[])) in
  visitCilFile (new replaceDeref vname new_vi) f;
  visitCilFile (new clean vname) f;
  f.globals <- GVar (new_vi,dummyInitinfo,locUnknown) :: f.globals;
  f
  
let trans = 
  promoteVar "Status"
(*  testDag  *)