open Linda
open Cil
open Lidoutil
module E = Errormsg

(* let trans x = E.log "here"; x *)

open ExtList
open UnionFind

let equiv h i i' = match i, i' with
  | Set((Var vi,NoOffset), _, _), Set((Var vi',NoOffset), _, _)
  | Call(Some (Var vi,NoOffset), _, _, _), Call(Some (Var vi',NoOffset), _, _, _) ->
    union (HashMap.get h vi.vid) (HashMap.get h vi'.vid)
  | _ -> ()
  
class collectSimilarVar h = object
  inherit nopCilVisitor
  method vstmt stmt = begin match stmt.skind with
      | Instr l -> ignore @$ shrink (equiv h) l
      | _ -> ()
    end;
    DoChildren
end

class similarVar n = object (self)
  inherit nopCilVisitor
  method vfunc f =
    let h = HashMap.of_list @$ map (fun e -> e.vid, uref e) f.slocals in
    ignore @$ visitCilFunction (new collectSimilarVar h) f;
    let vargroups = filter 
      (fun l -> length l >= 4 && length l * sizeOf_int ((hd l).vtype) <= (n / 8)) @$
      classifyBy (fun vi vi' -> equal (HashMap.get h vi.vid) (HashMap.get h vi'.vid) && vi.vtype = vi'.vtype) f.slocals in
    E.log "%s\n" @$ show_list (show_list (fun vi -> vi.vname)) @$ vargroups;
    ChangeTo (foldl (fun f group ->
              let arrVi = makeTempVar f (TArray((hd group).vtype, Some (integer (length group)),[])) in
              foldl (fun f (vi, lv) -> visitCilFunction (new replaceViLvalVisitor vi lv) f) f @$
              mapi (fun i vi -> vi, (Var arrVi, Index (integer i, NoOffset))) group
        ) f vargroups)
end

let trans n file =
  visitCilFile (new similarVar n) file;
  file