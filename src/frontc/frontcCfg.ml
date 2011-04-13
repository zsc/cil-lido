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

(*open Graph.Pack.Digraph*)
(*module G = Graph*)
(*open Graph                                                                       *)
(*module G = Imperative.Graph.AbstractLabeled (struct type t = string end) (struct *)
(*  type t = cabsloc                                                               *)
(*  let compare = compare                                                          *)
(*  let hash = Hashtbl.hash                                                        *)
(*  let equal = (=)                                                                *)
(*  let default = locUnknown                                                       *)
(*  end)                                                                           *)

(*let g = create ()*)
class iterGlobalVisitor f = object
    inherit nopCabsVisitor
    method vdef def = f def;SkipChildren 
end
let iterGlobals f cabs = visitCabsFile (new iterGlobalVisitor f) cabs
(*                                                              *)
(*let buildFunLocTable cabs =                                   *)
(*  let funLocTable = ref [] in                                 *)
(*  ignore (iterGlobals                                         *)
(*    (function                                                 *)
(*      | FUNDEF ((spec,name),blk,loc,loc')->                   *)
(*        addRefList (show_plain_cabs_name name,loc) funLocTable*)
(*      | _ -> ())                                              *)
(*    cabs);                                                    *)
(*  HashMap.of_list @$ !funLocTable                             *)
type ambiguity = UnkownCall of cabsloc    

(*class controlFlowGraphVisitor cfg funLocTable ambs = object                                       *)
(*    inherit nopCabsVisitor                                                                        *)
(*    val curFun = ref ""                                                                           *)
(*    val curLoc = ref locUnknown                                                                   *)
(*    method vexpr exp = match exp with                                                             *)
(*      | CALL(VARIABLE v,_) ->                                                                     *)
(*        let e = G.E.create (G.V.create !curFun) !curLoc (G.V.create v) in                         *)
(*        G.add_edge_e cfg e;                                                                       *)
(*(*        (try G.add_edge cfg (G.V.create !curLoc) (G.V.create (Hashtbl.find funLocTable v))*)    *)
(*(*        with Not_found -> addRefList (UnkownCall !curLoc) ambs);                          *)    *)
(*        DoChildren                                                                                *)
(*      | _ -> DoChildren                                                                           *)
(*    method vstmt stmt =                                                                           *)
(*      curLoc := locOfStmt stmt;                                                                   *)
(*      DoChildren                                                                                  *)
(*    method vdef = function                                                                        *)
(*      | FUNDEF ((spec,name),blk,loc,loc')-> curFun := show_plain_cabs_name name;DoChildren        *)
(*      | _ -> DoChildren                                                                           *)
(*end                                                                                               *)
(*                                                                                                  *)
(*module Display = struct                                                                           *)
(*  include G                                                                                       *)
(*(*  let vertex_name v = "\"" ^ String.escaped (show_cabsloc @$ V.label v) ^ "\""*)                *)
(*  let vertex_name v = "\"" ^ String.escaped (V.label v) ^ "\""                                    *)
(*  let graph_attributes _ = []                                                                     *)
(*  let default_vertex_attributes _ = []                                                            *)
(*  let vertex_attributes _ = []                                                                    *)
(*  let default_edge_attributes _ = []                                                              *)
(*  let edge_attributes _ = []                                                                      *)
(*  let get_subgraph _ = None                                                                       *)
(*end                                                                                               *)
(*module DotOutput = Graphviz.Dot(Display)                                                          *)
(*                                                                                                  *)
(*let buildControlFlowGraph cabs =                                                                  *)
(*  let cfg = G.create () in                                                                        *)
(*  let ambs = ref [] in                                                                            *)
(*  let cabs' = visitCabsFile (new controlFlowGraphVisitor cfg (buildFunLocTable cabs) ambs) cabs in*)
(*  let oc = open_out "tmp.dot" in                                                                  *)
(*(*  let oc = stdout in*)                                                                          *)
(*  DotOutput.output_graph oc cfg;                                                                  *)
(*  cabs'                                                                                           *)
  