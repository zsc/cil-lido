open Cabs
open Cabsvisit
open List
open Linda
open MaybeMonad
open ExtList
module H = Hashtbl
module E = Errormsg
open Lidoutil

(** Plain printers *)
(*let showLoc {lineno = ln;filename = fn;byteno = bn;ident = id} =  *)
(*  Printf.sprintf "(line:%d,file:%s,byte:%d,ident:%d)" ln fn bn id *)

(* byteno considers header file, lineno not *)
let show_cabsloc cl = Printf.sprintf "%s %d %d\n " cl.filename cl.lineno cl.byteno

(*for i in ['| %s -> "%s"'%(i.strip(),i.strip()) for i in s.split('|')]:print i*)
let show_plain_cabs_binop = function  
| ADD -> "ADD"
| SUB -> "SUB"
| MUL -> "MUL"
| DIV -> "DIV"
| MOD -> "MOD"
| AND -> "AND"
| OR -> "OR"
| BAND -> "BAND"
| BOR -> "BOR"
| XOR -> "XOR"
| SHL -> "SHL"
| SHR -> "SHR"
| EQ -> "EQ"
| NE -> "NE"
| LT -> "LT"
| GT -> "GT"
| LE -> "LE"
| GE -> "GE"
| ASSIGN -> "ASSIGN"
| ADD_ASSIGN -> "ADD_ASSIGN"
| SUB_ASSIGN -> "SUB_ASSIGN"
| MUL_ASSIGN -> "MUL_ASSIGN"
| DIV_ASSIGN -> "DIV_ASSIGN"
| MOD_ASSIGN -> "MOD_ASSIGN"
| BAND_ASSIGN -> "BAND_ASSIGN"
| BOR_ASSIGN -> "BOR_ASSIGN"
| XOR_ASSIGN -> "XOR_ASSIGN"
| SHL_ASSIGN -> "SHL_ASSIGN"
| SHR_ASSIGN -> "SHR_ASSIGN"
  
let rec show_init_expression = function
  | NO_INIT -> "NO_INIT"
  | SINGLE_INIT e -> "SINGLE_INIT(" ^ show_plain_cabs_expression e ^ ")"
  | COMPOUND_INIT _ -> "COMPOUND_INIT"
and show_plain_cabs_expression = function
  | NOTHING -> "NOTHING"
  | UNARY (op,e) -> "UNARY(" ^ show_plain_cabs_expression e ^ ")"
  | LABELADDR s -> "LABELADDR(" ^ s ^ ")"
  | BINARY(op,e,e2) -> "BINARY(" ^ show_plain_cabs_binop op^ "," ^show_plain_cabs_expression_list [e;e2]  ^ ")" 
  | QUESTION(e,e2,e3) -> "QUESTION" ^ show_plain_cabs_expression_list [e;e2;e3] ^ ")"
   (* A CAST can actually be a constructor expression *)
  | CAST ((_,d),ie) -> "CAST(" ^ String.concat "," [show_plain_cabs_decl_type d;show_init_expression ie] ^ ")" 
    (* There is a special form of CALL in which the function called is
       __builtin_va_arg and the second argument is sizeof(T). This 
       should be printed as just T *)
  | CALL (e,es) -> "CALL(" ^ show_plain_cabs_expression_list (e::es)  ^ ")" 
  | COMMA es -> "COMMA(" ^ show_plain_cabs_expression_list es  ^ ")" 
  | CONSTANT _ -> "CONSTANT"
  | PAREN e -> "PAREN("  ^ show_plain_cabs_expression e ^ ")" 
  | VARIABLE s -> "VARIABLE(" ^ s ^ ")"
  | EXPR_SIZEOF e -> "EXPR_SIZEOF(" ^ show_plain_cabs_expression e ^ ")"
  | TYPE_SIZEOF _ -> "TYPE_SIZEOF"
  | EXPR_ALIGNOF e -> "EXPR_ALIGNOF(" ^ show_plain_cabs_expression e ^ ")"
  | TYPE_ALIGNOF _ -> "TYPE_ALIGNOF"
  | INDEX (e,e2) -> "INDEX(" ^ show_plain_cabs_expression_list [e;e2]  ^ ")" 
  | MEMBEROF (e,s) -> "MEMBEROF(" ^ show_plain_cabs_expression e ^ "," ^ s ^ ")"
  | MEMBEROFPTR (e,s) -> "MEMBEROFPTR(" ^ show_plain_cabs_expression e ^ "," ^ s ^ ")"
  | GNU_BODY _ -> "GNU_BODY"
  | EXPR_PATTERN s -> "EXPR_PATTERN(" ^ s ^ ")"
and show_plain_cabs_expression_list l = 
  String.concat "," (map show_plain_cabs_expression l)
and show_plain_cabs_constant = function
  | CONST_INT s -> "CONST_INT(" ^ s ^ ")"
  | CONST_FLOAT s -> "CONST_FLOAT(" ^ s ^ ")"
  | CONST_CHAR _ -> "CONST_CHAR" 
  | CONST_WCHAR _ -> "CONST_WCHAR"
  | CONST_STRING s -> "CONST_STRING(" ^ s ^ ")"
  | CONST_WSTRING _ -> "CONST_WSTRING"
and show_plain_cabs_decl_type = function
 | JUSTBASE -> "JUSTBASE"                               (* Prints the declared name *)
 | PARENTYPE (_,d,_) -> "PARENTYPE("^ show_plain_cabs_decl_type d ^")" 
 | ARRAY (d,_,e) -> "ARRAY("^ show_plain_cabs_decl_type d ^ "," ^ show_plain_cabs_expression e ^")" 
 | PTR (_,d) -> "PTR("^ show_plain_cabs_decl_type d ^")" 
 | PROTO (d,_,_) -> "PROTO("^ show_plain_cabs_decl_type d ^")" 
and show_plain_cabs_for_clause = function
   FC_EXP e -> show_plain_cabs_expression e
 | FC_DECL d -> show_plain_cabs_def d
and show_plain_cabs_block blk =
  "BLOCK(" ^
  String.concat ",\n" blk.blabels ^ "|\n" ^
  String.concat ";\n" (map show_plain_cabs_stmt blk.bstmts) ^ ")"
and show_plain_cabs_stmt = function
   NOP _ -> "NOP"
 | COMPUTATION (e,_) -> "COMPUTATION("^ show_plain_cabs_expression e^")"
 | BLOCK (blk,_) -> "BLOCK("^ show_plain_cabs_block blk^")"
 | SEQUENCE (s,s',_) -> "SEQUENCE(" ^ show_plain_cabs_stmt s ^ ",\n" ^ show_plain_cabs_stmt s' ^ ")"
 | IF (e,s,s',_) -> "IF(" ^ show_plain_cabs_expression e^ ",\n" ^show_plain_cabs_stmt s ^ ",\n" ^ show_plain_cabs_stmt s' ^ ")"
 | WHILE (e,s,_) -> "WHILE(" ^ show_plain_cabs_expression e^ ",\n" ^show_plain_cabs_stmt s ^ ")"
 | DOWHILE (e,s,_) -> "DOWHILE(" ^ show_plain_cabs_expression e^ "," ^show_plain_cabs_stmt s ^ ")"
 | FOR (fc,e,e',s,_) -> "FOR(" ^ show_plain_cabs_for_clause fc^ "," 
    ^show_plain_cabs_expression e ^ ",\n" ^ show_plain_cabs_expression e'^ ",\n" 
    ^show_plain_cabs_stmt s ^ ")"
 | BREAK _ -> "BREAK"
 | CONTINUE _ -> "CONTINUE"
 | RETURN (e,_) -> "RETURN("^ show_plain_cabs_expression e^")"
 | SWITCH (e,s,_) -> "SWITCH(" ^ show_plain_cabs_expression e^ "," ^show_plain_cabs_stmt s ^ ")"
 | CASE (e,s,_) -> "CASE(" ^ show_plain_cabs_expression e^ "," ^show_plain_cabs_stmt s ^ ")"
 | CASERANGE (e,e',s,_) -> "CASERANGE("
    ^show_plain_cabs_expression e ^ "," ^ show_plain_cabs_expression e'^ "," 
    ^show_plain_cabs_stmt s ^ ")"
 | DEFAULT (s,_) -> "DEFAULT("^ show_plain_cabs_stmt s^")"
 | LABEL (str,s,_) -> "LABEL("^ str ^ "," ^ show_plain_cabs_stmt s^")"
 | GOTO (str,_) -> "GOTO(" ^ str ^ ")"
 | COMPGOTO (e,_) -> "COMPGOTO("^ show_plain_cabs_expression e^")"
 | DEFINITION def -> "DEFINITION(" ^ show_plain_cabs_def def ^ ")"

 | ASM _ -> "ASM"
 | _ -> failwith "show_plain_cabs_stmt"
and show_plain_cabs_spec_elem = function
    SpecTypedef -> "SpecTypedef"
  | SpecCV cvspec -> "SpecCV(" ^ show_plain_cabs_cvspec cvspec   ^ ")"          (* const/volatile *)
  | SpecAttr _ -> "SpecAttr"      (* __attribute__ *)
  | SpecStorage storage -> "SpecStorage(" ^ show_plain_cabs_storage storage ^ ")" 
  | SpecInline -> "SpecInline"
  | SpecType typeSpecifier -> "SpecType(" ^ show_plain_cabs_typeSpecifier typeSpecifier ^ ")"
  | SpecPattern string -> "SpecPattern(" ^ string ^ ")"
and show_plain_cabs_typeSpecifier = function (* Merge all specifiers into one type *)
    Tvoid -> "Tvoid"
  | Tchar -> "Tchar"
  | Tshort -> "Tshort"
  | Tint -> "Tint"
  | Tlong -> "Tlong"
  | Tint64 -> "Tint64"
  | Tfloat -> "Tfloat"
  | Tdouble -> "Tdouble"
  | Tsigned -> "Tsigned"
  | Tunsigned -> "Tunsigned"
  | Tnamed s -> "Tnamed(" ^s^ ")"
  (* each of the following three kinds of specifiers contains a field 
   * or item list iff it corresponds to a definition (as opposed to
   * a forward declaration or simple reference to the type); they
   * also have a list of __attribute__s that appeared between the
   * keyword and the type name (definitions only) *)
  | Tstruct (s,_,_) -> "Tstruct(" ^s ^ ")"
  | Tunion (s,_,_) -> "Tunion(" ^s ^ ")"
  | Tenum (s,_,_) -> "Tenum(" ^s ^ ")"
  | TtypeofE e -> "TtypeofE(" ^ show_plain_cabs_expression e ^ ")"
  | TtypeofT _ -> "TtypeofT"
and show_plain_cabs_storage = function
    NO_STORAGE -> "NO_STORAGE" 
    | AUTO -> "AUTO" 
    | STATIC -> "STATIC" 
    | EXTERN -> "EXTERN"
    | REGISTER -> "REGISTER"
and show_plain_cabs_funspec = function 
    INLINE -> "INLINE" 
    | VIRTUAL -> "VIRTUAL" 
    | EXPLICIT -> "EXPLICIT"
and show_plain_cabs_cvspec = function
    CV_CONST -> "CV_CONST" 
    | CV_VOLATILE -> "CV_VOLATILE" 
    | CV_RESTRICT -> "CV_RESTRICT"
and show_plain_cabs_name = function (string , decl_type , attributes , cabsloc) -> string
and show_plain_cabs_init_name = function (name , init_expression) ->
  "(" ^ show_plain_cabs_name name ^ "," ^ show_plain_cabs_init_expression init_expression ^ ")" 
and show_plain_cabs_init_expression = function
  | NO_INIT -> "NO_INIT"
  | SINGLE_INIT expression -> "SINGLE_INIT(" ^ show_plain_cabs_expression expression ^ ")"
  | COMPOUND_INIT _ -> "COMPOUND_INIT"
and show_plain_cabs_single_name = function (specifier,name) -> show_plain_cabs_name name  
and show_plain_cabs_def = function
   FUNDEF ( single_name , block , cabsloc , cabsloc') ->
    "FUNDEF(" ^ show_plain_cabs_single_name single_name ^","^ show_plain_cabs_block block ^")"
 | DECDEF ( init_name_group , cabsloc)         (* global variable(s), or function prototype *)
    -> "DECDEF(" ^ show_plain_cabs_init_name_group init_name_group ^ ")"
 | TYPEDEF ( name_group , cabsloc) -> "TYPEDEF(" ^ show_plain_cabs_name_group name_group ^ ")"
 | ONLYTYPEDEF ( specifier , cabsloc) -> "ONLYTYPEDEF(" ^ show_plain_cabs_specifier specifier^ ")"
 | GLOBASM ( string , cabsloc) -> "GLOBASM(" ^ string ^ ")"
 | PRAGMA ( expression , cabsloc) -> "PRAGMA(" ^ show_plain_cabs_expression expression ^ ")"
 | LINKAGE (string , cabsloc , definitions) (* extern "C" { ... } *)
    -> "LINKAGE(" ^string ^ show_list show_plain_cabs_def definitions ^ ")"
 | _ -> failwith "def"
and show_plain_cabs_name_group = function ( specifier , names) -> show_list show_plain_cabs_name names
(* The optional expression is the bitfield *)
and show_plain_cabs_field_group = function (specifier , neos) -> "field_group"
(* like name_group, except the declared variables are allowed to have initializers *)
(* e.g.: int x=1, y=2; *)
and show_plain_cabs_init_name_group = function (specifier , init_names) ->
  show_list show_plain_cabs_init_name init_names
and show_plain_cabs_specifier spec_elems = show_list show_plain_cabs_spec_elem spec_elems 

(** utility *)

let rec locOfStmt = function
  | NOP cl
  | COMPUTATION (_,cl)
  | BLOCK(_,cl)
  | SEQUENCE(_,_,cl)
  | IF(_,_,_,cl)
  | WHILE(_,_,cl)  
  | DOWHILE(_,_,cl)
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
  | ASM (_,_,_,cl)
  | TRY_EXCEPT (_,_,_,cl)
  | TRY_FINALLY (_,_,cl) -> cl
  | DEFINITION def -> locOfDef def
and locOfDef = function
   FUNDEF (_,_,cabsloc,_)
 | DECDEF (_, cabsloc)        (* global variable(s), or function prototype *)
 | TYPEDEF (_, cabsloc)
 | ONLYTYPEDEF (_, cabsloc)
 | GLOBASM (_,cabsloc)
 | PRAGMA (_, cabsloc)
 | LINKAGE (_,cabsloc,_)
 | TRANSFORMER (_,_, cabsloc)
 (* expression transformer: source and destination *)
 | EXPRTRANSFORMER (_,_, cabsloc) -> cabsloc

(** A visitor that yeilds [num] statements to caller, 
and replaces the matched instructions with received when [transform] returns Some x.*)

class statementStream 
    num
    (transform: statement list-> statement list option) 
  = object(self) inherit nopCabsVisitor
    method vblock blk = 
        let changed = ref false in
        let rec loop stk = function 
          [] -> List.rev stk
        | (x::xs) as l -> begin
            match transform (take num l) with 
                Some x' -> changed:=true;loop (List.rev x'@stk) (drop num l)
                | None -> loop (x::stk) xs
        end in
        let stmts = loop [] blk.bstmts in
        if !changed then ChangeTo {blk with bstmts = stmts} else DoChildren                      
end

let newTemps = ref []
let newTemp =
  let c = ref 0 in
  fun () ->
	  let t = "__temp"^string_of_int (!c) in
    incr c;
	  newTemps := t::!newTemps;
	  t
  
let integer i = CONSTANT (CONST_INT (string_of_int i)) 
let string s = CONSTANT (CONST_STRING s)
    
let mkBlockStmt stmts loc = BLOCK({bstmts = stmts;blabels=[];battrs=[]},loc)
let mkCall v es loc = COMPUTATION(CALL(VARIABLE v,es),loc)
let index e e2 = INDEX(e,e2) 
let var v = VARIABLE v
let assign e e2 loc = COMPUTATION(BINARY(ASSIGN,e,e2),loc) 
let call fn es loc = COMPUTATION(CALL((var fn),es),loc)
let binop op e e' = BINARY(op,e,e')
let addExp = binop ADD
let subExp = binop SUB
let mulExp = binop MUL
let divExp = binop DIV
let incrVar v = assign (var v) (addExp (var v) (integer 1)) 
let mkLoop e init bound stmt loc =
  let cond = BINARY (LT,e,bound) in
  let update = COMPUTATION(UNARY(POSINCR,e),loc) in  
  mkBlockStmt [
  assign e init loc;
  WHILE(cond,mkBlockStmt [stmt;update] loc,loc)
  ] loc
    
let declare_flags_def spec flagVars loc =
    let init_names = map (fun ret -> ((ret,JUSTBASE,[],loc),SINGLE_INIT (integer 0))) flagVars in  
    DECDEF ((spec,init_names),loc)
let declare_flags spec flagVars loc = DEFINITION (declare_flags_def spec flagVars loc)
let declare_spec name spec loc = DEFINITION (DECDEF ((spec,[(name,JUSTBASE,[],loc),NO_INIT]),loc))
let declare_int name loc = declare_spec name [SpecType Tint] loc 

let rec nameOfExp x = match x with
  | VARIABLE v -> v
  | PAREN e -> nameOfExp e
  | CAST (_,SINGLE_INIT(VARIABLE v)) -> v
  | CAST (_,_) -> if !debug then E.log "cast\n";
    if !debug then E.log "plain: %s" (show_plain_cabs_expression x);""
  | _ -> ""

let rec extractLength = function
  | PAREN e -> extractLength e
  | BINARY(MUL,e,TYPE_SIZEOF _)
  | BINARY(MUL,TYPE_SIZEOF _,e) -> extractLength e
  | e -> e

let rec stripCast = function
  | PAREN e -> stripCast e
  | CAST(_,SINGLE_INIT e) -> stripCast e
  | e -> e

class firstDefLoc loc = object
    inherit nopCabsVisitor
    method vdef def = match def with
      | FUNDEF(_,_,loc',_)
      | DECDEF(_,loc') -> loc:=Some loc';SkipChildren
      | _ -> SkipChildren
end

let insertBeforeFirstDef def (fn,defs) =
  let rec loop def defs = match defs with
  | [] -> [def]
  | DECDEF _::_
  | FUNDEF _::_ -> def ::defs
  | x::xs -> x:: loop def xs in 
  fn, (loop def defs)
class insertOnReturn locStmt = object
  inherit nopCabsVisitor
  val vars = ref []
  val curSpec = ref None
  method vdef def = match def with
    | FUNDEF ((spec,_),blk,loc,loc') ->
      vars := [];
      curSpec := Some spec;
      ChangeDoChildrenPost ([def],map (
        function FUNDEF (sn,blk,loc,loc') -> 
          FUNDEF(sn,{blk with bstmts = blk.bstmts @ [locStmt loc']},loc,loc') 
                | x -> x))
    | _ -> SkipChildren
  method vstmt stmt = match stmt with
    | RETURN (e,loc) ->
        ChangeTo (match e with
          | NOTHING | VARIABLE _ -> [locStmt loc;stmt]
          | _ ->
            let ret = "__retvar" in 
            let retDef = declare_spec ret (fromSome !curSpec) loc in
            let compRet = assign (var ret) e loc in
              [mkBlockStmt ([retDef;compRet;locStmt loc;RETURN(var ret,loc)]) loc])
    | _ -> DoChildren
end

class insertOnMainReturnVisitor locStmt = object
    inherit nopCabsVisitor
    method vdef def = match def with
      | FUNDEF ((spec,name),blk,loc,loc') when show_plain_cabs_name name = "main" ->
        ChangeTo (visitCabsDefinition (new insertOnReturn locStmt) def)
(*        ChangeTo ([FUNDEF(sn,{blk with bstmts = blk.bstmts @ [locStmt loc']},loc,loc')]) *)
      | _ -> SkipChildren
end
let insertOnMainReturn stmt cabs =
  visitCabsFile (new insertOnMainReturnVisitor stmt) cabs

let locUnknown = {
  filename = "";
  lineno = -1;
  byteno = -1;
  ident = -1
}          
    
(*open Graph.Pack.Digraph*)
(*module G = Graph*)
(*open Graph                                                                      *)
(*module G = Imperative.Graph.AbstractLabeled(struct type t = cabsloc end) (struct*)
(*  type t = Linda.Algebra.Rational.t                                             *)
(*  let compare = compare                                                         *)
(*  let hash = Hashtbl.hash                                                       *)
(*  let default = Linda.Algebra.Rational.of_int 1                                 *)
(*  end)                                                                          *)

(*let g = create ()*)
class iterGlobalVisitor f = object
    inherit nopCabsVisitor
    method vdef def = f def;SkipChildren 
end
let iterGlobals f cabs = visitCabsFile (new iterGlobalVisitor f) cabs

let buildFunLocTable cabs =
  let funLocTable = ref [] in 
  ignore (iterGlobals
    (function
      | FUNDEF ((spec,name),blk,loc,loc')->
        addRefList (show_plain_cabs_name name,loc) funLocTable
      | _ -> ())
    cabs);
  HashMap.of_list @$ !funLocTable
type ambiguity = UnkownCall of cabsloc    

(*class controlFlowGraphVisitor cfg funLocTable ambs = object                                       *)
(*    inherit nopCabsVisitor                                                                        *)
(*    val curLoc = ref locUnknown                                                                   *)
(*    method vexpr exp = match exp with                                                             *)
(*      | CALL(VARIABLE v,_) ->                                                                     *)
(*        (try G.add_edge cfg (G.V.create !curLoc) (G.V.create (Hashtbl.find funLocTable v))        *)
(*        with Not_found -> addRefList (UnkownCall !curLoc) ambs);                                  *)
(*        DoChildren                                                                                *)
(*      | _ -> DoChildren                                                                           *)
(*    method vstmt stmt =                                                                           *)
(*      curLoc := locOfStmt stmt;                                                                   *)
(*      DoChildren                                                                                  *)
(*end                                                                                               *)
(*                                                                                                  *)
(*module Display = struct                                                                           *)
(*  include G                                                                                       *)
(*  let vertex_name v = "\"" ^ String.escaped (show_cabsloc @$ V.label v) ^ "\""                    *)
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
  