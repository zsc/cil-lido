open Pretty
open Cil

open Linda
open Lidoutil
open Lidostruct
open Lidoarray
module E = Errormsg

(*If multiple names are needed, pass them as comma-seperated list*)
let lidoFormSIMDArray = ref false
let lidoFormSIMDWidth = ref ""
let lidoStructPeel = ref false
let lidoStructPeelNames : string ref = ref ""
let lidoArrayFlatten = ref false 
let lidoArrayFlattenNames : string ref = ref ""  
let lidoArrayTranspose = ref false  
let lidoArrayTransposeNames : string ref = ref ""  
let lidoArrayLift = ref false
let lidoDumpLoops = ref false
let lidoMergeByteOp = ref false
let lidoUnionToStruct = ref false
let lidoDumpStmts = ref false
let lidoDoTest = ref false
let lidoDoVortex = ref false
  
let setAndFill a b = Arg.String (fun s -> a :=  true; b := s)  
  
let lidoPasses (f:file) = ignore (
  f |> guardTrans !lidoStructPeel structTrans
  |> guardTrans (!lidoArrayFlatten || !lidoArrayTranspose) arrayTrans
  |> guardTrans (!lidoDumpLoops) dumpLoops
  |> guardTrans !lidoMergeByteOp MergeByteOp.optimize
  |> guardTrans !lidoUnionToStruct Union2struct.trans
  |> guardTrans !lidoDumpStmts Lidoutil.dumpStmtsOfFile
  |> guardTrans !lidoFormSIMDArray (FormSIMDArray.trans (try int_of_string !lidoFormSIMDWidth with _ -> 64))
  |> guardTrans !GlobalVariableToPointer.enable GlobalVariableToPointer.trans
  |> guardTrans !lidoDoVortex Vortex.trans
  );
  if !lidoDoTest then Lidoutil.doTest f

let feature : featureDescr = 
  { fd_name = "lidomain";              
    fd_enabled = ref false;
    fd_description = "locality inspired data optimizations";
    fd_extraopt = [
      "--lidoFormSIMDArray", setAndFill lidoFormSIMDArray lidoFormSIMDWidth,
      " Form SIMD array."; 
      "--lidoStructPeel", setAndFill lidoStructPeel lidoStructPeelNames,
      " Structure peeling.";
      "--lidoArrayFlatten", setAndFill lidoArrayFlatten lidoArrayFlattenNames,
      " Array falttening.";
      "--lidoArrayTranspose", setAndFill lidoArrayTranspose lidoArrayTransposeNames,
      " Array transposing.";      
      "--lidoArrayLift", Arg.Set lidoArrayLift,
      " Lift stack/heap arrays to global.";
      "--lidoDumpLoops", Arg.Set lidoDumpLoops,
      " Dump all loops's loop_struct.";    
      "--lidoMergeByteOp", Arg.Set lidoMergeByteOp,
      " Merge byte shifting operations to long long operations.";  
      "--lidoUnionToStruct", Arg.Set lidoUnionToStruct,
      " Turn union to struct when type safety implies the fields do not interfere.";  
      
      "--lidoDumpStmts", Arg.Set lidoDumpStmts,
      " Dump all stmts in plain form.";
      "--lidoDoTest", Arg.Set lidoDoTest,
      " For testing.";     
      "--lidoVortex", Arg.Set lidoDoVortex,
      " For testing vortex.";     
      
	    (* BOP stuff *)
	    "--BOPglobalVarToPointer", 
	    Arg.Set GlobalVariableToPointer.enable,
	    " Global var to pointers";                      
      ];
    fd_doit = lidoPasses;
    fd_post_check = true;
  } 