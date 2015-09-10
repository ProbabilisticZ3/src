// MN Rabe

namespace ProbabilisticZ3

open System
open System.Diagnostics
open System.Collections.Generic

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open Problems
open Results
open EncodingContext
open ExpressionEncodings
open Cubes
open Paths
open PathEncodings
open CounterExamples
open CubeEncoding
open AnalyzerContexts
open AnalyzerContextEncodings
open TacticUtils

module Tactics =

    // Calls Z3 with correct timeout and returns AnalyzerContext object 
    // with updated statistics and the time passed in seconds
    let callZ3 (ac:AnalyzerContext) (solver:Solver) : Status = 
        let time_left = int64 ac.co.problem.Timeout - ac.Statistics.Stopwatch.ElapsedMilliseconds
        ac.co.z3.UpdateParamValue("TIMEOUT", time_left.ToString())
        ac.Statistics.QueriesCount <- ac.Statistics.QueriesCount+1
        let st = solver.Check()
        st
        
        

    let findCandidateCube (ac:AnalyzerContext) (cces:ConcreteCCE list) (path:Path) (cubeSize:int) : ConcreteCube option = 
        report_1 4 "Searching for a cube candidate of size: %d" cubeSize    
        let stopWatch = Stopwatch.StartNew()
        let (cube,cubeConstraints) = createCube ac.co cubeSize
        let upperBoundOnSteps : BoolExpr = z3mkAnd ac.co.z3 << List.map (encodeStepBound ac << fst) <| cube

        let otherCubesConstraints : BoolExpr =
            match ac.co.problem.configs.OverlappingCubes with
            | true -> cubeIsNotEqualToOtherCubes ac cube cubeSize ac.PositiveCubes 
            | false -> cubeIsDisjointToOtherCubes ac cube ac.PositiveCubes 

        let pathInCube = rPathIsInCube ac (path2RPath path) cube 
        let pathInCube_simp = downcast pathInCube.Simplify()
        let constraints : BoolExpr list = 
            [
            cubeConstraints ;
            upperBoundOnSteps ;
            cubeDoesNotContainCCEs ac.co cube cces ; 
            otherCubesConstraints ;
            pathInCube_simp ;
            z3mkOr ac.co.z3 // Optional
                [
                noIsolatedLowSignificanceBits ac cube ;
                noIsolatedHighSignificanceBits ac cube ;
                ]
            excludeCECache_cube ac cube ;

            ] 

        let solver = getFreshSolver ac
        solver.Assert(Array.ofList constraints)
        stopWatch.Stop()
        ac.Statistics.EncodingTime <- ac.Statistics.EncodingTime+stopWatch.Elapsed.TotalSeconds
        report_1 3 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        report_0 2 "Calling Z3 ..."
        let stopWatch = Stopwatch.StartNew()
        let status = callZ3 ac solver
        stopWatch.Stop()
        ac.Statistics.CubeCandateSearchTime <- ac.Statistics.CubeCandateSearchTime+stopWatch.Elapsed.TotalSeconds
        report_2 4 "Z3 finished check in %f s: %s" stopWatch.Elapsed.TotalSeconds (status.ToString())
        report_1 2 "%s" (solver.Statistics.ToString())

        try
            match status with
            | Status.SATISFIABLE   -> 
                report_1 2 "Cube candidate of size %d found." cubeSize    
                let ccube = extractCube solver cube
//                if List.exists (fun (ccb:ConcreteBitSelector) -> ccb.StepSelector.Int>0) << List.map fst << fst <| ccube
//                then
//                    report_0 5 "Trolololo"
                Some ccube
            | Status.UNSATISFIABLE -> 
                report_1 4 "No cube of size %d found." cubeSize
                None
            | Status.UNKNOWN       -> 
                report_0 5 "Timeout."
                raise (new TimeoutException())
            | _ -> raise (InnerError "Unexpected value from intermediate analysis.") //; Some ERROR
        finally 
            solver.Dispose()

    let encodeCCESearch_sumEncoding (ac:AnalyzerContext) (path:Path) (cube:ConcreteCube option) (distance:int) : BoolExpr = 
        report_1 3 "Starting check for counter-examples of distance %d." distance
        let stopWatch = Stopwatch.StartNew()

        let cceConstraints : BoolExpr = fusePathWithRandomVars_sumEncoding ac path distance

        let optionalCube : BoolExpr = 
            match cube with 
            | Some cube -> encodeConcreteCube ac.co (relevantRandomVars ac) cube
            | None ->  ac.co.z3.MkTrue() 

        let otherCubesConstraints : BoolExpr = excludeConcreteCubes ac ac.PositiveCubes

        let constraints : BoolExpr = 
            ac.co.z3.MkAnd
                [|
                otherCubesConstraints ;
                optionalCube ;
                excludeEarlyTermination ac ;
                ac.bmcFormula_overApprox_negatedGoal ;
                cceConstraints ;
                |]  
        stopWatch.Stop()
        ac.Statistics.EncodingTime <- ac.Statistics.EncodingTime+stopWatch.Elapsed.TotalSeconds
        report_1 3 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        constraints


    let encodeCCESearch (ac:AnalyzerContext) (path:Path) (cube:ConcreteCube option) (distance:int) : BoolExpr * CloseCounterExample = 
        report_1 3 "Starting check for counter-examples of distance %d." distance
        let stopWatch = Stopwatch.StartNew()

        let (cce : CloseCounterExample, isCCE) = createCloseCE ac.co distance
        let upperBoundOnSteps : BoolExpr = z3mkAnd ac.co.z3 << List.map (encodeStepBound ac) <| cce
        let cceConstraints : BoolExpr = 
            z3mkAnd ac.co.z3
                [
                // Constraints concerning CE:
                isCCE ; 
//                stateBeforeFirstBitSelector ac path cce ;
                (match distance with
                 | 0 -> fusePathWithRandomVars_zeroDistance ac path 
                 | 1 -> fusePathWithRandomVars_singleBitSelector ac path cce.Head 
                 | _ -> fusePathWithRandomVars ac path cce) ;
                excludeIrrelevantBits ac.co ac.IrrelevantBits cce ;
                upperBoundOnSteps ;
                (if ac.co.problem.configs.LocalCCEElimination 
                    then localCCEElimination ac cce
                    else ac.co.z3.MkTrue() )
                ] 

        let optionalCube : BoolExpr = 
            match cube with 
            | Some cube -> encodeConcreteCube ac.co (relevantRandomVars ac) cube
            | None ->  ac.co.z3.MkTrue()
        let otherCubesConstraints : BoolExpr = 
            excludeConcreteCubes ac ac.PositiveCubes
//            match ac.co.problem.configs.OverlappingCubes with
//            | true  -> ac.co.z3.MkTrue()
//            | false -> excludeConcreteCubes ac ac.PositiveCubes

        let constraints : BoolExpr = 
            ac.co.z3.MkAnd
                [|
                otherCubesConstraints ;
                optionalCube ;
                excludeEarlyTermination ac ;
                ac.bmcFormula_overApprox_negatedGoal ;
                cceConstraints ;
                |]  
        stopWatch.Stop()
        ac.Statistics.EncodingTime <- ac.Statistics.EncodingTime+stopWatch.Elapsed.TotalSeconds
        report_1 3 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        (constraints,cce)


    let solveCCESearch (ac:AnalyzerContext) (path:Path) (formula:BoolExpr) (cce:CloseCounterExample option): ConcreteCCE option = 
        let solver = getFreshSolver ac
        solver.Assert(formula)

        report_0 2 "Calling Z3 ..."
        let stopWatch = Stopwatch.StartNew()
        let status = callZ3 ac solver
        stopWatch.Stop()

        ac.Statistics.CCEsSearchTime <- ac.Statistics.CCEsSearchTime+stopWatch.Elapsed.TotalSeconds

        report_2 3 "Z3 finished check in %f s: %s" stopWatch.Elapsed.TotalSeconds (status.ToString())
        report_1 2 "%s" (solver.Statistics.ToString())
        try 
            match status with
            | Status.SATISFIABLE   -> 
                report_0 2 "Path to the goal region exists. " 
                let mutable ccce : ConcreteCCE = 
                    if cce.IsSome 
                    then extractCounterExample solver cce.Value
                    else extractCounterExample_sumEncoding ac solver path 
//                if List.exists (fun (ccb:ConcreteBitSelector) -> ccb.StepSelector.Int>0) ccce
//                then
//                    report_0 5 "Trolololo"
                Some ccce
            | Status.UNSATISFIABLE -> 
                report_0 5 "No counter-example found. "
                None
            | Status.UNKNOWN       -> 
                report_0 5 "Timeout."
                raise (new TimeoutException())
            | _ -> raise (InnerError "Unexpected value from intermediate analysis.") //; Some ERROR
        finally 
            solver.Dispose()



    let listCCEs_sumEncoding ac path (curDistance:int) (maxDistance:int) (maxNum:int) (cube:ConcreteCube option) (otherCCEs:ConcreteCCE list) : ConcreteCCE list =
        let rec listCCEs_internal (curDistance:int) (maxNum:int) (otherCCEs:ConcreteCCE list) (bakedGoal:BoolExpr option) : ConcreteCCE list =
            if maxNum>0
            then
                let f:BoolExpr = 
                    if bakedGoal.IsSome then bakedGoal.Value 
                    else 
                        let f = encodeCCESearch_sumEncoding ac path cube curDistance
                        let noOtherCCEs : BoolExpr list = List.map (excludeOtherCCE_sumEncoding ac.co path) otherCCEs 
                        let f = z3mkAnd ac.co.z3 (f :: noOtherCCEs)
                        let t_ctx_simplify = ac.co.z3.MkTactic("ctx-simplify")
                        let stopWatch = Stopwatch.StartNew()
                        let f_opt = applyTactic ac t_ctx_simplify f
                        stopWatch.Stop()
                        ac.Statistics.SimplifyTime <- ac.Statistics.SimplifyTime+stopWatch.Elapsed.TotalSeconds
                        f_opt
                
                let f = // bake in the new CCE
                    if otherCCEs.IsEmpty then f else 
                    let noOtherCCEs : BoolExpr = excludeOtherCCE_sumEncoding ac.co path otherCCEs.Head
                    let f = ac.co.z3.MkAnd [|f;noOtherCCEs|]
//                    let t_ctx_simplify = ac.co.z3.MkTactic("ctx-simplify")
//                    let stopWatch = Stopwatch.StartNew()
//                    let f_opt = applyTactic ac.co t_ctx_simplify f
//                    stopWatch.Stop()
//                    ac.Statistics.SimplifyTime <- ac.Statistics.SimplifyTime+stopWatch.Elapsed.TotalSeconds
                    f

                let ccce : ConcreteCCE option = solveCCESearch ac path f None
                if ccce.IsSome 
                then
                    report_1 3 "Found close counterexample: %s" 
                        <| String.concat "." (List.map (fun x -> cbsToString x) ccce.Value)
                    ccce.Value :: listCCEs_internal curDistance (maxNum-1) (ccce.Value::otherCCEs) (Some f)
                elif curDistance<maxDistance 
                    then listCCEs_internal (curDistance+1) maxNum otherCCEs None
                    else [] // done
            else [] // done
        listCCEs_internal curDistance maxNum otherCCEs None

    // find close counter-examples
    let listCCEs ac path (curDistance:int) (maxDistance:int) (maxNum:int) (cube:ConcreteCube option) (otherCCEs:ConcreteCCE list) : ConcreteCCE list =
        let rec listCCEs_internal (curDistance:int) (maxNum:int) (otherCCEs:ConcreteCCE list) (bakedGoal:(BoolExpr*CloseCounterExample) option) : ConcreteCCE list =
            if maxNum>0
            then
                let (f:BoolExpr,cce) = 
                    if bakedGoal.IsSome then bakedGoal.Value 
                    else 
                        let (f,cce) = encodeCCESearch ac path cube curDistance
                        let noOtherCCEs : BoolExpr = excludeOtherCCEs ac.co cce otherCCEs 
                        let f = ac.co.z3.MkAnd [|f;noOtherCCEs|]
                        let t_ctx_simplify = ac.co.z3.MkTactic("ctx-simplify")
                        let stopWatch = Stopwatch.StartNew()
                        let f_opt = applyTactic ac t_ctx_simplify f
                        stopWatch.Stop()
                        ac.Statistics.SimplifyTime <- ac.Statistics.SimplifyTime+stopWatch.Elapsed.TotalSeconds
                        (f_opt,cce)
                
                let f = // bake in the new CCE
                    if otherCCEs.IsEmpty then f else 
                    let noOtherCCEs : BoolExpr = excludeOtherCCEs ac.co cce [otherCCEs.Head] 
                    let f = ac.co.z3.MkAnd [|f;noOtherCCEs|]
//                    let t_ctx_simplify = ac.co.z3.MkTactic("ctx-simplify")
//                    let stopWatch = Stopwatch.StartNew()
//                    let f_opt = applyTactic ac.co t_ctx_simplify f
//                    stopWatch.Stop()
//                    ac.Statistics.SimplifyTime <- ac.Statistics.SimplifyTime+stopWatch.Elapsed.TotalSeconds
                    f

                let ccce : ConcreteCCE option = solveCCESearch ac path f (Some cce)
                if ccce.IsSome 
                then
                    report_1 3 "Found close counterexample: %s" 
                        <| String.concat "." (List.map (fun x -> cbsToString x) ccce.Value)
                    ccce.Value :: listCCEs_internal curDistance (maxNum-1) (ccce.Value::otherCCEs) (Some (f,cce))
                elif curDistance<maxDistance 
                    then listCCEs_internal (curDistance+1) maxNum otherCCEs None
                    else [] // done
            else [] // done
        listCCEs_internal curDistance maxNum otherCCEs None



    let findSinglePath 
            (ac:AnalyzerContext) 
            (cube:ConcreteCube option) 
            (invertGoalRegion:bool) 
            (enableEarlyTermination:bool) // If true, we check for reachability in UP TO CurrentStepBound steps. Otherwise, it's exactly CurrentStepBound steps. 
            : Path option = 

        assert(not (invertGoalRegion && enableEarlyTermination))

        report_1 3 "Searching for a path of length %d." ac.CurrentStepBound
        let stopWatch = Stopwatch.StartNew()

        let optionalCube : BoolExpr = 
            match cube with 
            | Some cube -> encodeConcreteCube ac.co (relevantRandomVars ac) cube
            | None ->  ac.co.z3.MkTrue()

//        let goalRegion = 
//            if invertGoalRegion
//            then ac.co.z3.MkNot <| goalRegion ac enableEarlyTermination
//            else goalRegion ac enableEarlyTermination
        let bmc = if invertGoalRegion then ac.bmcFormula_overApprox_negatedGoal else ac.bmcFormula_underApprox

        let constraints : BoolExpr [] = 
            [|
//            ac.PrecomputedZ3Objects.InitialCondition ;
//            allStepsTransitionRelation ac ;
//            variableRangesAllSteps ac ;
//            goalRegion ;
            excludeEarlyTermination ac ; 
//            noDeadlock ac ;
            excludeConcreteCubes ac ac.PositiveCubes ;
            optionalCube ;
            excludeCECache_rvars ac ac.co.randomVars ;
            |] 


        let solver = getFreshSolver ac
//        solver.Assert(modelDefinitions ac.co)
        solver.Assert(bmc)
        solver.Assert(constraints)
        stopWatch.Stop()
        ac.Statistics.EncodingTime <- ac.Statistics.EncodingTime+stopWatch.Elapsed.TotalSeconds
        report_1 3 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        report_0 2 "Calling Z3 ..."
        let stopWatch = Stopwatch.StartNew()
        let status = callZ3 ac solver
        stopWatch.Stop()

        if cube.IsSome 
        then ac.Statistics.CubeCheckSearchTime <- ac.Statistics.CubeCheckSearchTime+stopWatch.Elapsed.TotalSeconds
        else ac.Statistics.PathSearchTime <- ac.Statistics.PathSearchTime+stopWatch.Elapsed.TotalSeconds

        

        report_2 3 "Z3 finished check in %f s: %s" stopWatch.Elapsed.TotalSeconds (status.ToString())
        report_1 2 "%s" (solver.Statistics.ToString())
        try 
            match status with
            | Status.SATISFIABLE   -> 
                report_0 2 "Path to the goal region exists. " 
                let path : Path = extractPath ac solver (relevantRandomVars ac) (relevantSysStateVars ac) 0
                Some path
            | Status.UNSATISFIABLE -> 
                report_0 3 "Path to the goal region does not exist. "
                None
            | Status.UNKNOWN -> 
                report_0 5 "Path to the goal region may exist, but could not find it (timeout)." // Could this have other causes?
                raise (new TimeoutException())
            | _ -> raise (InnerError "Unexpected value from intermediate analysis.") //; Some ERROR
        finally 
            solver.Dispose()

   
//    let checkModelValidity () =
        // 5.4 Check validity of the model
        // 5.4.1 variable bounds
        // 5.4.2 deadlocks
        // 5.4.3 probabilities larger than 1 or smaller than 0 -- rates ...
        // 5.4.4 depending on model type, check for existence of nondeterminism

//    let checkAbstractionQuality () = 
        // 5.5 Determine how much probability mass we are going to loose by approximations