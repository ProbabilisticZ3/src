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
open PrismModelEncoding
open ExpressionEncodings
open Cubes
open Paths
open CounterExamples
open CubeEncoding
open AnalyzerContexts
open AnalyzerContextEncodings
open TacticUtils

module Tactics_Monolythic =
    
    
    // new version of the relevancy check, set to replace the other one once it works
    let encodeRelevancyCheck (ac:AnalyzerContext) (bitSel:BitSelector) (inGoalAtStep:int) : BoolExpr = 
        let co = ac.co
        
        let bmcFun : FuncDecl = co.z3.MkFuncDecl("existsPath_noFinalCondition", Array.ofList << List.concat <| (relevantRandomVarsSorts ac @ relevantSysStateVarsSorts ac), co.z3.MkBoolSort())
        let bmcFunctionDefinition : BoolExpr = 
            upcast co.z3.MkForall 
                (List.toArray (List.concat <| relevantRandomVars ac @ relevantSysStateVars ac), 
                co.z3.MkEq(co.z3.MkApp(bmcFun, Array.ofList << List.concat <| relevantRandomVars ac @ relevantSysStateVars ac),
                    z3mkAnd co.z3
                        [
                        initialCondition co ;
//                        ac.PrecomputedZ3Objects.InitialCondition ;
                        allStepsTransitionRelation co ac.CurrentStepBound ;
                        allStepsFormulaConstraints co ac.CurrentStepBound ;
    //                        finalCondition co; // is taken care of externally
                        noDeadlock co ac.CurrentStepBound ;
                        variableRangesAllSteps co ac.CurrentStepBound ; 
                        excludeConcreteCubes ac ac.PositiveCubes ;
                        ]))

        // Be in the final region for the specified step. Encapsulated in a function to apply it also at the copied variables
        let goalRegionFun = co.z3.MkFuncDecl("finalCondition", Array.ofList co.sysStateArgsSorts, co.z3.MkBoolSort())
        let goalRegionFunctionDefinition : BoolExpr = 
            upcast co.z3.MkForall 
                (List.toArray co.sysStateArgs, 
                co.z3.MkEq(
                    co.z3.MkApp(goalRegionFun, Array.ofList co.sysStateArgs),
                    finalCondition co None))

        // create new copy of state variables and random variables
        let copyOfRandomVars = 
            List.map 
                (List.map
                    (fun (constant:Expr) -> // this expression is a simple constant
                        let name = constant.FuncDecl.Name.ToString() + "_relevancy_copy"
                        co.z3.MkConst(name, constant.Sort)))
            <| relevantRandomVars ac

        let copyOfSysStateVars = 
            List.map
                (List.map
                    (fun (constant:Expr) -> // this expression is a simple constant
                        let name = constant.FuncDecl.Name.ToString() + "_relevancy_copy"
                        co.z3.MkConst(name, constant.Sort)))
            <| relevantSysStateVars ac

        // Both paths have same random variables except for the specified position. 
        let equalityConstraints : BoolExpr = 
            z3mkAnd co.z3
            << List.collect
                (fun (rvars:Expr list, rvarscopy: Expr list, step:int) -> 
                    List.map
                        (fun (v:Expr option, vcopy:Expr option,(m:PrismModule,moduleNumber:int)) -> 
                            if v.IsNone 
                            then co.z3.MkTrue()
                            else
                                downcast co.z3.MkITE(
                                    // if
                                    z3mkAnd co.z3 [
                                        co.z3.MkEq(bitSel.StepSelector,co.z3.MkBV(step,co.stepBVSize));
                                        co.z3.MkEq(bitSel.ModuleSelector,co.z3.MkBV(moduleNumber,co.moduleNumberBVSize))], 
                                    // then
                                    z3mkAnd co.z3
                                    << List.map
                                        (fun (position:int) ->
                                            downcast co.z3.MkITE(
                                                // if
                                                co.z3.MkEq(bitSel.PosSelector,co.z3.MkBV(position,co.positionBVSize)),
                                                // then
                                                co.z3.MkNot
                                                <| co.z3.MkEq(
                                                    co.z3.MkExtract(uint32 position,uint32 position,downcast v.Value),
                                                    co.z3.MkExtract(uint32 position,uint32 position,downcast vcopy.Value)),
                                                // else
                                                co.z3.MkEq(
                                                    co.z3.MkExtract(uint32 position,uint32 position,downcast v.Value),
                                                    co.z3.MkExtract(uint32 position,uint32 position,downcast vcopy.Value))
                                                ))
                                    <| [0.. (Convert.ToInt32 co.randomBVSize)-1],
                                    // else 
                                    co.z3.MkEq(v.Value,vcopy.Value)
                                    ))
                    << List.zip3 
                        (matchRandomVariablesToModules co rvars co.prismModel.Modules)
                        (matchRandomVariablesToModules co rvarscopy co.prismModel.Modules)
                    << List.zip co.prismModel.Modules
                    <| [0..co.prismModel.Modules.Length-1]
                )
            << List.zip3 (relevantRandomVars ac) copyOfRandomVars
            <| [0..ac.CurrentStepBound-1]

        // exclude previously found bits: 
        let excludedBits : BoolExpr = 
            z3mkAnd co.z3
            << List.map
               (fun (relStep:int,relMod:int,relPos:int)->
                    co.z3.MkNot
                    <| z3mkAnd co.z3 [
                        co.z3.MkEq(bitSel.StepSelector,co.z3.MkBV(relStep,co.stepBVSize));
                        co.z3.MkEq(bitSel.ModuleSelector,co.z3.MkBV(relMod,co.moduleNumberBVSize))
                        co.z3.MkEq(bitSel.PosSelector,co.z3.MkBV(relPos,co.positionBVSize))])
            << Set.toList 
            <| ac.RelevantBits

        z3mkAnd co.z3 [
            bmcFunctionDefinition ; 
            goalRegionFunctionDefinition ; 
            equalityConstraints ; 
            excludedBits ;
            downcast co.z3.MkApp(bmcFun,Array.ofList << List.concat <| relevantRandomVars ac @ relevantSysStateVars ac) ;
            downcast co.z3.MkApp(bmcFun,Array.ofList << List.concat <| copyOfRandomVars @ copyOfSysStateVars) ;
            downcast co.z3.MkApp(goalRegionFun, Array.ofList (List.nth co.sysStateVars inGoalAtStep)) ;
            downcast co.z3.MkApp(goalRegionFun, Array.ofList (List.nth copyOfSysStateVars inGoalAtStep)) |> co.z3.MkNot // assert that one is reaching the goal region, but the other isn't
            ]



    let encodeDistributionCheck (ac:AnalyzerContext) : BoolExpr = 
        let co = ac.co
        let z3 = co.z3
        // This is the core of our solver
        upcast z3.MkForall
            (List.toArray (List.concat <| relevantRandomVars ac @ relevantSysStateVars ac), 
            z3.MkImplies(
                z3.MkAnd(Array.ofList
                    [downcast z3.MkApp(co.distributions.Item (ac.CurrentStepBound-1), Array.ofList << List.concat <| relevantRandomVars ac);
                    initialCondition co ;
//                    ac.PrecomputedZ3Objects.InitialCondition;
                    allStepsTransitionRelation co ac.CurrentStepBound;
                    allStepsFormulaConstraints co ac.CurrentStepBound ;
                    variableRangesAllSteps co ac.CurrentStepBound; // no need to check this, because of initial condition, the transition relation, and the variableBounds statement in the right side of the implication; but improves performance
                    ]), 
                z3.MkAnd(Array.ofList
                    [finalCondition co (Some ac.CurrentStepBound);
                    noDeadlock co ac.CurrentStepBound;
                    variableRangesAllSteps co ac.CurrentStepBound; 
                    ])))


                    
    // This function defines the variables that will make the cube and 
    let findCube (ac:AnalyzerContext) (cubeSize:int) : ConcreteCube option = 
        report_0 5 "Searching for a candidate cube."
        let stopWatch = Stopwatch.StartNew()
        let (cube,cubeConstraints) = createCube ac.co cubeSize

        let additionalCubeConstriants = 
            z3mkAnd ac.co.z3
            << List.collect 
                (fun (bs:BitSelector, _) -> encodeBitRelevancy ac bs :: encodeStepBound ac bs :: []) 
            <| cube

        let distributionCheck = encodeDistributionCheck ac

        let positiveCheckOptimization : BoolExpr = 
            if   ac.co.problem.configs.IntegratedPositiveChecks // we do positive BMC checks, and we fix the free positions to 0. 
            then encodeIntegratedPositiveChecks ac cube false
            else ac.co.z3.MkTrue()

        let constraints : BoolExpr list = 
                [
                distributionCheck ;
                cubeConstraints ;
//                positiveCheckOptimization ;
                cubeIsDisjointToOtherCubes ac cube ac.PositiveCubes ;
                excludeIrrelevantBits ac.co ac.IrrelevantBits << List.map fst <| cube ; 
                fuseCubeWithDistribution ac cube ;
                additionalCubeConstriants ;
                ] 
        
        let solver = getFreshSolver ac
        solver.Assert(Array.ofList constraints)
        solver.Assert(modelDefinitions ac.co OVERAPPROX)
        stopWatch.Stop()
        report_1 4 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        report_0 4 "Calling Z3 ..."
        let stopWatch = Stopwatch.StartNew()
        let status = solver.Check()
        stopWatch.Stop()
        report_2 4 "Z3 finished check in %f s: %s" stopWatch.Elapsed.TotalSeconds (status.ToString())
        report_1 4 "%s" (solver.Statistics.ToString())
        try
            match status with
            | Status.SATISFIABLE   -> 
                report_1 2 "Cube of size %d found." cubeSize    
                if reportLevel<=3 then searchAndPrintDistributionFunction solver ac.CurrentStepBound
                let ccube = extractCube solver cube
                Some ccube
            | Status.UNSATISFIABLE -> report_1 5 "No cube of size %d found." cubeSize; None
            | Status.UNKNOWN       -> report_0 5 "Timeout on finding exact distribution function."; None
            | _ -> raise (InnerError "Unexpected value from intermediate analysis.") //; Some ERROR
        finally 
            solver.Dispose()


    let encodeExactDistributionCheck (ac:AnalyzerContext) : BoolExpr = 
        let co = ac.co
        let z3 = co.z3
        upcast z3.MkForall
            (List.toArray (List.concat <| relevantRandomVars ac @ relevantSysStateVars ac), 
            z3.MkImplies(
                z3.MkAnd(
                    [|
                    initialCondition co ;
//                    ac.PrecomputedZ3Objects.InitialCondition ;
                    allStepsTransitionRelation co ac.CurrentStepBound ;
                    allStepsFormulaConstraints co ac.CurrentStepBound ;
                    variableRangesAllSteps co ac.CurrentStepBound ;
                    |]),
                    z3.MkEq(
                        z3.MkAnd(
                            [|
                            noDeadlock co ac.CurrentStepBound ;
                            finalCondition co (Some ac.CurrentStepBound) ;
                            variableRangesAllSteps co ac.CurrentStepBound ;
                            |]), 
                        downcast z3.MkApp(ac.co.distributions.Item (ac.CurrentStepBound-1), Array.ofList << List.concat <| relevantRandomVars ac);
                        ))
                    )

    let findExactDistribution (ac:AnalyzerContext) : unit =
        report_0 5 "Starting search for exact distribution function."
        let stopWatch = Stopwatch.StartNew()
        let distributionConstr : BoolExpr = encodeExactDistributionCheck ac
        let solver = getFreshSolver ac
        solver.Assert(distributionConstr)
        solver.Assert(modelDefinitions ac.co OVERAPPROX)
        stopWatch.Stop()
        report_1 4 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        report_0 4 "Calling Z3 ..."
        let stopWatch = Stopwatch.StartNew()
        let status = solver.Check()
        stopWatch.Stop()
        report_2 4 "Z3 finished check in %f s: %s" stopWatch.Elapsed.TotalSeconds (status.ToString())
        report_1 4 "%s" (solver.Statistics.ToString())
        try
            match status with
            | Status.SATISFIABLE   -> 
                report_0 3 "Distribution function found."
                if reportLevel <= 1 then searchAndPrintDistributionFunction solver ac.CurrentStepBound
                ()
            | Status.UNSATISFIABLE -> report_0 5 "Not distribution function found. This is probably a serious error in the model. "; ()
            | Status.UNKNOWN       -> report_0 5 "Timeout on finding exact distribution function. "; ()
            | _ -> raise (InnerError "Unexpected value from intermediate analysis.") //; Some ERROR
        finally 
            solver.Dispose()

    
    let checkRelevancy (ac:AnalyzerContext) (inGoalAtStep:int) : (int*int*int) option = 
        report_0 4 "Trying to find a relevant bit" 
        let (bitSel:BitSelector,bitSelConstraints) = createBitSelector ac.co 1
        let stopWatch = Stopwatch.StartNew()
        let upperBoundOnStep : BoolExpr = encodeStepBound ac bitSel
        let lowerBoundOnBitRelevancy : BoolExpr = encodeBitRelevancy ac bitSel
        
        let checkConstraints = encodeRelevancyCheck ac bitSel inGoalAtStep

        let solver = getFreshSolver ac
        solver.Assert(
            [|
            bitSelConstraints ; 
            checkConstraints ;
            upperBoundOnStep ;
            lowerBoundOnBitRelevancy ;
            |])
        solver.Assert(modelDefinitions ac.co OVERAPPROX)
        stopWatch.Stop()
        report_1 2 "Encoding completed in %f s." stopWatch.Elapsed.TotalSeconds

        report_0 2 "Calling Z3 ..."
        let stopWatch = Stopwatch.StartNew()
        let status = solver.Check()
        stopWatch.Stop()
        report_2 4 "Z3 finished check in %f s: %s" stopWatch.Elapsed.TotalSeconds (status.ToString())
        report_1 2 "%s" (solver.Statistics.ToString())
        try
            match status with
            | Status.SATISFIABLE   -> 
                // Extract the bitSelector.
                let bitVal:BitVecExpr = createBitVal ac.co 1
                let ccube = extractCube solver [(bitSel,bitVal)]
                report_1 4 "Relevancy found a relevant bit: %s " (printConcreteCube_bitSelectorOnly ccube);
                let cbs = (fst (fst ccube).Head)
                Some (cbs.StepSelector.Int,cbs.ModuleSelector.Int,cbs.PosSelector.Int)
            | Status.UNSATISFIABLE -> 
                report_0 4 "Relevancy did not find any valid pair of paths. "; 
                None
            | Status.UNKNOWN       -> 
                report_0 4 "Relevancy unconclusive (timeout). Could not exclude the relevancy."; 
                raise (InnerError "Unexpected value from intermediate analysis.") 
            | _ -> raise (InnerError "Unexpected value from intermediate analysis.") //; Some ERROR
        finally 
            solver.Dispose()
 
