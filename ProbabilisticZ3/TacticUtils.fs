
namespace ProbabilisticZ3

open System
open System.Diagnostics
open System.Collections.Generic

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open Problems
open SolverConfigs
open Results
open EncodingContext
open PrismModelEncoding
open ExpressionEncodings
open Cubes
open Paths
open PathEncodings
open CounterExamples
open CubeEncoding
open AnalyzerContexts
open AnalyzerContextEncodings

module TacticUtils = 

    // Use only this method to generate a new solver object.
    let getFreshSolver (ac:AnalyzerContext) : Solver = 
        let z3 = ac.co.z3
        match (ac.co.problem.configs.AnalyzerStrategy,4) with
        | (TacticEvaluation,0) -> 
            z3.MkSolver(z3.UsingParams(z3.MkTactic("ufbv"),z3.MkParams()))
        | (TacticEvaluation,1) -> 
            let parameters = z3.MkParams()
            parameters.Add("local-ctx",true)
            z3.MkSolver(z3.UsingParams(z3.MkTactic("ufbv"),parameters))
        | (TacticEvaluation,2) ->
            let parameters = z3.MkParams()
            parameters.Add("max-depth",uint32 10000)
            let t0 = z3.Then(z3.MkTactic("simplify"), z3.MkTactic("macro-finder")) 
            let t1 = z3.Then(z3.UsingParams(z3.MkTactic("ctx-simplify"),parameters),t0)
            let t = z3.Then(t1,z3.MkTactic("ufbv"))
            t.Solver
        | (TacticEvaluation,3) ->
            let parameters = z3.MkParams()
//            parameters.Add("auto-config",false)
            parameters.Add("mbqi",false)
            parameters.Add("macro-finder",true)
            let t1 = z3.UsingParams(z3.MkTactic("ctx-solver-simplify"),parameters)
//            let t = z3.Then(t1,z3.MkTactic("ufbv"))
            t1.Solver
        | (TacticEvaluation,4) -> 
            let parameters = z3.MkParams()
            parameters.Add("max_steps", (uint32) 50)
            parameters.Add("mbqi",false)
//            Global.SetParameter("verbose", "1")
//            let t0 = z3.Then(z3.MkTactic("simplify"), z3.MkTactic("macro-finder")) 
            let t0 = z3.MkTactic("macro-finder")
            let t1 = z3.Then(t0, z3.UsingParams(z3.MkTactic("ctx-simplify"),parameters))
            let t = z3.Then(t1,z3.MkTactic("ufbv"))
            t.Solver
        | (TacticEvaluation,6) -> 
            let t0 = z3.Then(z3.MkTactic("simplify"), z3.MkTactic("ctx-simplify")) // solve-eqs
            let t1 = z3.Then(t0,z3.MkTactic("symmetry-reduce"))
            let t2 = z3.Then(t1,z3.MkTactic("reduce-bv-size"))
            let t3 = z3.Then(t1,z3.MkTactic("der"))
            let t4 = z3.Repeat(t3,uint32 1000)
            let parameters = z3.MkParams()
//            parameters.Add("blast-full",true)
//            parameters.Add("pull-cheap-ite",true)
//            parameters.Add("cache-all",true)
//            parameters.Add("restart",z3.MkSymbol("geometric"))
//            parameters.Add("restart-factor",1.3)
//            parameters.Add("random-freq",0.05)
            let t = z3.Then(t4,z3.UsingParams(z3.MkTactic("bv"),parameters))
            t.Solver
        | (TacticEvaluation,7) -> // SAT based ... bit-blasting does not work?
            let t0 = z3.Then(z3.MkTactic("simplify"), z3.MkTactic("macro-finder")) 
            let t1 = z3.Then(t0, z3.MkTactic("ctx-simplify")) // solve-eqs
//            let t2 = z3.Then(t1,z3.MkTactic("reduce-bv-size"))
//            let t3 = z3.Then(t2,z3.MkTactic("der"))
            let parameters = z3.MkParams()
            parameters.Add("blast-full",true)
            let t4 = z3.Then(t1,z3.UsingParams(z3.MkTactic("bit-blast"),parameters))
            let t5 = z3.Then(t4,z3.MkTactic("sat-preprocess"))
//            let t6 = z3.Then(t5,z3.MkTactic("ctx-simplify"))
//            let t7 = z3.Then(t6,z3.MkTactic("aig"))
            let t8 = z3.Then(t5,z3.MkTactic("sat"))
            t8.Solver
        | (TacticEvaluation,8) ->     
            let t0 = z3.Then(z3.MkTactic("simplify"), z3.MkTactic("ctx-simplify")) // solve-eqs
            let t1 = z3.Then(t0,z3.MkTactic("symmetry-reduce"))
            let t2 = z3.Then(t1,z3.MkTactic("reduce-bv-size"))
            let parameters = z3.MkParams()
            parameters.Add("split-largest-clause",true)
            let t3 = z3.Then(t2,z3.UsingParams(z3.MkTactic("split-clause"),parameters))
            let t = z3.Repeat(t3)
            t.Solver
        | _ -> 
            let p1 = z3.MkParams()
            p1.Add("max_steps", (uint32) 50)
            // p1.Add("mbqi",false)
//            let t0 = z3.MkTactic("macro-finder")
            let t1 = z3.UsingParams(z3.MkTactic("ctx-simplify"),p1)
            let p2 = z3.MkParams()
            // p2.Add("learned",true)
            // p2.Add("aig-per-assertion",false)
//            p2.Add("local-ctx",true)
//            p2.Add("local-ctx-limit", (uint32) 100)
//            p2.Add("resolution", false)
            let t = z3.UsingParams(z3.Then(t1,z3.MkTactic("ufbv")),p2)
            t.Solver


    let encodeBitRelevancy (ac:AnalyzerContext) (bs:BitSelector) : BoolExpr = 
        let co = ac.co
        let minPosition : BitVecExpr = upcast co.z3.MkBV(co.randomBVSize - uint32(ac.BitRelevancy), co.positionBVSize)
        co.z3.MkBVUGE(bs.PosSelector, minPosition)

    let encodeStepBound (ac:AnalyzerContext) (bs:BitSelector) : BoolExpr = 
        let co = ac.co
        let stepMax:BitVecExpr = upcast co.z3.MkBV(ac.CurrentStepBound-1, co.stepBVSize)
        co.z3.MkBVULE(bs.StepSelector, stepMax)


    let searchAndPrintDistributionFunction (solver:Solver) (step:int) = 
        // generate output on the distribution function found
        let distribution_decl = 
            List.find
                (fun (d:FuncDecl) -> 
                    let sym = d.Name
                    match sym with 
                    | :? StringSymbol as ssym -> 
                        // true // set true for displaying all functions of the model
                        ssym.String.Contains ("distribution_step_" + step.ToString())
                        // not (ssym.String.Contains "strategy")
                        //distribution_step_4
                    | _ -> false)
            <| Array.toList solver.Model.FuncDecls 
        report_2 4 "%s\r\n%s" (distribution_decl.Name.ToString()) (solver.Model.FuncInterp(distribution_decl).ToString()) 


    let noIsolatedLowSignificanceBits (ac:AnalyzerContext) (cube:Cube) : BoolExpr = 
        if not ac.co.problem.configs.NoIsolatedLowSignificanceBits then ac.co.z3.MkTrue() else
        let z3 = ac.co.z3
        let rec cmp (bss:BitSelector list) : BoolExpr list = 
            match bss with
            | bs1::bs2::rest -> 
                z3.MkOr(
                    z3.MkEq(bs1.PosSelector,z3.MkBV(ac.co.problem.fractionsEncoding-1,ac.co.positionBVSize)),
                    z3mkAnd z3 
                        [
                        z3.MkEq(bs1.StepSelector,bs2.StepSelector) ;
                        z3.MkEq(bs1.ModuleSelector,bs2.ModuleSelector) ;
                        z3.MkEq(bs2.PosSelector,z3.MkBVAdd(bs1.PosSelector,z3.MkBV(1,ac.co.positionBVSize))) ;
                        ]
                    ) :: cmp (bs2::rest)
            | _ -> []
        z3mkAnd z3 << cmp << List.map fst <| cube

    let noIsolatedHighSignificanceBits (ac:AnalyzerContext) (cube:Cube) : BoolExpr = 
        if not ac.co.problem.configs.NoIsolatedLowSignificanceBits then ac.co.z3.MkTrue() else
        let z3 = ac.co.z3
        let rec cmp (bss:BitSelector list) : BoolExpr list = 
            match bss with
            | bs1::bs2::rest -> 
                z3.MkOr(
                    z3.MkEq(bs2.PosSelector,z3.MkBV(0,ac.co.positionBVSize)),
                    z3mkAnd z3 
                        [
                        z3.MkEq(bs1.StepSelector,bs2.StepSelector) ;
                        z3.MkEq(bs1.ModuleSelector,bs2.ModuleSelector) ;
                        z3.MkEq(bs1.PosSelector,z3.MkBVSub(bs2.PosSelector,z3.MkBV(1,ac.co.positionBVSize))) ;
                        ]
                    ) :: cmp (bs2::rest)
            | _ -> []
        z3mkAnd z3 << cmp << List.map fst <| cube



    let localCCEElimination (ac:AnalyzerContext) (cce:CloseCounterExample) : BoolExpr =
        let co = ac.co
        let z3 = co.z3
        let res = 
            z3mkAnd z3
            << List.mapi //             (fun (step:int) (rvars:Expr list,nextSysStateVars_thisStep : Expr list) -> 
                (fun (step:int) 
                      (randomVars:Expr list, 
                       (sysStateVars:Expr list, nextSysStateVars:Expr list, 
                        (formulaVars:Expr list, 
                         (syncGuardVars:Expr list,pChoiceVars)))) -> 
                    let (rvar_alt_defs : BoolExpr list, rvars_alt : Expr list) =  
                        List.unzip
                        << List.concat 
                        << List.mapi
                            (fun (moduleNumber:int) (rvar:Expr option) -> 
                                // assemble the alternative random variable
                                match rvar with
                                | None -> [] // do nothing
                                | Some rvar -> 
                                    let rvarName = rvar.FuncDecl.Name.ToString()
                                    let rvar_alt = z3.MkBVConst(rvarName + "_alt",co.randomBVSize)
                                    let rvar_alt_def : BoolExpr = 
                                        z3mkAnd co.z3
                                            << List.map
                                                (fun (position:int) ->
                                                    downcast z3.MkITE(
                                                        z3mkOr z3 
                                                        << List.map
                                                            (fun (bitSel:BitSelector) ->
                                                                z3mkAnd z3
                                                                    [
                                                                    z3.MkEq(bitSel.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
                                                                    z3.MkEq(bitSel.ModuleSelector,z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
                                                                    z3.MkEq(bitSel.PosSelector,z3.MkBV(position,co.positionBVSize))
                                                                    ])
                                                        <| cce,
                                                        z3.MkNot(
                                                            z3.MkEq(
                                                                z3.MkExtract(uint32 position,uint32 position,downcast rvar_alt),
                                                                z3.MkExtract(uint32 position,uint32 position,downcast rvar))),
                                                        z3.MkEq(
                                                            z3.MkExtract(uint32 position,uint32 position,downcast rvar_alt),
                                                            z3.MkExtract(uint32 position,uint32 position,downcast rvar))
                                                    )
                                                    )
                                            <| [0..(Convert.ToInt32 co.randomBVSize)-1]
                                    (rvar_alt_def,upcast rvar_alt) :: []
                                )
                        <| matchRandomVariablesToModules co randomVars co.prismModel.Modules
                    let currentStep : Expr = // if co.prismModel.Type.Equals(DTMC) then co.z3.MkBV(0,co.stepBVSize) :> Expr else 
                        co.z3.MkBV(step,co.stepBVSize) :> Expr
                    let nextSysStateVars_alt : Expr list = 
                        List.map 
                            (fun (v:Expr) -> 
                                let vName = v.FuncDecl.Name.ToString()
                                if v.IsBool then 
                                    upcast z3.MkBoolConst(vName + "_alt")
                                else
                                    let vbv : BitVecExpr = downcast v
                                    let vName = v.FuncDecl.Name.ToString()
                                    upcast z3.MkBVConst(vName + "_alt", vbv.SortSize) ) 
                            nextSysStateVars

                    z3.MkAnd 
                        [|
                        z3mkAnd co.z3 rvar_alt_defs ;
                        downcast z3.MkApp(
                            co.transitionRelation,
                            Array.ofList ( currentStep :: rvars_alt @ sysStateVars @ nextSysStateVars_alt @ formulaVars @ syncGuardVars @ pChoiceVars)) 
                        z3.MkImplies(
                            z3mkOr z3 << List.map2 (fun a b -> z3.MkNot(z3.MkEq(a,b))) randomVars <| rvars_alt,
                            z3mkOr co.z3
                                << List.map2
                                    (fun (nextSysStateVar:Expr) (nextSysStateVar_alt:Expr) -> 
                                        z3.MkNot(z3.MkEq(nextSysStateVar,nextSysStateVar_alt))
                                        )
                                    nextSysStateVars
                                <| nextSysStateVars_alt
                            )
                        |]
                    )
            << List.zip (take ac.CurrentStepBound co.randomVars)
            << List.zip3 (take ac.CurrentStepBound co.sysStateVars) (take ac.CurrentStepBound co.sysStateVars.Tail)
            << List.zip (take ac.CurrentStepBound co.formulaVars)
            << List.zip (take ac.CurrentStepBound co.syncGuardVars)
            << take ac.CurrentStepBound
            <| co.pChoiceVars

        let t_macro_finder = co.z3.MkTactic("macro-finder")

        let it = 
            applyTactic ac t_macro_finder 
                (z3.MkAnd 
                    [|
                    ac.PrecomputedZ3Objects.TRDef_overApprox ;
                    ac.PrecomputedZ3Objects.GuardDefs ;
                    ac.PrecomputedZ3Objects.FormulaDefs ;
                    res ;
                    |])
        it


    let fuseCubeWithDistribution (ac:AnalyzerContext) (cube:Cube) : BoolExpr = 
        let co = ac.co
        let rrv = relevantRandomVars ac
        let rrv_array = Array.ofList << List.concat <| rrv
        upcast co.z3.MkForall(
            rrv_array, 
            co.z3.MkEq(
                co.z3.MkApp(co.distributions.Item (ac.CurrentStepBound-1),  rrv_array), 
                encodeCube co cube rrv))
    
    let fusePathWithRandomVars_zeroDistance (ac:AnalyzerContext) (path:Path) : BoolExpr = 
        let co = ac.co
        let z3 = co.z3
        z3mkAnd z3
        << List.mapi
            (fun (step:int) ((_,pathVars: RVar list), rvars:Expr list) -> 
                z3mkAnd co.z3
                << List.mapi
                    (fun (moduleNumber:int) (pathVar:RVar, rvar:Expr option) -> 
                        match pathVar with
                        | NonProbModule -> // it is a module without random variable
                            z3.MkTrue()
                        | NonProbTransition -> // for this module, a deterministic transition was picked
                            z3.MkEq(z3.MkBV(0,co.randomBVSize), rvar.Value)
                        | Prob pVar -> 
                            z3.MkEq(pVar, rvar.Value)
                    )
                << List.zip pathVars
                <| matchRandomVariablesToModules co rvars co.prismModel.Modules)
        << List.zip (take ac.CurrentStepBound path)
        <| relevantRandomVars ac
        
    let fusePathWithRandomVars_singleBitSelector (ac:AnalyzerContext) (path:Path) (bitSelector:BitSelector) : BoolExpr = 
        let co = ac.co
        let z3 = co.z3
        z3mkAnd z3
        << List.mapi
            (fun (step:int) ((_,pathVars: RVar list), rvars:Expr list) -> 
                z3mkAnd co.z3
                << List.mapi
                    (fun (moduleNumber:int) (pathVar:RVar, rvar:Expr option) -> 
                        match pathVar with
                        | NonProbModule -> // it is a module without random variable
                            z3.MkTrue()
//                            z3.MkNot(
//                                z3.MkAnd
//                                    [|
//                                    z3.MkEq(bitSelector.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
//                                    z3.MkEq(bitSelector.ModuleSelector,z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
//                                    |]
//                                )
                        | NonProbTransition -> // for this module, a deterministic transition was picked
                            z3.MkAnd
                                [|
                                z3.MkNot(
                                    z3.MkAnd
                                        [|
                                        z3.MkEq(bitSelector.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
                                        z3.MkEq(bitSelector.ModuleSelector,z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
                                        |]
                                    ) ;
                                z3.MkEq(z3.MkBV(0,co.randomBVSize), rvar.Value)
                                |]
                        | Prob pVar -> 
                            downcast z3.MkITE (
                                // if
                                z3.MkAnd
                                    [|
                                    z3.MkEq(bitSelector.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
                                    z3.MkEq(bitSelector.ModuleSelector,z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
                                    |], 
                                // then
                                z3mkAnd co.z3
                                << List.map
                                    (fun (position:int) ->
                                        downcast z3.MkITE(
                                            z3.MkEq(bitSelector.PosSelector,z3.MkBV(position,co.positionBVSize)),
                                            z3.MkNot(
                                                z3.MkEq(
                                                    z3.MkExtract(uint32 position,uint32 position,downcast pVar),
                                                    z3.MkExtract(uint32 position,uint32 position,downcast rvar.Value))),
                                            z3.MkEq(
                                                z3.MkExtract(uint32 position,uint32 position,downcast pVar),
                                                z3.MkExtract(uint32 position,uint32 position,downcast rvar.Value))
                                        )
                                        )
                                <| [0..(Convert.ToInt32 co.randomBVSize)-1] ,
                                //else
                                z3.MkEq(pVar, rvar.Value)
                                )
                    )
                << List.zip pathVars
                <| matchRandomVariablesToModules co rvars co.prismModel.Modules)
        << List.zip (take ac.CurrentStepBound path)
        <| relevantRandomVars ac

        

    let fusePathWithRandomVars (ac:AnalyzerContext) (path:Path) (cce:CloseCounterExample) : BoolExpr = 
        let co = ac.co
        let z3 = co.z3
        z3mkAnd z3
        << List.collect
            (fun (step:int, (_,pathVars: RVar list), rvars:Expr list) -> 
                List.collect
                    (fun (moduleNumber:int,(pathVar:RVar, rvar:Expr option)) -> 
                        match pathVar with
                        | NonProbModule -> // it is a module without random variable
                            [] // []
                        | NonProbTransition -> // it is a module without random variable
                            [] // []
                        | _ -> 
                            let pVar = 
                                match pathVar with
                                | NonProbTransition -> // for this module, a deterministic transition was picked
                                    z3.MkBV(0,co.randomBVSize)
                                | Prob pVar -> pVar
                                | NonProbModule -> 
                                    raise (InnerError "Case not possible.")
                            downcast z3.MkITE(
                                //if
                                z3mkOr z3 
                                << List.map 
                                    (fun (bitselector:BitSelector) -> 
                                        z3mkAnd z3 
                                            [
                                            z3.MkEq(bitselector.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
                                            z3.MkEq(bitselector.ModuleSelector,z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
                                            ])
                                <| cce,
                                // then
                                z3mkAnd co.z3
                                << List.map
                                    (fun (position:int) ->
                                        downcast z3.MkITE(
                                            // if   
                                            z3mkOr z3 
                                            << List.map
                                                (fun (bitSel:BitSelector) ->
                                                    z3mkAnd z3  
                                                        [
//                                                        z3.MkEq(bitSel.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
//                                                        z3.MkEq(bitSel.ModuleSelector,z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
                                                        z3.MkEq(bitSel.PosSelector,z3.MkBV(position,co.positionBVSize))
                                                        ])
                                            <| cce ,
                                            // then
                                            z3.MkNot
                                            <| z3.MkEq(
                                                z3.MkExtract(uint32 position,uint32 position,downcast pVar),
                                                z3.MkExtract(uint32 position,uint32 position,downcast rvar.Value)) ,
                                            // else
                                            z3.MkEq(
                                                z3.MkExtract(uint32 position,uint32 position,downcast pVar),
                                                z3.MkExtract(uint32 position,uint32 position,downcast rvar.Value))
                                        )
                                        )
                                <| [0..(Convert.ToInt32 co.randomBVSize)-1]
                                ,
                                // else
                                z3.MkEq(pVar,rvar.Value) 
                                ) :: []

                            ) 
                << List.zip [0..co.prismModel.Modules.Length-1]
                << List.zip pathVars // (matchRandomVariablesToModules co pathVars co.prismModel.Modules)
                <| (matchRandomVariablesToModules co rvars co.prismModel.Modules) 
            )
        << List.zip3 [0..ac.CurrentStepBound-1]  (take ac.CurrentStepBound path)
        <| relevantRandomVars ac 

    let reachGoalForAny ac steplist : BoolExpr = 
        z3mkOr ac.co.z3
        << List.map (fun step -> finalCondition ac.co (Some step))
        <| steplist
            
    let goalRegion ac enableEarlyTermination : BoolExpr =
        match enableEarlyTermination with
        | true -> reachGoalForAny ac [0..ac.CurrentStepBound]
        | false -> reachGoalForAny ac [ac.CurrentStepBound]

    let excludeEarlyTermination ac = 
        match ac.NoPathToGoalRegionUntilStep with
        | None   -> ac.co.z3.MkTrue()
        | Some s -> ac.co.z3.MkNot (reachGoalForAny ac [0..s-1]) ;

    let encodeIntegratedPositiveChecks (ac:AnalyzerContext) (cube:Cube) (enableEarlyTermination:bool) : BoolExpr =
        let co = ac.co
        let z3 = co.z3

        let goalRegion : BoolExpr = goalRegion ac enableEarlyTermination
//            finalCondition ac.co (Some ac.CurrentStepBound)

        // encapsulate the positiveBMC check as a function definition
        let bmcFun : FuncDecl = 
            z3.MkFuncDecl("existsPath", Array.ofList << List.concat <| relevantRandomVarsSorts ac @ relevantSysStateVarsSorts ac, co.z3.MkBoolSort())

        let bmcFunctionDefinition : BoolExpr = 
            let rrv = relevantRandomVars ac
            let rsv = relevantSysStateVars ac
            let args = Array.ofList << List.concat <| rrv @ rsv
            upcast z3.MkForall 
                (args, 
                z3.MkEq(z3.MkApp(bmcFun, args),
                    z3mkAnd co.z3
                        [
                        initialCondition co
//                        ac.PrecomputedZ3Objects.InitialCondition ;
                        allStepsTransitionRelation co ac.CurrentStepBound ;
                        allStepsFormulaConstraints co ac.CurrentStepBound ;
                        goalRegion ; 
                        noDeadlock co ac.CurrentStepBound ;
                        variableRangesAllSteps co ac.CurrentStepBound ;
                        downcast z3.MkApp(co.distributions.Item (ac.CurrentStepBound-1), Array.ofList << List.concat <| rrv ) ;
                        excludeConcreteCubes ac ac.PositiveCubes;
                        ]))

        // create new copy of state variables and random variables
        let copyOfRandomVars = 
            List.map 
                (List.map
                    (fun (constant:Expr) -> // this expression is a simple constant
                        let name = constant.FuncDecl.Name.ToString() + "_positiveBMC"
                        co.z3.MkConst(name, constant.Sort)))
            <| relevantRandomVars ac

        let copyOfSysStateVars = 
            List.map
                (List.map
                    (fun (constant:Expr) -> // this expression is a simple constant
                        let name = constant.FuncDecl.Name.ToString() + "_positiveBMC"
                        co.z3.MkConst(name, constant.Sort)))
            <| relevantSysStateVars ac

        // Fix all free bits to some arbitrary value (i.e. 0). 
        // This is a legal strengthening of the requiremet that there is a path in the specified cube. 
        let zeroConstraints : BoolExpr = 
            z3mkAnd z3
            << List.collect
                (fun (step:int, rvars:Expr list) -> 
                    List.collect
                        (fun (v:Expr option,(m:PrismModule,moduleNumber:int)) -> 
                            List.collect
                                (fun (position:int) ->
                                    if v.IsSome
                                    then
                                        let randomVar : BitVecExpr = downcast v.Value
                                        z3.MkImplies(
                                            z3mkAnd z3 
                                            << List.map 
                                                (fun (bitselector,_) -> 
                                                    z3.MkNot 
                                                    <| z3mkAnd z3 [
                                                        z3.MkEq(bitselector.StepSelector,z3.MkBV(step,co.stepBVSize)) ;
                                                        z3.MkEq(bitselector.ModuleSelector,co.z3.MkBV(moduleNumber, co.moduleNumberBVSize)) ;
                                                        z3.MkEq(bitselector.PosSelector,co.z3.MkBV(position, co.positionBVSize)) ;
                                                        ])
                                            <| cube
                                            , 
                                            z3.MkEq(
                                                z3.MkExtract(uint32 position,uint32 position,randomVar),
                                                z3.MkBV(0,1u))
                                        ) :: []
                                    else [] )
                                [0.. (Convert.ToInt32 co.randomBVSize)-1])
                    << List.zip (matchRandomVariablesToModules co rvars co.prismModel.Modules)
                    << List.zip co.prismModel.Modules
                    <| [0..co.prismModel.Modules.Length-1]
                )
            << List.zip [0..ac.CurrentStepBound-1]
            << take ac.CurrentStepBound
            <| copyOfRandomVars 

        z3mkAnd z3
            [
            bmcFunctionDefinition ;
            downcast z3.MkApp(bmcFun,Array.ofList << List.concat <| copyOfRandomVars @ copyOfSysStateVars) ; 
            zeroConstraints 
            ]


    let cubeDoesNotContainCCEs (co:EncodingContext) (cube:Cube) (cces:ConcreteCCE list) : BoolExpr =
        z3mkAnd co.z3
        << List.map
            (fun (cce:ConcreteCCE) -> 
                z3mkOr co.z3
                << List.collect
                    (fun (cbs:ConcreteBitSelector) -> 
                        List.map
                            (fun (bs:BitSelector,_) -> 
                                z3mkAnd co.z3
                                    [
                                    co.z3.MkEq(bs.StepSelector,cbs.StepSelector) ;
                                    co.z3.MkEq(bs.ModuleSelector,cbs.ModuleSelector) ;
                                    co.z3.MkEq(bs.PosSelector,cbs.PosSelector) ;
                                    ]
                            )
                            cube
                    )    
                <| cce)
        <| cces



//    let cubeHasPathBitVals (co:EncodingContext) (cube:Cube) (path:Path) : BoolExpr =
//        encodeCube co cube (rVarsOfPath co path)


    
    // There is no bs in the cube that contradicts the rpath
    let rPathIsInCube (ac:AnalyzerContext) (rpath:RPath) (cube:Cube) : BoolExpr = 
        let z3 = ac.co.z3
        z3.MkNot  
        << z3mkOr z3
        << List.map // over all cube positions
            (fun (bs:BitSelector,bitVal:BitVecExpr) ->
                z3mkAnd z3
                << List.mapi // maps over all steps
                    (fun (step:int) (pvars:RStep) -> 
                        z3.MkImplies(
                            z3.MkEq (bs.StepSelector,z3.MkBV(step,ac.co.stepBVSize)),
                            z3mkAnd z3
                            << List.concat
                            << List.mapi // maps over all modules 
                                (fun (moduleNum:int) (pvar:RVar) -> 
                                    match pvar with
                                    | NonProbModule -> 
//                                        z3.MkNot (z3.MkEq (bs.ModuleSelector,z3.MkBV(moduleNum,ac.co.moduleNumberBVSize)))
                                        [] // taken care of somewhere else
                                    | NonProbTransition -> 
//                                        z3.MkNot (z3.MkEq (bs.ModuleSelector,z3.MkBV(moduleNum,ac.co.moduleNumberBVSize)))
                                        []
                                    | Prob bvnum -> 
                                        z3.MkImplies(
                                            z3.MkEq (bs.ModuleSelector,z3.MkBV(moduleNum,ac.co.moduleNumberBVSize)),
                                            z3mkAnd z3
                                            << List.map
                                                (fun (posNum:int) -> 
                                                    z3.MkImplies(
                                                        z3.MkEq (bs.PosSelector,z3.MkBV(posNum,ac.co.positionBVSize)),
                                                        z3.MkNot (z3.MkEq (bitVal,z3.MkExtract(uint32 posNum,uint32 posNum,bvnum)))
                                                    )
                                                            
                                                )
                                            <| [0..(int32 ac.co.randomBVSize)-1]
                                            ) :: []
                                    )
                            <| pvars)
                        )
                <| rpath
                )
        <| cube

    // For all CEs there is a bs in the cube that contradicts some CE value
    let excludeCECache_cube (ac:AnalyzerContext) (cube:Cube) : BoolExpr = 
        let z3 = ac.co.z3
        z3mkAnd z3
        << List.map 
            (fun (rpath:RPath) -> 
                    z3.MkNot(rPathIsInCube ac rpath cube)
                )
        <| ac.CECache

    let excludeCECache_rvars (ac:AnalyzerContext) (randomVars:Expr list list) : BoolExpr = 
        z3mkAnd ac.co.z3
        << List.map // maps over all counterexamples
            (fun (rpath:RPath) -> 
                ac.co.z3.MkNot
                << z3mkAnd ac.co.z3
                << List.collect // maps over all steps
                    (fun (pvars:RStep, rvars: Expr list) ->
                        List.collect // maps over all modules
                            (fun (pvar:RVar,rvar:Expr option) -> 
                                match pvar with
                                | NonProbModule | NonProbTransition -> []
                                | Prob bvnum -> ac.co.z3.MkEq(bvnum,rvar.Value) :: []
                                )
                        << List.zip pvars
                        << matchRandomVariablesToModules ac.co rvars 
                        <| ac.co.prismModel.Modules
                        )
                << List.zip rpath
                << takeAsMany rpath
                <| randomVars
                )
        <| ac.CECache



    
    // Encodes the cce as a linear number of boolean flags. Expresses the distance as a linear bound on the sum of 1s. 
    let fusePathWithRandomVars_sumEncoding (ac:AnalyzerContext) (path:Path) (distance:int) : BoolExpr = 
        let co = ac.co
        let z3 = co.z3
        let maxBitsNumber : int = ac.CurrentStepBound * co.prismModel.Modules.Length * (int) co.randomBVSize
//        let bvSize = Convert.ToUInt32 (ceil (log (Convert.ToDouble distance) / log 2.0)) + 1u
        let distanceBVSize = Convert.ToUInt32 (ceil (log (Convert.ToDouble maxBitsNumber)/ log 2.0)) + 1u
        let distanceSort = z3.MkBitVecSort(distanceBVSize)
        
        z3.MkBVUGE(
            z3.MkBV(distance,distanceBVSize),
            List.fold 
                (fun old novel -> z3.MkBVAdd(novel,old))
                (upcast z3.MkBV(0,distanceBVSize))
            << List.collect
                (fun (step:int, (_,pathVars: RVar list), rvars:Expr list) -> 
                    List.collect
                        (fun (moduleNumber:int,(pathVar:RVar, rvar:Expr option)) -> 
                            if pathVar.Equals NonProbModule then []
                            else 
                            let pVar = 
                                match pathVar with
                                | NonProbTransition -> 
                                    z3.MkBV(0,co.randomBVSize)
                                    //z3.MkEq(z3.MkBV(0,co.randomBVSize),rvar.Value) :: [] // alternatively this could be non-restricted
                                    // not restricting this kind of variables might detect more close counter-examples, but might also make the search harder
                                | Prob pVar -> pVar
                                | NonProbModule -> raise (InnerError "Reference to nonprobabilistic module.")
                            List.map
                                (fun (position:int) ->
                                    downcast z3.MkITE(
                                        // if   
                                        z3.MkNot
                                        <| z3.MkEq(
                                            z3.MkExtract(uint32 position,uint32 position,downcast pVar),
                                            z3.MkExtract(uint32 position,uint32 position,downcast rvar.Value)) ,
                                        // then
                                        z3.MkBV(1,distanceBVSize),
                                        // else
                                        z3.MkBV(0,distanceBVSize)
                                    ))
                            <| [0..(Convert.ToInt32 co.randomBVSize)-1]
                            ) 
                    << List.zip [0..co.prismModel.Modules.Length-1]
                    << List.zip pathVars // (matchRandomVariablesToModules co pathVars co.prismModel.Modules)
                    <| (matchRandomVariablesToModules co rvars co.prismModel.Modules) 
                )
            << List.zip3 [0..ac.CurrentStepBound-1]  (take (ac.CurrentStepBound) path) // not including the last set of variables!
            <| relevantRandomVars ac 
        )

    // There is a bitSelector for which the affected bit is the same as on the original path
    let excludeOtherCCE_sumEncoding (co:EncodingContext) (path:Path) (otherCCCE:ConcreteCCE) : BoolExpr =
        let z3 = co.z3

        z3mkOr z3
        << List.map // over all cube positions
            (fun (bs:ConcreteBitSelector) ->
                let pathVarsStep : SysState * RStep = path.Item bs.StepSelector.Int
                let pathVarModule : RVar = (snd pathVarsStep).Item bs.ModuleSelector.Int
                let pathVarModule_bv : BitVecNum = 
                    match pathVarModule with
                    | Prob v -> v
                    | NonProbTransition -> z3.MkBV(0,co.randomBVSize)
                    | _ -> raise (InnerError "A concrete bitSelector referred to a nonprobabilistic module.")
                let rvarsStep : Expr list = co.randomVars.Item bs.StepSelector.Int
                let rvar = (matchRandomVariablesToModules co rvarsStep co.prismModel.Modules).Item bs.ModuleSelector.Int

                let posNum = bs.PosSelector.Int
                z3.MkEq (
                    z3.MkExtract(uint32 posNum,uint32 posNum,downcast rvar.Value),
                    z3.MkExtract(uint32 posNum,uint32 posNum,pathVarModule_bv))
                )
        <| otherCCCE



    // In the new sum encoding, the CCCEs can only be found by comparison with the path
    let extractCounterExample_sumEncoding (ac:AnalyzerContext) (solver:Solver) (path:Path) : ConcreteCCE = 
        let co = ac.co
        let z3 = co.z3
        List.collect
            (fun (step:int, (_,pathVars: RVar list), rvars:Expr list) -> 
                List.collect
                    (fun (moduleNumber:int,(pathVar:RVar, rvar:Expr option)) -> 
                        match pathVar with
                        | NonProbModule -> // it is a module without random variable
                            [] // []
                        | _ -> 
                            let pVar = 
                                match pathVar with
                                | Prob pVar -> pVar
                                | _ -> //That is: NonProbTransition; we need to extract the difference information anyhow
                                    z3.MkBV(0,co.randomBVSize)
                            List.collect
                                (fun (position:int) ->
                                    let pathVarBitVal : BitVecNum = downcast solver.Model.Eval(z3.MkExtract(uint32 position,uint32 position,downcast pVar),true)
                                    let rVarBitVal : BitVecNum = downcast solver.Model.Eval(z3.MkExtract(uint32 position,uint32 position,downcast rvar.Value),true)
                                    if not (pathVarBitVal.Int = rVarBitVal.Int) 
                                    then 
                                        {
                                        StepSelector = z3.MkBV(step,co.stepBVSize) ;
                                        ModuleSelector = z3.MkBV(moduleNumber,co.moduleNumberBVSize) ;
                                        PosSelector = z3.MkBV(position,co.positionBVSize) ;
                                        } :: []
                                    else []
                                    )
                            <| [0..(Convert.ToInt32 co.randomBVSize)-1]
                        ) 
                << List.zip [0..co.prismModel.Modules.Length-1]
                << List.zip pathVars // (matchRandomVariablesToModules co pathVars co.prismModel.Modules)
                <| (matchRandomVariablesToModules co rvars co.prismModel.Modules) 
            )
        << List.zip3 [0..ac.CurrentStepBound-1]  (take ac.CurrentStepBound path)
        <| relevantRandomVars ac 