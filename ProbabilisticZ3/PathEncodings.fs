// MN Rabe

namespace ProbabilisticZ3

open System

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open SolverConfigs
open Problems
open Paths
open CounterExamples
open EncodingContext
open AnalyzerContexts
open ExpressionEncodings
open PrismModelEncoding

module PathEncodings =

    let rec extractPath (ac:AnalyzerContext) (solver:Solver) (rVarss:Expr list list) (sysVarss:Expr list list) (step:int) : Path = 
        let co = ac.co

        let sysNums : Expr list -> SysVar list = 
            List.map (fun (sysVar:Expr) -> 
                let value = solver.Model.Eval(sysVar,true)
                if value.IsBool then B (downcast value) else BV (downcast value)
                )
        let rNums : Expr list -> BitVecNum list = 
            List.map (fun (rVar:Expr) -> downcast solver.Model.Eval(rVar,true))

        let transitionInfos : (Transition * (int*int)) option list = 
            List.mapi // modules
                (fun (mNum:int) (m:PrismModule) -> 
                    let activeTransition : (Transition * (int*int)) list = // there can be at most one active transition per module
                        List.concat
                        << List.mapi // transitions
                            (fun (tNum:int) (t:Transition) -> 
                                let b = solver.Model.Eval(ac.co.z3.MkBoolConst(transitionConstName_var (mNum,tNum) step),true)
                                if b.BoolValue.Equals Z3_lbool.Z3_L_TRUE 
                                then (t,(mNum,tNum)) :: [] 
                                else []
                            )
                        <| m.Transitions.Value
                    match activeTransition with
                    | [] -> None 
                    | t :: [] -> Some t
                    | _ -> raise (InnerError "Multiple transitions are active at the same time???")
                )
            <| co.prismModel.Modules

        let rec determineNonProbTransitions (rNumOpts : BitVecNum option list) (tInfos:(Transition * (int*int)) option list) : RVar list = 
            match (rNumOpts,tInfos) with 
            | ([],[]) -> []
            | (Some p :: ps, Some tInfo :: tInfosR) -> 
                match tInfo with // should exist, since this corresponds to a module with random variable
                | (TDet _,_) -> NonProbTransition :: determineNonProbTransitions ps tInfosR
                | (TProb _,_) -> Prob p :: determineNonProbTransitions ps tInfosR
            | (None :: ps, _ :: tInfosR) -> 
                NonProbModule :: determineNonProbTransitions ps tInfosR
            | _ -> raise (InnerError "Lists must have equal length")

        match (sysVarss,rVarss) with
        | (sysVars::[],[]) -> (sysNums sysVars,[]) :: []
        | (sysVars::sysVarsr,rVars::rVarsr) ->
            let sysNums : SysVar list = sysNums sysVars
            let rNums = rNums rVars
            let rNumOpts = matchRandomVariablesToModules ac.co rNums ac.co.prismModel.Modules
            let rVarsReduced = determineNonProbTransitions rNumOpts transitionInfos

            let pathR = extractPath ac solver rVarsr sysVarsr (step+1)
            (sysNums,rVarsReduced) :: pathR 
        | _ -> raise (InnerError "Length of lists does not match. Expected rVarss to have exactly one less entry than systVarss.")


    let printPath (path:Path) = 
        (String.concat "step-" 
                (List.map 
                    (fun (_,rvars:RVar list) -> 
                        String.concat 
                            "." 
                            (List.map 
                                (fun (rvar:RVar) ->  
                                    match rvar with
                                    | NonProbModule | NonProbTransition -> "NonProb" 
                                    | Prob num -> num.Int.ToString()) 
                                    rvars))
                    path))


    let rec rVarsOfPath (co:EncodingContext) (path:Path) : Expr list list = 
        match path with 
        | (_,rStep)::step2::pathr -> 
            List.collect 
                (fun (rvar:RVar) -> 
                    match rvar with 
                    | NonProbModule -> []
                    | NonProbTransition -> [co.z3.MkBV(0,co.randomBVSize)]
                    | Prob x -> [x :> Expr]) 
                rStep  
            :: rVarsOfPath co (step2::pathr)
        | (_,[])::[] -> []
        | _ -> raise (InnerError "This recursion should avoid reaching the last element of the list ... but didn't.")

        
    let rec path2RPath xs = // List.map snd ... and cut off the last element
        match xs with
        | (y,z)::x::xr -> z :: path2RPath (x::xr)
        | _ -> []
        //| [] | x::xr -> []

    let CCE2RPath (ac:AnalyzerContext) (referencePath:Path) (cce:ConcreteCCE) : RPath = 

        let rec createNewRVars (rVars:RVar list) (cce:ConcreteCCE) (step:int) (moduleNum:int) : (RVar list * ConcreteCCE) = 
            match (rVars, cce) with
            | (rVar::rVarsr, cbs::ccer) -> 
                match (compare cbs.StepSelector.Int step, compare cbs.ModuleSelector.Int moduleNum) with
                | (-1,_) ->
                    raise (InnerError "There should not appear a step number that is smaller than the currently considered one. Was the cce not sorted?")
                | (1,_) -> // This cbs already refers to the next step, we can stop with this list of rVars
                    (rVar::rVarsr, cbs::ccer)
                | (0,-1) -> // cbs.ModuleSelector < moduleNum
                    raise (InnerError "We apparently left out a module, or the cce was not sorted.")
                | (0,0)  -> // We are at the right module
                    let newRVar : RVar = 
                        match rVar with
                        | NonProbModule -> 
                            raise (InnerError "Concrete counterexample refers to a nonprobabilistic module.")
                        | _ -> 
                        let p = 
                            match rVar with
                            | NonProbTransition -> ac.co.z3.MkBV(0,ac.co.randomBVSize)
                            | Prob p -> p
                            | NonProbModule -> raise (InnerError "Concrete counterexample refers to a nonprobabilistic module.")
                        let z3 = ac.co.z3
                        let flipper = 
                                z3.MkBVSHL(
                                    z3.MkBV(1,p.SortSize),
                                    if p.SortSize-cbs.PosSelector.SortSize > 0u
                                    then 
                                        z3.MkConcat(
                                            z3.MkBV(0,p.SortSize-cbs.PosSelector.SortSize),
                                            cbs.PosSelector)
                                    else upcast cbs.PosSelector)
                        let e = z3.MkBVXOR(p,flipper)
                        Prob (downcast e.Simplify())
                            
                    createNewRVars (newRVar::rVarsr(*There could be more cbss that refer to this module*)) ccer step moduleNum
                    
                | (0,1)  -> // cbs.ModuleSelector > moduleNum , go to the next module
                    let (rs,cs) = createNewRVars rVarsr (cbs::ccer) step (moduleNum+1) 
                    (rVar::rs,cs)
                | _ -> raise (InnerError "Unexpected result of comparison")
            | (rVars,[]) -> (rVars, [])
            | ([],cce)   -> ([], cce)



        let rec CCE2Path (referencePath:Path) (cce:ConcreteCCE) (step:int) : RPath = 
            match (referencePath, cce) with
            | (path,[]) -> path2RPath path
            | ([],_) | (_::[],_) -> raise (InnerError "The concrete close counterexample referred to some position outside the path or it referred to the last step of a path, which is supposed to be irrelevant.")
            | ((sysVar,rVars:RVar list) :: pathr, cbs::ccer) -> 
                match compare cbs.StepSelector.Int step with 
                | -1 -> // cbs.StepSelector < step
                    raise (InnerError "Unexpected value for 'step', or the cce was not sorted.")
                | 0  -> // We are at the step. 
                    // map over rvars
                    // if rvar is concerned by cce then flip the bits
                    // else use the same as for the reference path
                    let (newRVars,ccer2) = createNewRVars rVars (cbs::ccer) step 0 
                    newRVars :: CCE2Path pathr ccer2 (step+1)
                | 1  -> // cbs.StepSelector > step , so this step whole step does not have to be changed
                    rVars :: CCE2Path pathr (cbs::ccer) (step+1)
                | _ -> raise (InnerError "Unexpected result of comparison")
        CCE2Path referencePath cce 0



