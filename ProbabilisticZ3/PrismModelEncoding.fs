// MN Rabe

namespace ProbabilisticZ3

open System

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open SolverConfigs
open Problems
open EncodingContext
open ExpressionEncodings

module PrismModelEncoding = 
    
    let syncLabelConstName_arg (syncLabel:string) : string = "var_" + syncLabel + "_arg"
    let syncLabelConstName_var (syncLabel:string) (step:int) : string = "var_" + syncLabel + "_" + step.ToString()

    let transitionConstName_arg tuple : string = "var_" + buildTransitionIdentifier tuple + "_arg"
    let transitionConstName_var tuple (step:int) : string = "var_" + buildTransitionIdentifier tuple + "_" + step.ToString()

    let pChoiceConstName_arg triple : string = "var_" + buildPChoiceIdentifier triple + "_arg"
    let pChoiceConstName_var triple (step:int) : string = "var_" + buildPChoiceIdentifier triple + "_" + step.ToString()

    // Provides a function that requires that all variables are in their specified bounds. 
    let encodeVariableRanges (co:EncodingContext) : BoolExpr = 
        let ranges : BoolExpr list = 
            List.collect 
                (fun (v:Variable) -> 
                    match (v.DataType,v.Range) with 
                    | (TInteger,Some(Eval (lower,upper))) ->
                        [co.z3.MkBVSGE(
                            downcast variable2Z3Const_arg co v,
                            co.z3.MkBV(lower,co.intBVSize)) ;
                         co.z3.MkBVSLE(
                            downcast variable2Z3Const_arg co v,
                            co.z3.MkBV(upper,co.intBVSize)) ;]
                    | (TInteger, Some (Raw _))  -> raise (InnerError ("Found unevaluated variable range for variable: '" + v.Name + "'."))
                    | (TInteger, None)          -> raise (InnerError "All integer variables should have a range.") 
                    | (_,_)                     -> [] // for all variables of other types
                    )
                (co.prismModel.Vars())

        let variableRangeFunctionDefinition : BoolExpr = 
            upcast co.z3.MkForall(
                    Array.ofList co.sysStateArgs, 
                    co.z3.MkEq(
                        co.z3.MkApp(co.variableRangeFunction, Array.ofList co.sysStateArgs),
                        co.z3.MkAnd(Array.ofList ranges))) 

        variableRangeFunctionDefinition


    let strategyArgs (co:EncodingContext) = 
            match co.problem.configs.StrategyEncoding with
            | Memoryless         -> Array.ofList <| co.sysStateArgs
            | StateTimeDependent -> Array.ofList <| co.stepArg :: co.sysStateArgs

    let strategyArgsSorts (co:EncodingContext) = 
        match co.problem.configs.StrategyEncoding with
        | Memoryless         -> Array.ofList <| co.sysStateArgsSorts
        | StateTimeDependent -> Array.ofList <| co.stepSort :: co.sysStateArgsSorts


    
    // Returns a list of conjuncts that 
    let initialCondition (co:EncodingContext) : BoolExpr = 
        // 5.2 Assert initial state
        // 5.2.1 Variables with constant initial state
        let innerExprs : Variable list -> Expressions.BoolExpr list =
            List.map
                (fun (v:Variable) -> 
                    match (v.DataType, v.Init) with 
                    | (TBool, None)     -> 
                        Expressions.IFF(
                            BoolExpr.BoolVar v,
                            BoolExpr.B false)
                    | (TInteger, None)  -> 
                        Expressions.Eq(
                            IntExpr.IntVar v,
                            match v.Range.Value with
                            | Eval (lower,upper) -> IntExpr.I lower // initial value is the lowest value in the range, see prism documentation
                            | _          -> raise (InnerError "Unevaluated variable range at unexpected point in the execution."))
                    | (TBool, Some (BoolExpr e))   -> 
                        Expressions.IFF(BoolExpr.BoolVar v, e)
                    | (TInteger, Some (IntExpr e)) -> 
                        Expressions.Eq(IntExpr.IntVar v, e)
                    | _        -> raise (InnerError "Detected variable that is not boolean or integer."))
        // 5.2.2 General constraints on initial states // TODO
        let initialConditions = 
            List.map 
                (translateBoolExpr co (Some 0) None) // step 0 represents the initial variables
            << innerExprs
            <| co.prismModel.Vars()
        co.z3.MkAnd (Array.ofList initialConditions)

    
    let compareProbToDouble (co:EncodingContext) (cmp:BitVecExpr * BitVecExpr -> BoolExpr) (random:BitVecExpr) (fixedPointVal:BitVecExpr) : BoolExpr = 
        // truncates doubles to the part after the comma
        let rSize = random.SortSize
        let fixedPointPosition = uint32(co.problem.fractionsEncoding)
        let relevantPart : BitVecExpr = co.z3.MkExtract(fixedPointPosition-1u,0u,fixedPointVal)

        let (extRandom,extDouble) : BitVecExpr*BitVecExpr =
            if fixedPointPosition = rSize then 
                (random,relevantPart)
            else if fixedPointPosition > rSize then // extend randoms
                let extRandom = co.z3.MkConcat(random,co.z3.MkBV(0,fixedPointPosition-rSize))
                (extRandom,relevantPart)
            else // extend doubles
                let extRelevantPart = co.z3.MkConcat(relevantPart,co.z3.MkBV(0,rSize-fixedPointPosition))
                (random,extRelevantPart)
        let it = cmp(extRandom,extDouble)
        it


    let translateUpdates (co:EncodingContext) (m:PrismModule) (updates:Update list) : BoolExpr =
        let existingUpdates : BoolExpr list = 
            List.map 
                (fun (u:Update) -> 
                    match u with
                    | BoolVarUp (v,e) -> co.z3.MkEq(variable2Z3Const_arg_next co v, translateBoolExpr co None None e)
                    | IntVarUp (v,e) -> co.z3.MkEq(variable2Z3Const_arg_next co v, translateIntExpr co None None e)
                    | DoubleVarUp (v,e) -> co.z3.MkEq(variable2Z3Const_arg_next co v, translateDoubleExpr co None None e)
                    | NoUpdate          -> co.z3.MkTrue())
                updates
        let isVar (var:Variable) (u:Update)  =
            match u with
            | BoolVarUp (v,_) | IntVarUp (v,_) | DoubleVarUp (v,_) -> var.Name.Equals v.Name
            | NoUpdate          -> false
        let notUpdatedVariables : Variable list =
            List.filter
                (fun (v:Variable) -> not << List.exists (isVar v) <| updates)
                m.Variables.Value // once there was an evil bug: @ co.prismModel.GlobalVariables
        let notUpdatedVariablesConstraints : BoolExpr list = 
            List.map
                (fun (v:Variable) -> 
                    co.z3.MkEq(
                        variable2Z3Const_arg_next co v,
                        variable2Z3Const_arg co v))
                notUpdatedVariables
        let result = co.z3.MkAnd(Array.ofList(existingUpdates@notUpdatedVariablesConstraints))
        result 

    // 1.1 Asserts the transition function for every variable in the given module. Then returns the function declarations of the variables' step functions. 
    let encodeModule (co:EncodingContext)  (abstr:AbstractionType) (moduleNum:int) (m:PrismModule) : BoolExpr list =
        let info = co.moduleInfos.Item(m.Name)
        let localChoiceNumbers : Map<Transition,int> = Map.ofList (List.zip (m.Transitions.Value) [0..m.Transitions.Value.Length-1])

        let encodeTransition (transitionNum:int) (t:Transition) : BoolExpr = 

            let transitionIsSelected : BoolExpr = 
                match co.problem.configs.SimplifiedGuardEncoding with
                | true -> 
//                    let name = "var_" + buildTransitionIdentifier (moduleNum,transitionNum) + "_arg" 
                    co.z3.MkBoolConst(transitionConstName_arg (moduleNum,transitionNum))
                | false -> 
                    let strategyArgs = 
                        match co.problem.configs.StrategyEncoding with
                        | Memoryless         -> Array.ofList <| co.sysStateArgs
                        | StateTimeDependent -> Array.ofList <| co.stepArg :: co.sysStateArgs
                    let strategyApp : BitVecExpr = 
                        downcast co.z3.MkApp(co.strategy, strategyArgs)
                    let localStrategyApp : BitVecExpr =
                        downcast co.z3.MkApp(co.localStrategies.Item m.Name, strategyArgs)
                    co.z3.MkEq(
                            localStrategyApp,
                            co.z3.MkBV(localChoiceNumbers.Item t, info.localChoiceBVSize))

            let randomCases : BoolExpr list =
                match t with 
                | TDet (sync, _, updates) -> translateUpdates co m updates :: []
                | TProb (sync, _, pchoices : (DoubleExpr * Update list) list) -> 
                    // create a disjunction over probabilistic choices mapping from 
                    // intervals to possible pchoices  (here we fixed an underapproximation)
                    let encodePChoice 
                            (accumSum : DoubleExpr, randomCases : BoolExpr list, pchoiceNum:int) // accumulator for fold
                            ((prob,updates) : PChoice) 
                            : DoubleExpr * BoolExpr list * int = 
                        // Construct the interval-condition that the local random choice is 
                        // between accumSum and accumSum+prob
                        let nextAccumSum : DoubleExpr = 
                            simplifyDoubleExpr 
                                (co.prismModel.Formulas @ co.prismModel.GlobalVariables @ m.Variables.Value) 
                                [] 
                                (DoubleExpr.Plus(accumSum,prob))
                        let accumSumExpr = 
                            translateDoubleExpr co None 
                                (if abstr.Equals OVERAPPROX then Some ROUND_DOWN else Some ROUND_UP)
                                accumSum
                        let nASExpr : BitVecExpr = 
                            translateDoubleExpr co None 
                                (if abstr.Equals OVERAPPROX then Some ROUND_UP else Some ROUND_DOWN)
                                nextAccumSum 

                        let lowerBound : BoolExpr = // this is equivalent to the following:
                            z3mkOr co.z3 
                                [
                                co.z3.MkEq(co.randomMax, co.moduleInfos.Item(m.Name).localRandomVar_arg.Value);
                                compareProbToDouble 
                                    co 
                                    co.z3.MkBVUGT 
                                    (co.z3.MkBVAdd( // this addition represents the NEXT random interval
                                        downcast co.moduleInfos.Item(m.Name).localRandomVar_arg.Value, 
                                        co.z3.MkBV(1u,co.randomBVSize))) 
                                    accumSumExpr]
                                
                        let upperBound : BoolExpr = 
                            match nextAccumSum with 
                            | D 1.0 -> co.z3.MkTrue() // corner case, since if nextAccumSum is 1, the comparison would fail due to limited number representation ... Problem: what if it cannot be determined statically -> will have a bogus comparison!!!
                            | _     ->
                                z3mkOr co.z3
                                    [
                                    co.z3.MkBVSGE(nASExpr, co.doubleOne);
                                    compareProbToDouble 
                                        co 
                                        co.z3.MkBVULT 
                                        (downcast co.moduleInfos.Item(m.Name).localRandomVar_arg.Value)
                                        nASExpr
                                    ]
//                                let alternativeWayToCompute ... wrong? = 
//                                    compareProbToDouble 
//                                        co 
//                                        co.z3.MkBVULE
//                                        (co.z3.MkBVSub( 
//                                            downcast co.moduleInfos.Item(m.Name).localRandomVar_arg.Value,
//                                            co.z3.MkBV(1,co.randomBVSize)))
//                                        nASExpr
                        let updateEffects : BoolExpr = 
                            if co.problem.configs.SimplifiedUpdateEncoding 
//                            then co.z3.MkBoolConst("var_" + buildPChoiceIdentifier (moduleNum,transitionNum,pchoiceNum) + "_arg")
                            then co.z3.MkBoolConst(pChoiceConstName_arg (moduleNum,transitionNum,pchoiceNum))
                            else translateUpdates co m updates
                        let newRandomCase : BoolExpr = 
                                (z3mkAnd co.z3
                                    [lowerBound ; 
                                    upperBound ;
                                    updateEffects]) 
                        let newRandomCaseSimplified : BoolExpr = downcast newRandomCase.Simplify()
                        (nextAccumSum, newRandomCaseSimplified :: randomCases, pchoiceNum+1)

                    let (sum,caseExprs,pChoiceCount) = List.fold encodePChoice (D 0.0, [], 0) pchoices
                    // sum should be 1 and pChoiceCount is known anyway
                    caseExprs

            let transitionExpr : BoolExpr = 
                co.z3.MkImplies(
                    transitionIsSelected,
                    co.z3.MkOr(Array.ofList randomCases))
            
            transitionExpr // return value of encodeTransition

        let it = List.mapi encodeTransition m.Transitions.Value // return value of encodeModule
        it


    let encodeTransitionRelation (co:EncodingContext) (abstr:AbstractionType) : BoolExpr = 
        let allTransitionConstraints : BoolExpr list = 
            List.concat
            << List.mapi
                (encodeModule co abstr) 
            <| co.prismModel.Modules

        let guardConstraints : BoolExpr = 
            downcast co.z3.MkApp(co.guardDefinitions,Array.ofList (co.sysStateArgs @ co.formulaArgs @ co.syncGuardArgs))

//         Optional: backward implication ... selecting the update implies the selection of the appropriate guard. 
        let pchoicesImplyGuards : BoolExpr = 
            if not co.problem.configs.SimplifiedUpdateEncoding  then co.z3.MkTrue()
            else 
            z3mkAnd co.z3
            << List.map 
                (fun (v:Variable) ->
                    co.z3.MkImplies(
                        translateBoolExpr co None None (BoolVar v),
                        downcast translateExpr co None None v.Init.Value))
            <| co.prismModel.PChoiceVariables

        // Optional: 
        let guardsImplySync : BoolExpr = 
            if not co.problem.configs.SimplifiedGuardEncoding then co.z3.MkTrue()
            else 
            z3mkAnd co.z3
            << List.map 
                (fun (v:Variable) ->
                    co.z3.MkImplies(
                        translateBoolExpr co None None (BoolVar v),
                        match v.VariableType with
                        | Guard syncLabel -> 
                            co.z3.MkBoolConst(syncLabelConstName_arg syncLabel)
//                            co.z3.MkBoolConst("var_" + syncLabel + "_arg") 
                        | _ -> raise (InnerError "Cannot happen.")
                        ))
            <| co.prismModel.GuardVariables

        let updateDefinitions : BoolExpr = 
            if not co.problem.configs.SimplifiedUpdateEncoding  then co.z3.MkTrue()
            else 
            let updateDefinitions : BoolExpr = 
                z3mkAnd co.z3
                << List.concat
                << List.mapi
                    (fun i (m:PrismModule) -> 
                        let moduleUpdates : BoolExpr list = 
                            List.mapi
                                (fun j (t:Transition) -> 
                                    let ups:Update list list =
                                        match t with
                                        | TDet (sl, guard, updates) -> [updates]
                                        | TProb (sl, guard, pcs) -> List.map snd pcs
                                    let pChoiceConstr (k:int) (ups:Update list) = 
                                        co.z3.MkImplies(
//                                            co.z3.MkBoolConst("var_" + buildPChoiceIdentifier (i,j,k) + "_arg"), 
                                            co.z3.MkBoolConst(pChoiceConstName_arg (i,j,k)),
                                            translateUpdates co m ups
                                            )
                                    let updatesDefinition = List.mapi pChoiceConstr ups
                                    // Optional: if this transition is taken, at leat one PChoice will be taken
                                    let pchoiceEnabledness : BoolExpr = 
                                        co.z3.MkImplies(
//                                            co.z3.MkBoolConst("var_" + buildTransitionIdentifier (i,j) + "_arg"),
                                            co.z3.MkBoolConst(transitionConstName_arg (i,j)),
                                            z3mkOr co.z3
                                            << List.mapi
                                                (fun k (_:Update list) -> 
//                                                    co.z3.MkBoolConst("var_" + buildPChoiceIdentifier (i,j,k) + "_arg")
                                                    co.z3.MkBoolConst(pChoiceConstName_arg (i,j,k))
                                                )
                                            <| ups)
                                    z3mkAnd co.z3 (pchoiceEnabledness :: updatesDefinition)
                                )
                                m.Transitions.Value
                        // Optional: for this module at least one transition will be taken
                        let transitionEnabledness : BoolExpr = 
                            z3mkOr co.z3
                            << List.mapi
                                (fun j (t:Transition) -> 
//                                    co.z3.MkBoolConst("var_" + buildTransitionIdentifier (i,j) + "_arg")
                                    co.z3.MkBoolConst(transitionConstName_arg (i,j))
                                )
                            <| m.Transitions.Value

                        transitionEnabledness :: moduleUpdates)
                <| co.prismModel.Modules
            updateDefinitions

        let transitionRelationDefinition : BoolExpr = // defines the transition relation
            upcast co.z3.MkForall(
                    Array.ofList <| co.stepArg :: co.randomArgs @ co.sysStateArgs @ co.sysStateArgs' @ co.formulaArgs @ co.syncGuardArgs @ co.pChoiceArgs, 
                    co.z3.MkEq(
                        co.z3.MkApp(co.transitionRelation, Array.ofList <| co.stepArg :: co.randomArgs @ co.sysStateArgs @ co.sysStateArgs' @ co.formulaArgs @ co.syncGuardArgs @ co.pChoiceArgs),
                        co.z3.MkAnd(
                            Array.ofList (
                                guardConstraints :: 
                                updateDefinitions :: 
                                pchoicesImplyGuards :: // optional
                                guardsImplySync :: // optional
                                allTransitionConstraints)))) 

        let it = transitionRelationDefinition.Simplify()
        let it2 = transitionRelationDefinition.Simplify()
        downcast it2


    let encodeFormulaDefinitions (co:EncodingContext) : BoolExpr = 
        let it = co.z3.MkForall(
                    Array.ofList (co.sysStateArgs @ co.formulaArgs), 
                    co.z3.MkEq(
                        co.z3.MkApp(co.formulaDefinitions, Array.ofList <| co.sysStateArgs @ co.formulaArgs), 
                        z3mkAnd co.z3
                        << List.map (fun (v:Variable) -> 
                            co.z3.MkEq(variable2Z3Const_arg co v, translateExpr co None None v.Init.Value))
                        <| co.prismModel.Formulas))
        upcast it
