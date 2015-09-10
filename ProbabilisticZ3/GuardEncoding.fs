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
open PrismModelEncoding


module GuardEncoding =

    // Defines the meaning of the function "guardDefinitions". It asserts the guard variables 
    // to be chosen according to the guards in the step to which the function is applied. 
    let encodeGuardsNewEncoding (co:EncodingContext) : BoolExpr = 
        
        let definitions : BoolExpr = 
            z3mkAnd co.z3
            << List.map (fun (v:Variable) -> 
                co.z3.MkImplies( // this is the essential difference to variables and formulas ... it uses implies
                    downcast variable2Z3Const_arg co v,
                    downcast translateExpr co None None v.Init.Value))
            <| co.prismModel.GuardVariables @ co.prismModel.SyncVariables

        let enablednessConstraint : BoolExpr = 
            z3mkOr co.z3
            << List.map (fun v -> translateBoolExpr co None None (BoolExpr.BoolVar v))
            <| co.prismModel.SyncVariables

        // Optional:  (creates a very long expression!)
//        let uniquenessConstraint : BoolExpr = // asserts that only one synclabel is enabled. 
//            z3mkAnd co.z3
//            << List.map 
//                (fun (v:Variable) -> 
//                    co.z3.MkImplies(
//                        translateBoolExpr co None (BoolExpr.BoolVar v),
//                        z3mkAnd co.z3 
//                        << List.collect
//                            (fun (v':Variable) -> 
//                                if v.Name.Equals v'.Name
//                                then []
//                                else [translateBoolExpr co None (BoolExpr.Not << BoolExpr.BoolVar <| v')]
//                                )
//                        <| co.prismModel.SyncVariables
//                        ))
//            <| co.prismModel.SyncVariables

        let it : BoolExpr = 
            upcast co.z3.MkForall(
                Array.ofList (co.sysStateArgs @ co.formulaArgs @ co.syncGuardArgs), 
                co.z3.MkEq(
                    co.z3.MkApp(co.guardDefinitions,Array.ofList <| co.sysStateArgs @ co.formulaArgs @ co.syncGuardArgs), 
                    co.z3.MkAnd 
                        [| 
                        definitions ; 
                        enablednessConstraint ; 
//                        uniquenessConstraint ;
                        |] 
                    ))
        let it_simp = it.Simplify()
        downcast it_simp



    let encodeFormulaDefinitions (co:EncodingContext) : BoolExpr = 
        upcast co.z3.MkForall(
            Array.ofList <| co.sysStateArgs @ co.formulaArgs, 
            co.z3.MkEq(
                co.z3.MkApp(co.formulaDefinitions,Array.ofList <| co.sysStateArgs @ co.formulaArgs), 
                z3mkAnd co.z3
                << List.map (fun (v:Variable) -> 
                    co.z3.MkEq(variable2Z3Const_arg co v, translateExpr co None None v.Init.Value))
                <| co.prismModel.Formulas))



    let relevantRanges (co:EncodingContext) : BoolExpr = 
//                co.z3.MkAnd(Array.ofList <| variableRanges co None)
        let stepRange: BoolExpr = 
            match co.problem.configs.StrategyEncoding with
            | Memoryless         -> co.z3.MkTrue()
            | StateTimeDependent -> 
                co.z3.MkBVULE(
                    downcast co.stepArg,
                    co.z3.MkBV(co.problem.GlobalStepBound-1,co.stepBVSize))
        z3mkAnd co.z3 [stepRange ; downcast co.z3.MkApp(co.variableRangeFunction, Array.ofList co.sysStateArgs)]

    let encodeGuards (co:EncodingContext) : BoolExpr = 
        let strategyArgs = strategyArgs co
        let strategyArgsSorts = strategyArgsSorts co
        let relevantRanges = relevantRanges co

        let deterministicCasesGlobalStrategy : (BoolExpr * Expr) list = 
            match co.prismModel.Type with
            | DTMC -> 
                List.collect
                    (fun (syncLabel:String, globalChoiceNum:int) -> 
                        if syncLabel.Equals("auxiliarySyncLabel_xkRbUclPoc3mSAShTH5L") 
                        then 
                            [] 
                        else
                            (co.z3.MkAnd(Array.ofList
                                (List.map
                                    (fun (m:PrismModule) -> 
                                        let moduleInfo = co.moduleInfos.Item m.Name
                                        co.z3.MkOr(Array.ofList
                                            (List.map
                                                (fun (t:Transition) -> 
                                                    match t with TDet (_,g,_) | TProb (_,g,_) -> translateBoolExpr co None None g)
                                                <| m.SynchSet.Item syncLabel)))
                                    co.prismModel.Modules)),
                             upcast co.z3.MkBV(globalChoiceNum, co.synchNameChoiceBVSize))::[])
                << Map.toList 
                <| co.syncLabelsNumbersMap
            | MDP  -> [] // TODO: create cases (possibly multiple ones per sync label), partition cases into determinsitic and nondeterministic, in deterministic cases fix the choice, in nondeterministic cases, list the disjunction over the options. If this is done, remove the call to (new)StrategyAssertions
            | _    -> raise (InnerError "Model type not supported in the encoding.")

        let lastElseCase : Expr =
            match co.prismModel.Type with
            | DTMC -> 
                upcast co.z3.MkBV(co.syncLabelsNumbersMap.Item "auxiliarySyncLabel_xkRbUclPoc3mSAShTH5L", co.synchNameChoiceBVSize)
            | MDP  ->
                let globalStrategyHelp : FuncDecl = co.z3.MkFreshFuncDecl("strategy_help",strategyArgsSorts,co.synchNameChoiceSort)
                co.declarations <- globalStrategyHelp :: co.declarations
                co.z3.MkApp(globalStrategyHelp,strategyArgs)
            | _    -> raise (InnerError "Model type not supported in the encoding.")

//        // Original version, caused a naughty error due to the auxiliarySyncLabel
//        let globalStrategyChoice : Expr = 
//            List.fold
//                (fun otherwise (case:BoolExpr, choice:Expr) -> 
//                    co.z3.MkITE(
//                        case, 
//                        choice,
//                        otherwise))
//                lastElseCase
//                deterministicCasesGlobalStrategy
//        let globalStrategyChoiceSimp = globalStrategyChoice.Simplify()

        let globalStrategyChoiceRev : Expr =
            List.foldBack
                (fun (case:BoolExpr, choice:Expr) otherwise -> 
                    co.z3.MkITE(
                        case, 
                        choice,
                        otherwise))
                deterministicCasesGlobalStrategy
                lastElseCase
        let globalStrategyChoiceRevSimp = globalStrategyChoiceRev.Simplify()

//        // Define local strategies (partially)
//        co.solver.Assert(
//            co.z3.MkForall(
//                strategyArgs, 
//                co.z3.MkEq(
//                    co.z3.MkApp(co.localStrategies.Item (m.Name),strategyArgs),
//                    co.z3.MkITE(relevantRanges,
//                        globalStrategyChoice,
//                        co.z3.MkBV(moduleInfo.localChoiceMap.Item auxTrans, moduleInfo.localChoiceBVSize)))))

        let globalStrategyConstraints : BoolExpr = 
            upcast co.z3.MkForall(
                    strategyArgs, 
                    co.z3.MkEq(
                        co.z3.MkApp(co.strategy,strategyArgs),
                        co.z3.MkITE(relevantRanges,
                            globalStrategyChoiceRevSimp,
                            co.z3.MkBV(co.syncLabelsNumbersMap.Item "auxiliarySyncLabel_xkRbUclPoc3mSAShTH5L", co.synchNameChoiceBVSize))))

        // Define local strategies (definition is partial, if model is an MDP)
        let localStrategyConstraints : BoolExpr list  =
            List.map 
                (fun (m:PrismModule) -> 
                    let moduleInfo = co.moduleInfos.Item m.Name
                    let auxTrans : Transition = List.find (fun t -> match t with TDet(s,_,_) | TProb(s,_,_) -> s.Equals "auxiliarySyncLabel_xkRbUclPoc3mSAShTH5L") m.Transitions.Value
            
                    let deterministicCasesLocalStrategy : (BoolExpr * Expr) list =
                        match co.prismModel.Type with
                        | DTMC -> // go through syncLabels and all corresponding transitions: if the global strategy selects the syncLabel and the transitions' guard is enabled, take it. 
                            List.collect
                                (fun (syncLabel:String,globalChoiceNum:int) -> 
                                    List.map
                                        (fun (t:Transition) -> 
                                            match t with 
                                            TDet (_,g,_) | TProb (_,g,_) -> 
                                                (co.z3.MkAnd(Array.ofList
                                                    [co.z3.MkEq(
                                                        co.z3.MkApp(co.strategy,strategyArgs),
                                                        co.z3.MkBV(globalChoiceNum,co.synchNameChoiceBVSize)) ;
                                                        translateBoolExpr co None None g
                                                        ]), 
                                                    upcast co.z3.MkBV(moduleInfo.localChoiceMap.Item t, moduleInfo.localChoiceBVSize)))
                                    <| m.SynchSet.Item syncLabel)
                            << Map.toList 
                            <| co.syncLabelsNumbersMap
                        | MDP  -> 
                            []
                        | _    -> raise (InnerError "Model type not supported in the encoding.")

                    let lastElseCase : Expr =
                        match co.prismModel.Type with
                        | DTMC -> 
                            upcast co.z3.MkBV(moduleInfo.localChoiceMap.Item auxTrans, moduleInfo.localChoiceBVSize)
                        | MDP  ->
                            let localStrategyHelp : FuncDecl = co.z3.MkFreshFuncDecl("strategy_help_"+m.Name, strategyArgsSorts, moduleInfo.localChoiceSort)
                            co.declarations <- localStrategyHelp :: co.declarations
                            co.z3.MkApp(localStrategyHelp,strategyArgs)
                        | _    -> raise (InnerError "Model type not supported in the encoding.")
                
                    let localStrategyChoice : Expr =
                        List.fold
                            (fun otherwise (case:BoolExpr,choice:Expr) -> 
                                co.z3.MkITE(
                                    case, 
                                    choice,
                                    otherwise))
                            lastElseCase
                            deterministicCasesLocalStrategy

                    upcast co.z3.MkForall(
                            strategyArgs, 
                            co.z3.MkEq(
                                co.z3.MkApp(co.localStrategies.Item (m.Name),strategyArgs),
                                co.z3.MkITE(relevantRanges,
                                    localStrategyChoice,
                                    co.z3.MkBV(moduleInfo.localChoiceMap.Item auxTrans, moduleInfo.localChoiceBVSize))))
                )
                co.prismModel.Modules

        let it = z3mkAnd co.z3 <| globalStrategyConstraints::localStrategyConstraints
        it





    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////// Old encoding of strategies ////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//    // STRATEGIES - "new" refers to the fact that it is the second version ... needs to be cleaned up eventually
//    let newStrategyConstraints (co:EncodingContext) : BoolExpr =   
//        let strategyArgs = strategyArgs co
//        let strategyArgsSorts = strategyArgsSorts co
//        let relevantRanges = relevantRanges co
//        let globalStrategyBounds : BoolExpr = // global strategy may only choose existing syncLabels
//            co.z3.MkBVULE(
//                downcast co.z3.MkApp(co.strategy, strategyArgs), 
//                co.z3.MkBV(co.synchNameChoiceCount-1, co.synchNameChoiceBVSize))
//
//        let globalStrategyConstraints : BoolExpr = // This condition expresses that if the global strategy picks an action, there must be choices for the local strategies such that the guards are fulfilled
//            z3mkAnd co.z3 << List.map
//                (fun (syncLabel:String) -> 
////                        let comparisonOperator = 
////                            match co.prismModel.Type with
////                            | DTMC -> co.z3.MkEq
////                            | MDP  -> co.z3.MkImplies
////                            | _    -> raise (InnerError "Model type not supported in the encoding.")
////                        comparisonOperator(
//                    co.z3.MkImplies(
//                        co.z3.MkEq(
//                            co.z3.MkApp(co.strategy,strategyArgs),
//                            co.z3.MkBV(co.syncLabelsNumbersMap.Item syncLabel, co.synchNameChoiceBVSize)),
//                        z3mkAnd co.z3 << List.map
//                            (fun (m:PrismModule) -> 
//                                z3mkOr co.z3 << List.map
//                                    (fun (t:Transition) -> 
//                                        match t with 
//                                        | TDet(_,g,_) | TProb(_,g,_) -> 
//                                            co.z3.MkAnd(Array.ofList
//                                                [co.z3.MkEq(
//                                                    co.z3.MkApp(co.localStrategies.Item(m.Name),strategyArgs),
//                                                    let infos : ModuleInfo = co.moduleInfos.Item(m.Name)
//                                                    co.z3.MkBV(infos.localChoiceMap.Item t, infos.localChoiceBVSize)) ;
//                                                translateBoolExpr co None g // activate to check guards also when selecting global choices
//                                                ]))
//                                    <| (m.SynchSet.Item syncLabel))
//                            <| co.prismModel.Modules
//                        ))
//                << Set.toList 
//                <| co.prismModel.syncLabels
//            
//        let simplifiedGlobalStrategyConstraints : BoolExpr = 
//            co.z3.MkImplies(relevantRanges,globalStrategyConstraints)  
//                    
//        // For the local strategies: 
//        // one assertion per module
//        let simplifiedLocalStrategyConstraints : BoolExpr list = 
//            List.map 
//                (fun (m:PrismModule) -> 
//                    let localStrategy = co.localStrategies.Item m.Name
//                    let moduleInfo = co.moduleInfos.Item m.Name
//                    let transitionConstraints : BoolExpr list = 
//                        List.map 
//                            (fun (choice:int) -> 
//                                let transition = m.Transitions.Value.Item choice
//                                let (synchName, guard) = 
//                                    match transition with
//                                    | TDet (a,b,_) -> (a,b)
//                                    | TProb (a,b,_) -> (a,b)
////                                let comparisonOperator = 
////                                    match co.prismModel.Type with
////                                    | DTMC -> co.z3.MkEq
////                                    | MDP  -> co.z3.MkImplies
////                                    | _    -> raise (InnerError "Model type not supported in the encoding.")
////                                comparisonOperator( // if the local strategy chooses transition i, then guard i must be fulfilled and the globalStrategy module must have chosen the corresponding synch label
//                                co.z3.MkImplies(
//                                    co.z3.MkEq(
//                                        co.z3.MkApp(localStrategy, strategyArgs), 
//                                        co.z3.MkBV(choice,moduleInfo.localChoiceBVSize)), 
////                                    translateBoolExpr co None guard
//                                    co.z3.MkAnd(Array.ofList 
//                                        [
//                                         translateBoolExpr co None guard ; // transition guard 
//                                         co.z3.MkEq(
//                                            co.z3.MkApp(co.strategy, strategyArgs), 
//                                            co.z3.MkBV(co.syncLabelsNumbersMap.Item synchName, co.synchNameChoiceBVSize))])
//                                    ))
//                            [0..moduleInfo.localChoiceCount-1]
//                    let localStrategyConstraints : BoolExpr = 
//                        co.z3.MkAnd(Array.ofList <| 
//                            co.z3.MkBVULE( // the local strategy must choose an existing action 
//                                downcast co.z3.MkApp(localStrategy, strategyArgs), 
//                                co.z3.MkBV(moduleInfo.localChoiceCount-1, moduleInfo.localChoiceBVSize)) 
//                            :: transitionConstraints)
////                    let auxTrans : Transition = List.find (fun t -> match t with TDet(s,_,_) | TProb(s,_,_) -> s.Equals "auxiliarySyncLabel_xkRbUclPoc3mSAShTH5L") m.Transitions.Value
////                    downcast co.z3.MkITE(
////                        relevantRanges, // if
////                        localStrategyConstraints, // then
////                        co.z3.MkEq( // else
////                            co.z3.MkApp(co.localStrategies.Item (m.Name),strategyArgs),
////                            co.z3.MkBV(
////                                moduleInfo.localChoiceMap.Item auxTrans,
////                                moduleInfo.localChoiceBVSize))) 
//                    co.z3.MkImplies(
//                        relevantRanges, 
//                        localStrategyConstraints) 
//                    )
//                co.prismModel.Modules
//
//        // Strategies get individual quantifiers
////        co.solver.Assert( // forall states (and steps), the strategy may only choose existing and enabled transitions, duplicated definitions, to ensure that z3 is fixing a meaningful strategy at some time.
////            co.z3.MkForall(strategyArgs, co.z3.MkAnd(Array.ofList (globalStrategyBounds :: simplifiedGlobalStrategyConstraints :: []))))
////
////        for constr : BoolExpr in simplifiedLocalStrategyConstraints do
////            co.solver.Assert( // forall states (and steps), the local strategy may only choose existing and enabled transitions, duplicated definitions, to ensure that z3 is fixing a meaningful strategy at some time.
////                co.z3.MkForall(strategyArgs, constr))
//
//        // All strategies in one quantifier
//        // forall states (and steps), the local strategy may only choose existing and enabled transitions, duplicated definitions, to ensure that z3 is fixing a meaningful strategy at some time.
//        upcast co.z3.MkForall(
//            strategyArgs, 
//            co.z3.MkAnd(Array.ofList (globalStrategyBounds :: simplifiedGlobalStrategyConstraints :: simplifiedLocalStrategyConstraints)))
//
//            
////        let strategyIsCorrect : FuncDecl = co.z3.MkFuncDecl("strategyAssertions", strategyArgsSorts, co.z3.MkBoolSort())
////        co.solver.Assert( // forall states (and steps), the strategy may only choose existing and enabled transitions, this is the function definition
////            co.z3.MkForall(strategyArgs, 
////                co.z3.MkEq(
////                    co.z3.MkApp(strategyIsCorrect,strategyArgs),
////                    co.z3.MkAnd(Array.ofList (globalStrategyBounds :: simplifiedGlobalStrategyConstraints :: simplifiedLocalStrategyConstraints)))
////            ))
////        strategyIsCorrect
//
//
//    // Creates the constraints that the strategy is only choosing existing actions, and that it only chooses enabled actions
//    let strategyConstraints (co:EncodingContext) : BoolExpr = 
//        
//        let (strategyArgs, strategyArgsSorts) = 
//            match co.problem.configs.StrategyEncoding with
//            | Memoryless         -> 
//                (Array.ofList <| co.sysStateArgs, Array.ofList <| co.sysStateArgsSort)
//            | StateTimeDependent -> 
//                (Array.ofList <| co.stepArg :: co.sysStateArgs, Array.ofList <| co.stepSort :: co.sysStateArgsSort)
//
//        // For the global strategy:
//        let globalStrategyConstraint : BoolExpr = 
//            co.z3.MkBVULE(
//                downcast co.z3.MkApp(co.strategy, strategyArgs), 
//                co.z3.MkBV(co.synchNameChoiceCount-1, co.synchNameChoiceBVSize))
//
//        // For the local strategies: 
//        let localStrategyConstraints : BoolExpr list =  // one boolean expression per module
//            List.map 
//                (fun (m:PrismModule) -> 
//                    let localStrategy = co.localStrategies.Item m.Name
//                    let moduleInfo = co.moduleInfos.Item m.Name
//                    let transitionConstraints : BoolExpr list = 
//                        List.map 
//                            (fun (choice:int) -> 
//                                let transition = m.Transitions.Value.Item choice
//                                let (synchName, guard) = 
//                                    match transition with
//                                    | TDet (a,b,_) -> (a,b)
//                                    | TProb (a,b,_) -> (a,b)
//                                co.z3.MkImplies( // if the local strategy chooses transition i, then guard i must be fulfilled and the globalStrategy module must have chosen the corresponding synch label
//                                    co.z3.MkEq(
//                                        co.z3.MkApp(localStrategy, strategyArgs), 
//                                        co.z3.MkBV(choice,moduleInfo.localChoiceBVSize)), 
//                                    co.z3.MkAnd(Array.ofList 
//                                        [translateBoolExpr co None guard ; // transition guard 
//                                         co.z3.MkEq(
//                                            co.z3.MkApp(co.strategy, strategyArgs), 
//                                            co.z3.MkBV(co.syncLabelsNumbersMap.Item synchName, co.synchNameChoiceBVSize))]
//                                        ))) 
//                            [0..moduleInfo.localChoiceCount-1]
//                    let moduleConstraint = 
//                        co.z3.MkAnd(Array.ofList <| 
//                            co.z3.MkBVULE( // the local strategy must choose an existing action 
//                                downcast co.z3.MkApp(localStrategy, strategyArgs), 
//                                co.z3.MkBV(moduleInfo.localChoiceCount-1, moduleInfo.localChoiceBVSize)) // THIS COMMENT IS NOT VALID ANY MORE: the -1 was removed intentionally from info.localChoiceCount to use the additional value as the null-op
////                            :: co.z3.MkEq( // if, and only if, the module cannot participate with any of its normal transitions in the step, it must choose the null-op, represented by the number info.localChoiceCount
////                                co.z3.MkNot(
////                                    co.z3.MkOr(Array.ofList
////                                        (List.map 
////                                            (fun (key,_) -> 
////                                                co.z3.MkEq(
////                                                    downcast co.z3.MkApp(co.strategy, strategyArgs), 
////                                                    co.z3.MkBV(co.syncActionNumbersMap.Item key, co.synchNameChoiceBVSize)))  
////                                            (Map.toList m.SynchSet) ))),
////                                co.z3.MkEq(
////                                    co.z3.MkApp(localStrategy, strategyArgs), 
////                                    let auxTransPosition : int = List.findIndex (fun TDet (s,_,_) | TProb(s,_,_) -> asdf) m.Transitions // TODO search through the transitions of that module
////                                    in co.z3.MkBV(auxTransPosition,moduleInfo.localChoiceBVSize))) 
//                            :: transitionConstraints)
//                    moduleConstraint)
//                co.prismModel.Modules 
//
//        // forall states (and steps), the strategy may only choose existing and enabled transitions, duplicated definitions, to ensure that z3 is fixing a meaningful strategy at some time.
//        upcast co.z3.MkForall(
//            strategyArgs, 
//            co.z3.MkAnd(Array.ofList (globalStrategyConstraint :: localStrategyConstraints)))
//
//
//    // asserts that the strategy is only choosing actions that exist and that are enabled
//    let fixMDPStrategy (co:EncodingContext) (prismModel:PrismModel) : BoolExpr = 
//        // let strategyCorrectness : FuncDecl = // asserts that the strategy is only choosing actions that exist and that are enabled
//        if prismModel.Type.Equals( MDP ) then
//            match 0 with
//            | 0 -> newStrategyConstraints co
//            | 1 -> strategyConstraints co // old encoding of strategies for comparison
//            | _ -> raise NotYetImplemented
//        else 
//            co.z3.MkTrue()
        
