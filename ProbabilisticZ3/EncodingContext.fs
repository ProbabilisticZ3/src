// MN Rabe

namespace ProbabilisticZ3

open System

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open SolverConfigs
open Problems

module EncodingContext =

    type AbstractionType = UNDERAPPROX | OVERAPPROX

    type ModuleInfo = {
        localChoiceBVSize : uint32
        localChoiceSort : Sort
        localChoiceCount : int
        localRandomVars : Expr list
        localRandomVar_arg : Expr option
        localRandomBVSize : uint32
        localRandomSort : Sort
        variables : Expr list list
        variables_arg : Expr list
        variables_arg' : Expr list
        variableSorts : Sort list
        localChoiceMap : Map<Transition,int>
    }


    type EncodingContext = {
        z3:Context
        problem:Problem
        prismModel:PrismModel

        moduleNumbersMap : Map<String,int> // maps module names to their internal number
        moduleNumbersMapInverse : Map<int,String> // maps module names to their internal number
        moduleInfos : Map<String,ModuleInfo> // maps module names to encoding information

        // debug information
        mutable declarations : FuncDecl list

        intBVSize    : uint32 
        intSort      : Sort 
        doubleBVSize : uint32
        doubleSort   : Sort
        randomBVSize : uint32 
        randomSort   : Sort 
        stepBVSize   : uint32
        stepSort     : Sort 
        stepArg      : Expr
        positionBVSize     : uint32 
        positionSort       : Sort 
        moduleNumberBVSize : uint32 
        moduleNumberSort   : Sort 
        moduleNumberSortMaxValue : BitVecExpr 
        
        synchNameChoiceCount   : int 
        synchNameChoiceBVSize  : uint32 
        synchNameChoiceSort    : Sort 
        syncLabelsNumbersMap   : Map<String,int> // maps synchronization labels to their internal number
        strategy         : FuncDecl
        localStrategies  : Map<String,FuncDecl>

        transitionRelation : FuncDecl
        variableRangeFunction : FuncDecl
        distributions : FuncDecl list
        formulaDefinitions : FuncDecl
        guardDefinitions : FuncDecl

        randomArgs       : Expr list 
        randomArgSorts   : Sort list
        randomVars       : Expr list list // one set of variables for each step
        randomVarsSorts  : Sort list list

        sysStateArgs     : Expr list  // as argument in step functions
        sysStateArgs'    : Expr list  // as argument for the next step's variables in the transition _relation_
        sysStateArgsSorts : Sort list 
        sysStateVars     : Expr list list // one set of variables for each step
        sysStateVarsSort : Sort list list
        
        syncGuardArgs : Expr list
        syncGuardArgsSorts : Sort list
        syncGuardVars : Expr list list
        syncGuardVarsSorts : Sort list list 

        formulaArgs : Expr list
        formulaArgsSorts : Sort list
        formulaVars : Expr list list
        formulaVarsSorts : Sort list list 
        
        pChoiceArgs : Expr list 
        pChoiceArgsSorts : Sort list 
        pChoiceVars : Expr list list 
        pChoiceVarsSorts : Sort list list 

        // Useful constants
        stepZero   : BitVecExpr 
        stepOne    : BitVecExpr 
//        stepMax    : BitVecExpr
        randomZero : BitVecExpr
        randomMax  : BitVecExpr
        doubleZero : BitVecExpr
        doubleOne  : BitVecExpr
        }


    let getZ3Sort (co:EncodingContext) (v:Variable) : Sort = 
        match v.DataType with
        | TInteger -> co.intSort
        | TBool    -> upcast co.z3.MkBoolSort()
        | TDouble  -> co.doubleSort
        | TBD      -> raise (InnerError "Unexpectedly a variable did not have a type during the construction of a Z3 instance.")



    let variable2Z3ConstName_arg_next (v:Variable) : string = 
        "var_"+v.Name+"_arg_next" 

    let variable2Z3ConstName_arg (v:Variable) : string = 
        "var_"+v.Name+"_arg" 

    let variable2Z3ConstName_step (v:Variable) (step:int) : string = 
        "var_" + v.Name + "_" + step.ToString()

    let variable2Z3Const_arg (co:EncodingContext) (v:Variable) : Expr = 
        co.z3.MkConst(variable2Z3ConstName_arg v, getZ3Sort co v)

    let variable2Z3Const_arg_next (co:EncodingContext) (v:Variable) : Expr = 
        co.z3.MkConst(variable2Z3ConstName_arg_next v, getZ3Sort co v)

    let variable2Z3Const_step (co:EncodingContext) (v:Variable) (step:int) : Expr = 
        co.z3.MkConst(variable2Z3ConstName_step v step, getZ3Sort co v)
        
        

    let initializeContext (problem:Problem) (prismModel:PrismModel) (z3:Context) : EncodingContext = 

        // Create Random variable for module, resolution is statically determined by now
        let randomBVSize = uint32(problem.fractionsEncoding)
        let randomSort = z3.MkBitVecSort(randomBVSize)

        let stepBVSize : uint32 = max 1u <| Convert.ToUInt32 (ceil (log (Convert.ToDouble (problem.GlobalStepBound+1)) / log 2.0)) //Convert.ToUInt32 (ceil ( log (Convert.ToDouble (problem.StepBound+1)) / log 2.0)) ;
        let stepSort : Sort     = upcast z3.MkBitVecSort(stepBVSize) 
        let stepArg : Expr      = z3.MkConst("stepArg", stepSort)

        let intBVSize : uint32       = uint32(problem.intEncoding)
        let intSort : Sort           = upcast z3.MkBitVecSort(intBVSize)
        let doubleBVSize : uint32    = uint32(problem.fractionsEncoding + problem.intEncoding)
        let doubleSort:Sort          = upcast z3.MkBitVecSort(uint32(doubleBVSize))

        // 5.3.1 Create mapping from synch names to lists of participating modules
        let synchNames : Set<string> = List.fold (fun (set:Set<string>) -> fun x -> match x with | TDet (y,_,_) -> set.Add y | TProb (y,_,_) -> set.Add y ) Set.empty (prismModel.Transitions())
        let findParticipating (map:Map<String,PrismModule list>) (s:string) : Map<String,PrismModule list> = 
            map.Add(s, List.filter (fun (pmod:PrismModule) -> pmod.SynchSet.ContainsKey s) prismModel.Modules)
        let participatingModules = Set.fold findParticipating Map.empty synchNames // quadratic in the number of modules! can be improved
        let synchNumbers : Map<String,int> = Map.ofList (List.zip (Set.toList synchNames) [0..synchNames.Count-1])
        let synchNameChoiceBVSize = max 1u <| Convert.ToUInt32 (ceil (log (Convert.ToDouble (synchNames.Count)) / log 2.0)) 
        let synchNameChoiceSort:Sort = upcast z3.MkBitVecSort(synchNameChoiceBVSize) 

        // This method is duplicated, since we need one global variant that need a Z3Context object, but this object is just being build.
        let getZ3Sort (v:Variable) : Sort = 
            match v.DataType with
            | TInteger -> intSort
            | TBool    -> upcast z3.MkBoolSort()
            | TDouble  -> doubleSort
            | TBD      -> raise (InnerError "Unexpectedly a variable did not have a type during the construction of a Z3 instance.")

        let initializeModuleInformation (m:PrismModule) : ModuleInfo =  
            // 1.1.1 create a choice variable that selects a transition
            let localRandomVars : Expr list = 
                if moduleIsProbabilistic m
                then 
                    List.map 
                        (fun step -> z3.MkConst("localRandom_" + m.Name + "_" + step.ToString(), randomSort)) 
                        [0..problem.GlobalStepBound-1]
                else
                    []
            let localRandomVar_arg : Expr option =             
                if moduleIsProbabilistic m
                then 
                    // to be used inside step function declarations
                    Some (z3.MkConst("localRandom_" + m.Name + "_arg", randomSort))
                else 
                    None
                
            //report_2 1 "Module %A has %d transitions." m.Name m.Transitions.Value.Length
            let localChoiceBVSize = max 1u (Convert.ToUInt32 (ceil ( log (Convert.ToDouble (m.Transitions.Value.Length)) / log 2.0))) 
            let localChoiceSort = z3.MkBitVecSort(localChoiceBVSize) :> Sort
            
            let localChoiceMap : Map<Transition,int> = Map.ofList << snd << List.fold (fun (num:int,tr:(Transition*int) list) (t:Transition) -> (num+1,(t,num)::tr)) (0,[]) <| m.Transitions.Value 

            let variables : Expr list list = 
                List.map 
                    (fun step -> List.map (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_step var step, getZ3Sort var)) m.Variables.Value)
                    [0..problem.GlobalStepBound]

            let variables_arg = List.map (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg var, getZ3Sort var)) m.Variables.Value
            let variables_arg' = List.map (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg_next var, getZ3Sort var)) m.Variables.Value
            let variableSorts = List.map getZ3Sort m.Variables.Value
            
            {
            localChoiceBVSize  = localChoiceBVSize ;
            localChoiceSort    = localChoiceSort ;
            localChoiceCount   = m.Transitions.Value.Length
            localRandomVars    = localRandomVars ;
            localRandomVar_arg = localRandomVar_arg ;
            localRandomBVSize  = randomBVSize ;
            localRandomSort    = randomSort ;
            variables          = variables ; 
            variables_arg      = variables_arg ; 
            variables_arg'     = variables_arg' ; 
            variableSorts      = variableSorts ;
            localChoiceMap     = localChoiceMap 
            }

        let moduleInfos = 
            Map.ofList 
            << List.map (fun (m:PrismModule) -> (m.Name, initializeModuleInformation m)) 
            <| prismModel.Modules

        let mutable declarations : FuncDecl list = []

        let randomArgs : Expr list = 
            let tmp =
                List.collect 
                    (fun (m:PrismModule) -> Option.toList (moduleInfos.Item(m.Name).localRandomVar_arg)) 
                    prismModel.Modules
            if tmp.IsEmpty 
            then 
                [z3.MkConst("dummyRandomVar_arg",z3.MkBitVecSort(randomBVSize))]
            else tmp

        // Create random variables
        let randomArgSorts : Sort list = 
            List.map 
                (fun (e:Expr) -> e.Sort)
                randomArgs 
        let randomVars : Expr list list = 
            let allRandomVars : Expr list list = 
                List.filter (fun (es:Expr list) -> not es.IsEmpty ) 
                << List.map (fun (m:PrismModule) -> moduleInfos.Item(m.Name).localRandomVars) 
                <| prismModel.Modules
            if allRandomVars.IsEmpty 
            then 
                let dummyRandomVars : Expr list = 
                    List.map 
                        (fun (step:int) -> z3.MkConst("dummyRandomVar_step_"+step.ToString(),z3.MkBitVecSort(randomBVSize))) 
                        [0..problem.GlobalStepBound-1] // this variable makes sure that there is at least one random variable to quantify over. This makes several special cases obsolete. 
                transpose [dummyRandomVars]
            else transpose allRandomVars 
        let randomVarsSorts : Sort list list = List.map (List.map (fun (e:Expr) -> e.Sort)) randomVars

        // Create global variables
        let globalSysVars : Expr list list = 
            List.map 
                    (fun step -> 
                        List.map 
                            (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_step var step, getZ3Sort var))
                            prismModel.GlobalVariables)
                    [0..problem.GlobalStepBound]
        let globalSysVarsArgs : Expr list = 
            List.map 
                (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg var, getZ3Sort var)) 
                prismModel.GlobalVariables 
        let globalSysVarsArgs' : Expr list = 
            List.map 
                (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg_next var, getZ3Sort var)) 
                prismModel.GlobalVariables 
        
        // Variables describing system state, used when quantifying over all sequences of states
        let sysStateVars : Expr list list = // copies for all variables and all steps
            let localVariables : Expr list list list = // These variables are in the order 'module, step, vars', but we need them in the oder 'step, (module, vars)'
                List.map 
                    (fun (m:PrismModule) -> moduleInfos.Item(m.Name).variables) 
                    prismModel.Modules
            let allVariables : Expr list list list = globalSysVars :: localVariables // includes the global Variables as if they belonged to another module
            let transposedVars : Expr list list list = // this is still in format 'step, module, vars'
                transpose allVariables 
            List.map List.concat transposedVars
        let sysStateVarsSort : Sort list list = List.map (List.map (fun (e:Expr) -> e.Sort)) sysStateVars 

        // Variables describing system state, used as arguments for single step functions etc
        let sysStateArgs : Expr list = 
            globalSysVarsArgs
            @ List.collect 
                (fun (m:PrismModule) -> moduleInfos.Item(m.Name).variables_arg) 
                prismModel.Modules
        let sysStateArgs' : Expr list = 
            globalSysVarsArgs'
            @ List.collect 
                (fun (m:PrismModule) -> moduleInfos.Item(m.Name).variables_arg') 
                prismModel.Modules
        let sysStateArgsSorts : Sort list = 
            List.map (fun (e:Expr) -> e.Sort) 
            <| sysStateArgs


        let syncGuardArgs : Expr list = 
            List.map 
                (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg var, getZ3Sort var)) 
            << List.concat
            <| [prismModel.SyncVariables ; prismModel.GuardVariables]
        let syncGuardArgsSorts : Sort list = 
            List.map (fun (e:Expr) -> e.Sort) 
            <| syncGuardArgs

        let syncGuardVars : Expr list list = 
            List.map
                (fun (step:int) ->
                    List.map 
                        (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_step var step, getZ3Sort var)) 
                    << List.concat
                    <| [prismModel.SyncVariables ; prismModel.GuardVariables])
                [0..problem.GlobalStepBound]
        let syncGuardVarsSorts : Sort list list = 
            List.map (List.map (fun (e:Expr) -> e.Sort))
            <| syncGuardVars



        let formulaArgs : Expr list = 
            List.map 
                (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg var, getZ3Sort var)) 
                prismModel.Formulas 
        let formulaArgsSorts : Sort list = 
            List.map (fun (e:Expr) -> e.Sort) 
            <| formulaArgs

        let formulaVars : Expr list list = 
            List.map
                (fun (step:int) ->
                    List.map 
                        (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_step var step, getZ3Sort var)) 
                        prismModel.Formulas)
                [0..problem.GlobalStepBound]
        let formulaVarsSorts : Sort list list = 
            List.map (List.map (fun (e:Expr) -> e.Sort))
            <| formulaVars


        let pChoiceArgs : Expr list = 
            List.map 
                (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_arg var, getZ3Sort var)) 
                prismModel.PChoiceVariables
        let pChoiceArgsSorts : Sort list = 
            List.map (fun (e:Expr) -> e.Sort) 
            <| pChoiceArgs

        let pChoiceVars : Expr list list = 
            List.map
                (fun (step:int) ->
                    List.map 
                        (fun (var:Variable) -> z3.MkConst(variable2Z3ConstName_step var step, getZ3Sort var)) 
                        prismModel.PChoiceVariables)
                [0..problem.GlobalStepBound]
        let pChoiceVarsSorts : Sort list list = 
            List.map (List.map (fun (e:Expr) -> e.Sort))
            <| pChoiceVars


        // Strategy
        let strategyArgsSorts = 
            match problem.configs.StrategyEncoding with
            | Memoryless         -> Array.ofList <| sysStateArgsSorts
            | StateTimeDependent -> Array.ofList <| stepSort :: sysStateArgsSorts
        let strategy : FuncDecl = 
            z3.MkFuncDecl("strategy", strategyArgsSorts, synchNameChoiceSort)

        declarations <- strategy :: declarations

        let localStrageies : Map<String,FuncDecl> = 
            Map.ofList 
            << List.map (fun (m:PrismModule) -> (m.Name, z3.MkFuncDecl("localStrategy_" + m.Name, strategyArgsSorts, moduleInfos.Item(m.Name).localChoiceSort)))
            <| prismModel.Modules

        for (_,decl) in Map.toList localStrageies do
            declarations <- decl :: declarations

        let transitionRelationArgsSort = randomArgSorts @ sysStateArgsSorts @ sysStateArgsSorts @ formulaArgsSorts @ syncGuardArgsSorts @ pChoiceArgsSorts

        let transitionRelation : FuncDecl = 
            z3.MkFuncDecl(
                "TransitionRelation",
                Array.ofList (stepSort :: transitionRelationArgsSort), 
                z3.MkBoolSort() :> Sort)
        declarations <- transitionRelation :: declarations
        
        let formulaDefinitions : FuncDecl = z3.MkFuncDecl("formulaDefinitions",Array.ofList (sysStateArgsSorts @ formulaArgsSorts),z3.MkBoolSort())
        declarations <- formulaDefinitions :: declarations

        let guardDefinitions : FuncDecl = z3.MkFuncDecl("guardDefinitions",Array.ofList (sysStateArgsSorts @ formulaArgsSorts @ syncGuardArgsSorts),z3.MkBoolSort())
        declarations <- guardDefinitions :: declarations

        let variableRangeFunction : FuncDecl = 
            z3.MkFuncDecl(
                "VariableRanges",
                Array.ofList sysStateArgsSorts, 
                z3.MkBoolSort() :> Sort)
        declarations <- variableRangeFunction :: declarations

        let distributions : FuncDecl list =
            List.map
                (fun (step:int) -> 
                    let distribution = z3.MkFuncDecl("distribution_step_" + step.ToString(), Array.ofList << List.concat <| (take step randomVarsSorts), z3.MkBoolSort())
                    distribution)
                [1..problem.GlobalStepBound]

        declarations <- distributions @ declarations


        let stepZero:BitVecExpr = upcast z3.MkBV(0, stepBVSize)
        let stepOne:BitVecExpr = upcast z3.MkBV(1, stepBVSize)
//        let stepMax:BitVecExpr = upcast z3.MkBV(ac.CurrentStepBound-1,stepBVSize)
        let randomZero:BitVecExpr = upcast z3.MkBV(0, randomBVSize)
        let randomMax:BitVecExpr = upcast z3.MkBV(Convert.ToUInt32(2.0**Convert.ToDouble(randomBVSize)-1.0), randomBVSize) // can cause problems if randomBVSize is too large
        let doubleZero:BitVecExpr = upcast z3.MkBV(0, doubleBVSize)
        let doubleOne:BitVecExpr = downcast (z3.MkBVSHL (z3.MkBV(1, doubleBVSize), z3.MkBV(problem.fractionsEncoding, doubleBVSize))).Simplify()

        let moduleNumberBVSize = max 1u (Convert.ToUInt32 (ceil ( log (Convert.ToDouble (prismModel.Modules.Length)) / log 2.0)))
        let moduleNumberSort = z3.MkBitVecSort(moduleNumberBVSize)
        let moduleNumberSortMaxValue = z3.MkBV(prismModel.Modules.Length-1,moduleNumberBVSize)
//        let moduleWithMaxLocalRandomBVSize = List.maxBy (fun (m:PrismModule) -> moduleInfos.Item(m.Name).localRandomBVSize) prismModel.Modules // max_{m in modules} localRandomBVSize_m
//        let maxLocalRandomBVSize = moduleInfos.Item(moduleWithMaxLocalRandomBVSize.Name).localRandomBVSize
        let positionBVSize : uint32 = max 1u (Convert.ToUInt32 (ceil ( log (Convert.ToDouble (randomBVSize)) / log 2.0)))
        let positionSort : Sort = upcast z3.MkBitVecSort(positionBVSize)


        {z3 = z3 ;
        problem = problem;
        prismModel = prismModel ;

        moduleNumbersMap = 
            Map.ofList 
                (List.zip (List.map (fun (m:PrismModule) -> m.Name) prismModel.Modules) [0..prismModel.Modules.Length-1]) ; // maps module names to their internal number, only needed as debuggin information
        moduleNumbersMapInverse = 
            Map.ofList 
            << List.zip
               [0..prismModel.Modules.Length-1] 
            << List.map (fun (m:PrismModule) -> m.Name) 
            <| prismModel.Modules ;
        moduleInfos = moduleInfos ;// maps module names to encoding information

        declarations = declarations ;

        intBVSize    = intBVSize ;
        intSort      = intSort ;
        doubleBVSize = doubleBVSize ;
        doubleSort   = doubleSort ;
        randomBVSize = randomBVSize ;
        randomSort   = randomSort ;
        stepBVSize   = stepBVSize ;
        stepSort     = stepSort ;
        stepArg      = z3.MkConst("step", stepSort) ;
        positionBVSize     = positionBVSize ;
        positionSort       = positionSort ;
        moduleNumberBVSize = moduleNumberBVSize ;
        moduleNumberSort   = moduleNumberSort ;
        moduleNumberSortMaxValue = moduleNumberSortMaxValue ;
        
        synchNameChoiceCount   = synchNames.Count;
        synchNameChoiceBVSize  = synchNameChoiceBVSize ;
        synchNameChoiceSort    = synchNameChoiceSort ;
        syncLabelsNumbersMap   = synchNumbers ; // maps synchronization labels to their internal number
        strategy = strategy ;
        localStrategies = localStrageies ;

        transitionRelation = transitionRelation ;
        variableRangeFunction = variableRangeFunction ;
        distributions = distributions ;
        formulaDefinitions = formulaDefinitions ;
        guardDefinitions = guardDefinitions ;

        randomArgs       = randomArgs ;
        randomArgSorts   = randomArgSorts ; 
        randomVars       = randomVars ;
        randomVarsSorts  = randomVarsSorts ;
        sysStateArgs     = sysStateArgs ;
        sysStateArgs'    = sysStateArgs' ;
        sysStateArgsSorts = sysStateArgsSorts ; 
        sysStateVars     = sysStateVars ;
        sysStateVarsSort = sysStateVarsSort ;

        syncGuardArgs = syncGuardArgs ;
        syncGuardArgsSorts = syncGuardArgsSorts ;
        syncGuardVars = syncGuardVars ;
        syncGuardVarsSorts = syncGuardVarsSorts ;

        formulaArgs = formulaArgs ;
        formulaArgsSorts = formulaArgsSorts ;
        formulaVars = formulaVars ;
        formulaVarsSorts = formulaVarsSorts ;

        pChoiceArgs = pChoiceArgs ;
        pChoiceArgsSorts = pChoiceArgsSorts ;
        pChoiceVars = pChoiceVars ;
        pChoiceVarsSorts = pChoiceVarsSorts ;

        // Useful constants
        stepZero   = stepZero ;
        stepOne    = stepOne ;
//        stepMax    = stepMax ;
        randomZero = randomZero ;
        randomMax  = randomMax ;
        doubleZero = doubleZero ;
        doubleOne  = doubleOne ;
        }



    let rec matchRandomVariablesToModules (co:EncodingContext) (randomVars:'a list) (modules:PrismModule list) : ('a option) list = 
        match modules with
        | m::mr -> 
            if   co.moduleInfos.Item(m.Name).localRandomVar_arg.IsSome 
            then Some randomVars.Head :: matchRandomVariablesToModules co randomVars.Tail mr
            else None :: matchRandomVariablesToModules co randomVars mr
        | [] -> assert(randomVars.IsEmpty); [] 