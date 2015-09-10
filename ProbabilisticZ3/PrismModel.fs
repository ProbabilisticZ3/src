// MN Rabe

namespace ProbabilisticZ3

open System

open Irony.Parsing

open Expressions
open Utils

module PrismModel =

    type Label = String * BoolExpr

    type ModuleType =
        | RegularModule
        | UnmatchedModuleRenaming
        | ModuleRenaming of PrismModule

    and ModelType = DTMC | MDP | CTMC | CTMDP

    and PrismModule (mType:ModuleType, node:ParseTreeNode option, name:String, vars:Variable list option, renaming:String->String, transitions:Transition list option, synchSet:Map<String,Transition list>) = 
        // note the constructor PrismModule.create
        member this.Node : ParseTreeNode option = node 
        member val Name = name with get, set
        member val MType = mType with get, set
        member val Variables : Variable list option = vars with get, set
        member val Renaming : String -> String = renaming with get, set
        member val Transitions : Transition list option = transitions with set, get
        member val SynchSet : Map<String, Transition list> = synchSet with get, set // indicates the mapping of synchronization action to transitions that are sensitive to this action

        static member create (node:ParseTreeNode) : PrismModule = 
            let mType : ModuleType =
                match node.Term.Name with 
                | "Module" -> RegularModule
                | "ModuleRenaming" -> UnmatchedModuleRenaming
                | _ -> invalidArg "node" ("Expected module or module renaming. Read: " + node.Term.Name)
            let rec createRenaming (eqns : ParseTreeNode list) (name:string) : string = 
                match eqns with 
                | [] -> name
                | head :: tail -> 
                    if name.Equals(head.ChildNodes.Item(0).Token.Text)
                    then head.ChildNodes.Item(2).Token.Text
                    else createRenaming tail name
            let renaming : String -> String =
                match mType with 
                | RegularModule -> id
                | UnmatchedModuleRenaming -> createRenaming (toList (node.ChildNodes.Item(5).ChildNodes))
                | ModuleRenaming _ -> raise (InnerError "Module renaming cannot be matched.")
            let name : String = 
                node.ChildNodes.Item(1).Token.Text 
            new PrismModule(mType, Some node, name, None, renaming, None, Map.empty)

    let moduleIsProbabilistic (m:PrismModule) : Boolean = m.Transitions.IsSome && List.exists (fun t -> match t with TProb _ -> true | _ -> false) m.Transitions.Value 

    // General methods start

    let createRenamedVariable (renaming: string -> string) (other:Variable) : Variable = 
        let newName = renaming other.Name
        Variable.createWithName(other.Node.Value, newName)

    let createUpdate (vars:Variable list) (renaming : string -> string) (node:ParseTreeNode) : Update = 
        let varname = renaming (node.ChildNodes.Item(0).Token.Text)
        match varname with
        | "true" -> NoUpdate
        | _ -> 
        let v = List.tryFind (varname.Equals << fun (x:Variable) -> x.Name) vars 
        match v with 
            | Some x -> 
                let e = simplifyExpr vars [] (createExpr vars renaming (node.ChildNodes.Item(3)))
                do if not (typify e = x.DataType) then invalidArg "node" ("Invalid type for update at location " + node.Span.Location.ToString()) else ()
                match e with 
                    | BoolExpr e' -> BoolVarUp (x, e')
                    | IntExpr e' -> IntVarUp (x, e')
                    | DoubleExpr e' -> DoubleVarUp (x, e')
            | None -> invalidArg "node" ("Unknown variable: '" + node.ChildNodes.Item(0).Token.Text + "'.")

    let createPChoice (vars:Variable list) (renaming : string -> string) (node:ParseTreeNode) : PChoice = 
        (createDoubleExpr vars  renaming (node.ChildNodes.Item(0)), List.map (createUpdate vars renaming) (toList (node.ChildNodes.Item(1).ChildNodes)))

    let createTransition (vars:Variable list) (renaming : string -> string) (node:ParseTreeNode) (count:int) : Transition * int = // TODO: check whether several updates for the same variable occur
        let synchActionNode = node.ChildNodes.Item(0).ChildNodes.Item(1)
        let synchActionString = if synchActionNode.ChildNodes.Count = 0 then "" else synchActionNode.ChildNodes.Item(0).Token.Text
        let (synchAction,nextCount) = 
            match synchActionString with
            | "" -> ("UnnamedAction_" + count.ToString(), count+1)
            | x  -> (renaming x,count)
        let guard : BoolExpr = simplifyBoolExpr vars [] (createBoolExpr vars renaming (node.ChildNodes.Item(1)))
        let choicesNode = node.ChildNodes.Item(3)
        match choicesNode.Term.Name with
            | "ProbabilisticChoiceList" -> 
                (TProb (synchAction, guard, List.map (createPChoice vars renaming) (toList choicesNode.ChildNodes)), nextCount)
            | "UpdateList" -> (TDet (synchAction, guard, List.map (createUpdate vars renaming) (toList choicesNode.ChildNodes)), nextCount)
            | x -> invalidArg "node" ("Error in the parse tree. Expected probabilistic choice list or update list but found: '" + x.ToString() + "'.")

    let rec determineVariables  (m : PrismModule) : Variable list = 
        match (m.Variables,m.MType) with
            | (Some vars, _) -> vars
            | (None, RegularModule) -> 
                let nodes : ParseTreeNode list = List.filter (nameIs "Declaration") (toList (m.Node.Value.ChildNodes.Item(2).ChildNodes))
                let letVars = List.map Variable.createVarFromNode nodes
                m.Variables <- Some (List.map Variable.createVarFromNode nodes)
                m.Variables.Value
            | (None, ModuleRenaming other) ->
                let vars = List.map (createRenamedVariable m.Renaming) (determineVariables other)
                m.Variables <- Some vars
                vars
            | (None, UnmatchedModuleRenaming) -> raise (InnerError "Module renamings must be matched before determining the variables.")

    let updateSynchSet (m : PrismModule) (t:Transition) : unit =
        match t with
            | TDet  (s,_,_) | TProb (s,_,_) -> 
                if m.SynchSet.ContainsKey s 
                then m.SynchSet <- m.SynchSet.Add (s, t :: m.SynchSet.Item s)
                else m.SynchSet <- m.SynchSet.Add (s, [t])
                // printfn "Added %A to module %A" s m.Name // Debug output
            //| _ -> ()

    let getTransitions (vars : Variable list) (m : PrismModule) (count:int) : Transition list * int = 
        match (m.Transitions, m.MType) with 
            | (Some ts, _) -> (ts,count)
            | (None, RegularModule) -> 
                let (ts,nextCount) = 
                    List.foldBack 
                        (fun t (ts,count) -> 
                            let (t,c) = createTransition vars m.Renaming t count 
                            in (t :: ts,c)) 
                        (List.filter (nameIs "Command") (toList (m.Node.Value.ChildNodes.Item(2).ChildNodes))) 
                        ([],count)
                m.Transitions <- Some ts
                List.iter (updateSynchSet m) ts
                (ts,nextCount)
            | (None, ModuleRenaming other) -> 
                let (ts,nextCount) = 
                    List.foldBack 
                        (fun t (ts,count) -> 
                            let (t,c) = createTransition vars m.Renaming t count 
                            in (t :: ts,c)) 
                        (List.filter (nameIs "Command") (toList (other.Node.Value.ChildNodes.Item(2).ChildNodes))) 
                        ([],count)
                m.Transitions <- Some ts
                List.iter (updateSynchSet m) ts
                (ts,nextCount)
            | (None, UnmatchedModuleRenaming) -> raise (InnerError "cannot get transitions of an unmatched module renaming")

    let matchUp others (m:PrismModule) : unit =  
        match m.MType with 
            | RegularModule -> ()
            | ModuleRenaming x -> ()
            | UnmatchedModuleRenaming ->
                let opt = List.tryFind (fun (x:PrismModule) -> m.Node.Value.ChildNodes.Item(3).Token.Text.Equals(x.Name)) others in
                match opt with 
                    | Some x -> m.MType <- ModuleRenaming x
                    | None -> invalidArg "this" ("Could not match module renaming " + m.Name + " to any other module.")



    type PrismModel 
            (modelType:ModelType, 
             parseTree:ParseTree, 
             modules:PrismModule list, 
             labels:Label list, 
             auxVariable:Variable option, 
             constants : Variable list, 
             globalVars : Variable list, 
             formulas:Variable list,
             syncVariables:Variable list,
             guardVariables:Variable list,
             updatesVariables: Variable list) = 
        let transitions () = List.collect (fun (m:PrismModule) -> m.Transitions.Value) modules
        let variables () = globalVars @ List.collect (fun (m:PrismModule) -> m.Variables.Value) modules
        member val Type : ModelType              = modelType with get
        member val ParseTree : ParseTree         = parseTree with get 
        member val Vars : unit -> Variable list  = variables with get  // does not contain the constants! they should be replaced already
        member val Modules : PrismModule list    = modules with get
        member val Transitions : unit -> Transition list = transitions with get 
        member val Labels : Label list           = labels with get 
        member val AuxVariable : Variable option = auxVariable with get
        member val syncLabels : Set<String>      = Set.ofList << List.map (fun (t:Transition) -> match t with TDet(s,_,_) | TProb(s,_,_) -> s) <| transitions ()
        member val Constants : Variable list     = constants with get
        member val GlobalVariables : Variable list = globalVars with get
        member val Formulas : Variable list        = formulas with get
        member val SyncVariables : Variable list   = syncVariables with get
        member val GuardVariables : Variable list  = guardVariables with get
        member val PChoiceVariables : Variable list  = updatesVariables with get
        
    let numberOfProbabilisticModules (prismModel:PrismModel) : int = 
        List.fold (fun (n:int) (m:PrismModule) -> if moduleIsProbabilistic m then n+1 else n) 0 prismModel.Modules

    let createPrismModel (fileContent) (externalConstants:Variable list) : PrismModel =
        // 2. Parse
        let parser = new Irony.Parsing.Parser(new PrismParser.PrismGrammar())
        let parseTree = parser.Parse(fileContent)

        do  if (parseTree.HasErrors()) then 
                printf "Parse tree has errors:\n"
                for m in parseTree.ParserMessages do
                    printf "  at %s:\n    %s\n" (m.Location.ToString()) (m.Message.ToString())
                invalidArg "parseTree" ("Parse tree has errors")
            else () // continue as normal
    
        let modelType = 
            match parseTree.Root.ChildNodes.Item(0).ChildNodes.Item(0).Term.Name with
            | "dtmc" | "probabilistic" -> DTMC
            | "mdp"  | "nondeterministic" -> MDP
            | "ctmc" | "stochastic" -> raise NotYetImplemented
            | "ctmdp" -> raise NotYetImplemented
            | "pta" -> raise NotYetImplemented
            | x -> raise (InnerError ("Unexpected model type" + x))
        
        // 3.1 Determine all names of constants 
        let modelConstants = 
            List.map Expressions.Variable.createVarFromNode 
            << List.collect (Utils.depthOneObjects "GlobalConstant") 
            << Utils.toList 
            <| parseTree.Root.ChildNodes

        let constants : Variable list = 
            List.map
                (fun (mC:Variable) -> 
                    let replacement : Variable option = List.tryFind (fun (extC:Variable) -> mC.Name.Equals extC.Name ) externalConstants
                    if replacement.IsSome && mC.ExprNode.IsSome
                    then report_1 5 "Constant %s defined externally and also in the model. Using external definition." mC.Name
                    if mC.ExprNode.IsNone && replacement.IsNone 
                    then raise (ArgumentException ("Undefined constant: " + mC.Name))
                    if replacement.IsSome 
                    then replacement.Value
                    else mC
                    ) 
                    
                modelConstants 

        // 3.2 Determine constants
        do List.iter (parseInitialVal constants id) constants
        let values = List.map (Expressions.evalConst constants []) constants 

        // 3.3 Global variables 
        let globalVars : Variable list = 
            List.map Expressions.Variable.createVarFromNode 
            << List.collect (Utils.depthOneObjects "GlobalVariable") 
            << Utils.toList 
            <| parseTree.Root.ChildNodes

        do List.iter (evalRanges constants) globalVars

        // 3.4 Modules
        let regularModules = 
            List.map PrismModule.create 
            << List.collect (Utils.depthOneObjects "Module") 
            << Utils.toList 
            <| parseTree.Root.ChildNodes

        // 3.5 Renamed modules
        let moduleRenamings = 
            List.map PrismModule.create 
            << List.collect (Utils.depthOneObjects "ModuleRenaming") 
            << Utils.toList 
            <| parseTree.Root.ChildNodes

        let modules = List.append moduleRenamings regularModules

        // 3.6 Match renamed modules
        do List.iter (matchUp modules) moduleRenamings

        // 3.7 Get local variables 
        let localDeclarations = List.collect determineVariables modules
        
        // Get formulas ... according to the semantics of the prism language formulas are expanded BEFORE module renamings are expanded. 
        let formulas : Variable list = 
            List.map Variable.createVarFromNode
            << List.collect (Utils.depthOneObjects "Formula") 
            << Utils.toList 
            <| parseTree.Root.ChildNodes
        
        do List.iter (evalRanges (formulas@constants)) localDeclarations
        
        let allVariables = List.append localDeclarations globalVars
        let allVariablesConstantsAndFormulas = List.concat [formulas; constants; globalVars; localDeclarations]        

        // 3.8 Determine initial values of variables
        // parse initial values of LOCAL variables; calls the simplifier and therefore needs the module's renaming information
        do List.iter (fun (m:PrismModule) -> List.iter (parseInitialVal allVariablesConstantsAndFormulas m.Renaming) m.Variables.Value) modules 
        // parse initial values of GLOBAL variables 
        List.iter (parseInitialVal allVariablesConstantsAndFormulas id) globalVars
        // parse expressions of FORMULAS  
        List.iter (parseInitialVal allVariablesConstantsAndFormulas id) formulas

        // 3.9 Parse transitions
        let (transitions,count) = 
            List.fold 
                (fun (ts, count) m -> 
                    let (t, newcount) = getTransitions allVariablesConstantsAndFormulas m count 
                    (t@ts, newcount)) 
                ([], 0) 
                modules

        let labelNodes : ParseTreeNode list = List.collect (Utils.depthOneObjects "Label") (Utils.toList parseTree.Root.ChildNodes)
        let labels : Label list = 
            List.map 
                (fun (node:ParseTreeNode) -> 
                    (node.ChildNodes.Item(1).Token.ValueString, simplifyBoolExpr allVariablesConstantsAndFormulas [] <| createBoolExpr allVariablesConstantsAndFormulas id (node.ChildNodes.Item(3)))) 
                labelNodes

        PrismModel (
            modelType, 
            parseTree, 
            modules, 
            labels, 
            None, 
            constants, 
            globalVars, 
            formulas, 
            [], [], [])

        
        
    let mkOrList (bs : BoolExpr list) : BoolExpr  = List.foldBack (fun (b:BoolExpr) (state:BoolExpr) -> BoolExpr.Or (state,b)) bs (BoolExpr.B false)
    let mkAndList (bs : BoolExpr list) : BoolExpr = List.foldBack (fun (b:BoolExpr) (state:BoolExpr) -> BoolExpr.And(state,b)) bs (BoolExpr.B true)


    let removeDeadlockedStates_NoAdditionalModule (model:PrismModel) (simplifiedGuardEncoding:bool) : PrismModel = 
        let auxvar = new Variable(None,None,"auxiliaryVariable_xkRbUclPoc3mSAShTH5L", None,TBool,LocalVariable,None)
        let syncLabel = "auxiliarySyncLabel_xkRbUclPoc3mSAShTH5L"
        // That there is a deadlock in a state s means that for every syncLabel there is a participating module such that no guard is enabled for state s. 
        let deadlock : BoolExpr = 
            if simplifiedGuardEncoding
            then B true // an additional requirement is given in the guard encoding (noDeadlock)
            else 
            BoolExpr.Not
            << 
            mkOrList
            << List.map
                (fun (otherModule:PrismModule) -> 
                    mkAndList
                    << List.map
                        (fun (label:String,ts:Transition list) -> 
                            mkOrList 
                            << List.map (fun (t:Transition) -> match t with TDet(_,g,_) | TProb(_,g,_)-> g) 
                            <| ts)
                    <| Map.toList otherModule.SynchSet)
            <| model.Modules

        let auxTransition = TDet (syncLabel, deadlock, [BoolVarUp (auxvar,BoolExpr.B true)])
        let moduleToModify : PrismModule = model.Modules.Head
        let modifiedModule : PrismModule = 
            new PrismModule(
                moduleToModify.MType,
                moduleToModify.Node,
                moduleToModify.Name, 
                Some <| moduleToModify.Variables.Value @ [auxvar], // alternative initial state: Some (BoolExpr.B false)
                moduleToModify.Renaming, 
                Some <| moduleToModify.Transitions.Value @ [auxTransition],
                moduleToModify.SynchSet.Add(syncLabel,auxTransition::[]))

        PrismModel(
            model.Type,
            model.ParseTree,
            modifiedModule :: model.Modules.Tail,
            model.Labels,
            Some auxvar,
            model.Constants,
            model.GlobalVariables,
            model.Formulas,
            model.SyncVariables,
            model.GuardVariables,
            model.PChoiceVariables)


    // Go through all modules, then go through all of their transitions, 
    // then go through all of their updates; if the update does not change a 
    // global variable, the variable must stay constant.  
    // This works under the assumption that global variables are not changed in synchronizing actions
    let preserveGlobalVariables (model:PrismModel) : PrismModel = 
        let globalVarSet : Set<Variable> = Set.ofList model.GlobalVariables
        let extractVar (u:Update) : Variable option = 
            match u with
            | BoolVarUp (v,_) | IntVarUp (v,_) | DoubleVarUp (v,_) -> Some v
            | NoUpdate -> None
        let makeGlobalVarsPreserving (ups:Update list) : Update list =
            let nonUpdatedGlobalVars : Set<Variable> =
                List.fold 
                    (fun (set:Set<Variable>) (u:Update) -> 
                        if (extractVar u).IsNone
                        then set
                        else set.Remove (extractVar u).Value
                        )
                    globalVarSet
                    ups
            let createNonUpdate (v:Variable) : Update = 
                match v.DataType with
                | TInteger -> IntVarUp (v,IntVar v)
                | TDouble  -> DoubleVarUp (v, DoubleVar v)
                | TBool    -> BoolVarUp (v, BoolVar v) 
                | TBD      -> InnerError "Detected typeless variable." |> raise
            (List.map (fun (v:Variable) -> createNonUpdate v) << Set.toList <| nonUpdatedGlobalVars) @ ups
            
        let newModules = 
            List.map
                (fun (m:PrismModule) -> 
                    let (newTransitions : Transition list, newSyncSet) = 
                        List.fold
                            (fun (ts,map:Map<String,Transition list>) (t:Transition) -> 
                                match t with
                                | TDet  (sl,g,ups) -> 
                                    let newT = TDet (sl,g,makeGlobalVarsPreserving ups) // for all global variables: if it is not contained in the updates, preserve it
                                    let oldSlTs = if map.ContainsKey sl then map.Item sl else []
                                    (newT::ts,map.Add(sl,newT::oldSlTs))
                                | TProb (sl,g,pcs) -> 
                                    let newPChoices = List.map (fun (e,ups) -> (e,makeGlobalVarsPreserving ups)) pcs
                                    let newT = TProb (sl,g,newPChoices) // for all pchoices, for all global variables: if it is not contained in the updates of pchoice, preserve it
                                    let oldSlTs = if map.ContainsKey sl then map.Item sl else []
                                    (newT::ts,map.Add(sl,newT::oldSlTs))
                                )
                            ([],Map.empty)
                            m.Transitions.Value

                    new PrismModule(
                        m.MType,
                        m.Node,
                        m.Name, // Name of the module, the string xkRbUclPoc3mSAShTH5L is intended to avoid collisions
                        m.Variables, // alternative initial state: Some (BoolExpr.B false)
                        m.Renaming, 
                        Some newTransitions, 
                        newSyncSet)
                )
                model.Modules
                
        PrismModel(
            model.Type,
            model.ParseTree,
            newModules,
            model.Labels,
            model.AuxVariable,
            model.Constants,
            model.GlobalVariables,
            model.Formulas,
            model.SyncVariables,
            model.GuardVariables,
            model.PChoiceVariables)



    // Every module has to participate in every sync label
    let synchEveryModule (model:PrismModel) : PrismModel = 
        let newModules = 
            List.fold // !!
                (fun (modules:PrismModule list) (syncLabel:String) -> 
                    List.map
                        (fun (m:PrismModule) ->
                            if m.SynchSet.ContainsKey(syncLabel) 
                            then m
                            else 
                                let newTransition : Transition = TDet (syncLabel, BoolExpr.B true, Update.NoUpdate::[])
                                new PrismModule(
                                    m.MType,
                                    m.Node,
                                    m.Name, // Name of the module, the string xkRbUclPoc3mSAShTH5L is intended to avoid collisions
                                    m.Variables, // alternative initial state: Some (BoolExpr.B false)
                                    m.Renaming, 
                                    Some (m.Transitions.Value @ [newTransition]), 
                                    m.SynchSet.Add(syncLabel,newTransition::[])))
                        modules)
                model.Modules
                << Set.toList <| model.syncLabels
        PrismModel(
            model.Type,
            model.ParseTree,
            newModules,
            model.Labels,
            model.AuxVariable,
            model.Constants,
            model.GlobalVariables,
            model.Formulas,
            model.SyncVariables,
            model.GuardVariables,
            model.PChoiceVariables)




    let buildTransitionIdentifier (i:int,j:int) = 
        "module" + i.ToString() + "_tran"+ j.ToString() + "_UclPoc3mSAShT"
    let buildPChoiceIdentifier (i:int,j:int, k:int) = 
        "module" + i.ToString() + "_tran"+ j.ToString() + "_pc" + k.ToString() + "_UclPoc3mSAShT"

    // encodes the Guards as Invariants (formulas)
    let prepareAdvancedDTMCEncoding (model:PrismModel) : PrismModel = 

        let guardVariablesAndPChoiceVariables_withSync : ((string * Variable) * Variable list) list list = 
            List.mapi
                (fun i (m:PrismModule) -> 
                    List.mapi
                        (fun j (t:Transition) -> 
                            let (label:string,guardVar:Variable,pcs:PChoice list) =
                                match t with
                                | TDet (sl, guard, updates) -> 
                                    (sl,
                                     new Variable(None,None,buildTransitionIdentifier (i,j), 
                                            Some (BoolExpr guard),DataType.TBool,VariableType.Guard sl,None),
                                     [(D 1.0,updates)])
                                | TProb (sl, guard, pcs) -> 
                                    (sl,
                                     new Variable(None,None,buildTransitionIdentifier (i,j), 
                                            Some (BoolExpr guard),DataType.TBool,VariableType.Guard sl,None),
                                     pcs)
                            let createPChoiceVar (k:int) (pc:PChoice) : Variable = 
                                new Variable(None,None,buildPChoiceIdentifier (i,j,k), 
                                        Some (BoolExpr <| BoolVar guardVar),DataType.TBool,VariableType.Update pc,None)
                            ((label,guardVar),List.mapi createPChoiceVar pcs)
                        )
                        m.Transitions.Value)
            <| model.Modules

//        let guardVariablesWithSync : (string*Variable) list list = 
//            List.mapi
//                (fun i (m:PrismModule) -> 
//                    List.mapi
//                        (fun j (t:Transition) -> 
//                            match t with 
//                            | TDet (sl, guard, _) | TProb (sl, guard, _) -> 
//                                (sl,new Variable(None,None,buildTransitionIdentifier (i,j), Some (BoolExpr guard),DataType.TBool,VariableType.Guard,None))
//                        )
//                        m.Transitions.Value)
//            <| model.Modules
        
        let guardVariables : Variable list = 
            List.map (fst >> snd) << List.concat <| guardVariablesAndPChoiceVariables_withSync

        let syncVariablesWithSync : (string*Variable) list = 
            List.mapi
                (fun i (labelString:string) ->
                    let participatingTransitions : Variable list list = 
                        List.map (List.map (snd << fst) << List.filter (labelString.Equals << fst << fst)) guardVariablesAndPChoiceVariables_withSync
                    let everyModuleSyncsExpr : BoolExpr = 
                        mkAndList << List.map (mkOrList << List.map BoolExpr.BoolVar)
                        <| participatingTransitions
                    let v = new Variable(None,None,labelString, Some (BoolExpr everyModuleSyncsExpr),DataType.TBool,VariableType.Sync labelString,None)
                    (labelString,v) )
            << Set.toList
            <| model.syncLabels

        let syncVariables = List.map snd syncVariablesWithSync
        
        let pchoiceVariables : Variable list = 
            List.concat << List.map snd << List.concat <| guardVariablesAndPChoiceVariables_withSync

        PrismModel(
            model.Type,
            model.ParseTree,
            model.Modules,
            model.Labels,
            model.AuxVariable,
            model.Constants,
            model.GlobalVariables,
            model.Formulas,
            model.SyncVariables @ syncVariables, 
            model.GuardVariables @ guardVariables,
            model.PChoiceVariables @ pchoiceVariables )


    let readPrismFile filePath (externalConstants:Variable list) (simplifiedGuardEncoding:bool) : PrismModel =
        report_1 5 "   file %s" filePath
        report_0 2 "Reading the Prism file ..."
        let fileContent = 
            try System.IO.File.ReadAllText(filePath) 
            with e -> printfn "%A" e.Message; raise e
        let prismModel = createPrismModel fileContent externalConstants 
        report_0 2 "Successfully read and parsed the Prism file."

        report_1 2 "  %A modules." prismModel.Modules.Length
        report_1 2 "  %A variables." (prismModel.Vars().Length)
        report_1 2 "  %A guarded commands." (prismModel.Transitions().Length)

        report_0 2 "Removing deadlocks."
        let prismModel = removeDeadlockedStates_NoAdditionalModule prismModel simplifiedGuardEncoding
                
        report_0 2 "Synchronizing global variables."
        let prismModel = preserveGlobalVariables prismModel

        report_0 2 "Adding implicite transitions."
        let prismModel = synchEveryModule prismModel 

        let prismModel = 
            if simplifiedGuardEncoding 
            then 
                report_0 2 "Adding variables for synchronization and guards (DTMC encoding)."
                prepareAdvancedDTMCEncoding prismModel
            else prismModel
            
        prismModel  
