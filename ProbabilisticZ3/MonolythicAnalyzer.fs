// CM Wintersteiger, MN Rabe

namespace ProbabilisticZ3

open System
open System.IO
open System.Diagnostics
open System.Collections.Generic

open PrismModel
open Utils
open Tactics_Monolythic
open Tactics
open Microsoft.Z3
open EncodingContext
open Results
open Problems
open AnalyzerContexts
open AnalyzerContextEncodings
open Cubes
open Paths
open CounterExamples


module MonolythicAnalyzer = 

    let rec findCubes (ac:AnalyzerContext) (curMax:int) (curCS:int) : AnalyzerContext = 
        report_1 4 "Searching for cube of size %d" curCS
        let cubeOpt = findCube ac curCS
        match cubeOpt with 
        | Some cube -> 
            report_1 4 "Found a cube of size %d" curCS
            let ac = 
                if curCS<ac.LargestCubeSizeFound 
                then { ac with LargestCubeSizeFound = curCS}
                else ac 
            ac.PositiveCubes <- cube::ac.PositiveCubes
            ac.AccumulatedProbability <- ac.AccumulatedProbability+2.0**(-Convert.ToDouble(curCS))
            if satisfiesBound ac 
            then ac // we are done!!
            else findCubes ac curMax curCS
        | None  -> 
            report_1 4 "No cube of size %d left in current abstraction" curCS
            if ac.LargestCubeSizeFound<>Int32.MaxValue && curCS>=ac.LargestCubeSizeFound+ac.CubeSizeSpread || curCS>=curMax
            then ac // nothing could be found. terminate search. 
            else findCubes ac curMax (curCS+1) 


    let relevancyReduction (ac:AnalyzerContext) (stepToCheckFor:int): AnalyzerContext =
        let temp_stepBound = ac.CurrentStepBound
        ac.CurrentStepBound <- stepToCheckFor

        let rec findNextRelevantBit (ac:AnalyzerContext) : AnalyzerContext = 
            let res = checkRelevancy ac stepToCheckFor
            match res with 
            | Some (step:int,mNum:int,pos:int) -> // found an example that proves the relevancy for this bit
                ac.RelevantBits <- ac.RelevantBits.Add (step,mNum,pos)
                findNextRelevantBit ac
            | None -> // terminate search, there are no more relevant bits at the moment
                // update also irrelevant bits: all bits within the current bitRelevancy 
                // and until the stepToCheckFor that have not been declared relevant can 
                // be declared irrelevant. 
                for step in [0..stepToCheckFor-1] do
                    for mNum in [0..ac.co.prismModel.Modules.Length-1] do
                        for pos in [ac.co.problem.fractionsEncoding - ac.BitRelevancy .. ac.co.problem.fractionsEncoding-1] do
                            if not <| ac.RelevantBits.Contains (step,mNum,pos)
                            then ac.IrrelevantBits <- ac.IrrelevantBits.Add (step,mNum,pos)
            
                ac  // end of match clause and function definition

        let ac = findNextRelevantBit ac
        ac.CurrentStepBound <- temp_stepBound
        ac




        
    let analyze_precisionAverse (problem:Problem) (prismModel:PrismModel) : Result = 
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable abstraction = initialAC co
        let maxGlobalCubeSize = max 1 (problem.fractionsEncoding * problem.GlobalStepBound * numberOfProbabilisticModules prismModel)
        let initialMaxCubeSize : int = 
            if problem.ProbabilityBound.IsSome 
            then max 1 ((Convert.ToInt32( ceil ( - (log (fst problem.ProbabilityBound.Value)) / log 2.0))))
            else min 10 maxGlobalCubeSize  // magic constant
        for maxCubeSizeSpread in [2..maxGlobalCubeSize-(initialMaxCubeSize)] do  // magic constant
            if satisfiesBound abstraction then () else
            abstraction.CubeSizeSpread <- maxCubeSizeSpread
            for bitRelevancy : int in [1..problem.fractionsEncoding] do
                if satisfiesBound abstraction then () else
                abstraction.BitRelevancy <- bitRelevancy
                abstraction <- relevancyReduction abstraction problem.GlobalStepBound
                for step : int in [1..problem.GlobalStepBound] do
                    if satisfiesBound abstraction then () else
                    abstraction.CurrentStepBound <- step
                    let curMax = initialMaxCubeSize + maxCubeSizeSpread   // magic constant
                          //((abstraction.CurrentStepBound * abstraction.BitRelevancy * numberOfProbabilisticModules prismModel))
                    let minimalCubeSize = // magic constant
                            max (initialMaxCubeSize-1) 
                                (max (numberOfProbabilisticModules prismModel) (bitRelevancy))   
                    report_1 4 "Checking abstraction: %s" (printAbstraction_short abstraction)
                    // is there any path reaching the goal in precisely n steps?
                    let res : Path option = findSinglePath abstraction None false true
                    match res with 
                    | Some _    -> abstraction <- findCubes abstraction curMax minimalCubeSize
                    | None      -> report_0 4 "No path found for current abstraction."
        
        report_1 5 "Probability mass found: %s " (abstraction.AccumulatedProbability.ToString())
        if problem.ProbabilityBound.IsNone then UNKNOWN
        elif satisfiesBound abstraction then HOLDS 
        else VIOLATED


    let analyze_stepAverse (problem:Problem) (prismModel:PrismModel) : Result = 
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable abstraction = initialAC co

        let maxGlobalCubeSize = max 1 (problem.fractionsEncoding * problem.GlobalStepBound * numberOfProbabilisticModules prismModel)
        let initialMaxCubeSize : int = 
            if problem.ProbabilityBound.IsSome 
            then max 1 ((Convert.ToInt32( ceil ( - (log (fst problem.ProbabilityBound.Value)) / log 2.0))))
            else min 10 maxGlobalCubeSize  // magic constant

        for maxCubeSizeSpread in [2..maxGlobalCubeSize-initialMaxCubeSize] do  // magic constant
            if satisfiesBound abstraction then () else
            abstraction.CubeSizeSpread <- maxCubeSizeSpread
            for step : int in [1..problem.GlobalStepBound] do
                if satisfiesBound abstraction then () else
                abstraction.CurrentStepBound <- step
                let res = findSinglePath abstraction None false true
                match res with 
                | Some _    -> 
                    for bitRelevancy : int in [1..problem.fractionsEncoding] do
                        if satisfiesBound abstraction then () else
                        abstraction.BitRelevancy <- bitRelevancy
                        abstraction <- relevancyReduction abstraction problem.GlobalStepBound
                        let curMax = initialMaxCubeSize + maxCubeSizeSpread  // magic constant
                                //((abstraction.CurrentStepBound * abstraction.BitRelevancy * numberOfProbabilisticModules prismModel))
                        let minimalCubeSize = max initialMaxCubeSize (max (numberOfProbabilisticModules prismModel) (bitRelevancy)) // magic constant
                        report_1 4 "Checking abstraction: %s" (printAbstraction_short abstraction)
                        // is there any path reaching the goal in precisely n steps?
                        abstraction <- findCubes abstraction curMax minimalCubeSize
                | None -> report_0 4 "No path found for current step depth."
        
        report_1 5 "Probability mass found: %s " (abstraction.AccumulatedProbability.ToString())
        if problem.ProbabilityBound.IsNone then UNKNOWN
        elif satisfiesBound abstraction then HOLDS 
        else VIOLATED


    let analyze_stepAverse2 (problem:Problem) (prismModel:PrismModel) : Result = 
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable abstraction = initialAC co

        let maxGlobalCubeSize = max 1 (problem.fractionsEncoding * problem.GlobalStepBound * numberOfProbabilisticModules prismModel)
        let initialMaxCubeSize : int = 
            if problem.ProbabilityBound.IsSome 
            then max 1 ((Convert.ToInt32( ceil ( - (log (fst problem.ProbabilityBound.Value)) / log 2.0))))
            else min 3 maxGlobalCubeSize // magic constant

        let mutable maxCubeSizeSpread = 4 // magic constant
        let mutable step = 1 
        let mutable continueLooping : bool = true 
        while continueLooping do
            abstraction.CubeSizeSpread <- maxCubeSizeSpread
            abstraction.CurrentStepBound <- step
            let res : Path option = findSinglePath abstraction None false true
            match res with 
            | Some _    -> 
                for bitRelevancy : int in [1..problem.fractionsEncoding] do
                    if satisfiesBound abstraction then () else
                    abstraction.BitRelevancy <- bitRelevancy
                    abstraction <- relevancyReduction abstraction problem.GlobalStepBound
                    let curMax = initialMaxCubeSize + maxCubeSizeSpread
                            //((abstraction.CurrentStepBound * abstraction.BitRelevancy * numberOfProbabilisticModules prismModel))
                    let minimalCubeSize = max initialMaxCubeSize bitRelevancy   + (maxCubeSizeSpread-3) // magic constant
                    report_1 4 "Checking abstraction: %s" (printAbstraction_short abstraction)
                    // is there any path reaching the goal in precisely n steps?
                    abstraction <- findCubes abstraction curMax minimalCubeSize
            | None -> report_0 4 "No path found for current step depth."

            if satisfiesBound abstraction then continueLooping <- false
            elif step > 4*(maxCubeSizeSpread-2) || step>=problem.GlobalStepBound   // magic constant
            then 
                if maxCubeSizeSpread>=maxGlobalCubeSize-initialMaxCubeSize 
                then continueLooping <- false
                else maxCubeSizeSpread <- maxCubeSizeSpread+1
            else step <- step+1
            
        report_1 5 "Probability mass found: %s " (abstraction.AccumulatedProbability.ToString())
        if problem.ProbabilityBound.IsNone then UNKNOWN
        elif satisfiesBound abstraction then HOLDS 
        else VIOLATED




/////////////////////////////////////////////////////////
////////// Here comes just old stuff: ///////////////////
/////////////////////////////////////////////////////////
//        // Encode model
//        report_0 2 "Encoding model to Z3."
//        let stopWatch = Stopwatch.StartNew()
//        let co = encode z3 sol problem prismModel
//        stopWatch.Stop()
//        report_1 5 "Created the constraint system in %f s." stopWatch.Elapsed.TotalSeconds
//
//        // Check 
//        report_0 4 "Calling Z3 ..."
//        let stopWatch = Stopwatch.StartNew()
//        let status = co.solver.Check()
//        stopWatch.Stop()
//        report_1 5 "Z3 checked this instance in %f s." stopWatch.Elapsed.TotalSeconds
//        report_1 5  "%s" (status.ToString())
//        report_1 4 "%s" (co.solver.Statistics.ToString())
//        
//        if status=Status.SATISFIABLE then 
//            searchAndPrintDistributionFunction co
//        let q = match status with
//                | Status.SATISFIABLE -> HOLDS 
//                | Status.UNSATISFIABLE -> VIOLATED 
//                | _ -> UNKNOWN 
//        if co.problem.ExpectedResult.IsSome && q <> co.problem.ExpectedResult.Value && q<>UNKNOWN
//        then Some ERROR 
//        else q

//    if problem.ExistenceOfPathsTestingMode
//        then 
//            for constDecl in co.solver.Model.ConstDecls do
//                if constDecl.Name.ToString().Contains "localRandom"
//                then report_2 4 "%s has value %s" (constDecl.Name.ToString()) (co.solver.Model.ConstInterp(constDecl).ToString())
//        //report_0 4 "Press any key to continue.";
//        //let _ =  Console.ReadKey(true)
//        () 



//    match problem.Z3Interface with
//            | SMTLIB_File outputFileName ->
//                report_0 4 "Creating SMTLibStringassertion string ..."
//                let assertions = String.Concat( List.map (fun (x:BoolExpr) -> "(assert " + x.ToString() + ")\n\n") (List.ofArray co.solver.Assertions))
//                let declarations = String.Concat (List.map (fun x -> x.ToString()+"\n") co.declarations)
//            
//                let makeFileName (problem:Problem) : String = 
//                    let lastPathSeparator : int = problem.FilePath.LastIndexOfAny(Array.ofList ['/';'\\'])
//                    let fileName = problem.FilePath.Substring (lastPathSeparator + 1)
//                    let leadingZeros (x:int) : String = String.replicate (2 - Convert.ToInt32 (floor(log10(Convert.ToDouble(x))))) "0"
//                    let randomChoiceEncodingToString rce : String =
//                        let argumentString =
//                            match rce with
//                            | RCE_Fixed a -> leadingZeros a + a.ToString()
//                            | RCE_Auto -> "Auto"
//                        argumentString // no UnionCastName to avoid clutter
//                    fileName 
//                        + (if problem.RunName.IsSome then "_" + problem.RunName.Value.ToString() else "")
//                        + "_steps" + leadingZeros problem.StepBound + problem.StepBound.ToString() 
//                        + "_prec" + randomChoiceEncodingToString problem.randomChoiceEncoding
//                        + "_" + solutionShapeToString problem.SolutionShape
//                        + ".smt2"
//
//                let outputFileName = if outputFileName.IsSome then outputFileName.Value else makeFileName problem
//                let writer = new StreamWriter("../../../experiments/" + outputFileName)
//                writer.WriteLine("(set-logic UFBV)")
//                writer.Write(declarations)
//                writer.Write(assertions)
//                writer.WriteLine("(check-sat)")
//                writer.Flush()
//                writer.Close()
//
//                report_1 4 "Written file to \"%s\"" outputFileName
//            
//                UNKNOWN
//
//            | DOTNET -> 