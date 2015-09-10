// CM Wintersteiger, MN Rabe

namespace ProbabilisticZ3

open System
open System.IO
open System.Diagnostics

open PrismModel
open Utils
open Tactics
open Tactics_Monolythic
open Microsoft.Z3
open EncodingContext
open Results
open Problems
open SolverConfigs
open AnalyzerContexts
open AnalyzerContextEncodings
open Cubes
open Paths
open PathEncodings
open MonolythicAnalyzer
open CounterExamples
open Statistics 

module CustomQEAnalyzer = 

    let globalMaxCubeSize problem prismModel : int =
        max 1 (problem.fractionsEncoding * problem.GlobalStepBound * numberOfProbabilisticModules prismModel)        

    let referenceCubeSize problem globalMaxCubeSize : int = 
        if problem.ProbabilityBound.IsSome 
        then 
            match problem.ProbabilityBound with
            | Some (0.0,_) -> 1 
            | _ -> max 1 ((Convert.ToInt32( ceil ( - (log (fst problem.ProbabilityBound.Value)) / log 2.0))))
        else min 10 globalMaxCubeSize



    // Searches for a single cube (or maybe a small number of partially overlapping cubes) along a single path. 
    let pathBasedCubeSearch (problem:Problem) (prismModel:PrismModel) (ac:AnalyzerContext) (path:Path) : AnalyzerContext =
        report_0 3 "Searching for a path to start cube search."
        report_1 3 "Current path: %s" (printPath path)
            
        let listCCEs = if problem.configs.CCESumEncoding then listCCEs_sumEncoding else listCCEs

        // First test whether the path hit a boundary region. In this case we would waste a lot of time. 
        // Became obsolete since we search for example paths in the underapproximation
//        match listCCEs ac path 0 0 1 None [] with // magic constant
//        | cce :: empty -> 
//            let ce = CCE2RPath ac path cce
//            ac.CECache <- ce :: ac.CECache
//            ac
//        | [] -> // continue 

        // Find all close counterexamples with distance 1. These are critical to 
        // know and there are not too many. 
        let mutable cces : ConcreteCCE list = listCCEs ac path 1 1 Int32.MaxValue None []

        // The current size of cubes we are searching for. 
        let mutable cubeSize = max 1 cces.Length 
        
        // Minimal distance of counter-examples
        let mutable nearestCEs = 2
        // Maximal distance to check for counter-examples
        let maxCheckDistance = 0  // magic constant  
        let mutable cubeIndependentCCEsToFind = 1 // magic constant

        let numberOfProbabilisticBits = ac.CurrentStepBound * numberOfProbabilisticModules prismModel * ac.co.problem.fractionsEncoding

        let mutable result : ConcreteCube list = []
        let mutable terminate : bool = false 
        while not terminate do
            // get a candidate cube
            match findCandidateCube ac cces path cubeSize with 
            | Some (candidate:ConcreteCube) -> 
                report_1 3 "Testing candidate cube: %s" (printConcreteCube_bitSelectorOnly candidate)
                // Check whether cube is correct ac
                match findSinglePath ac (Some candidate) true false with 
                | Some ce_path -> 
                    // Extract a better CE:  
//                    match listCCEs nearestCEs numberOfProbabilisticBits 1 (Some candidate) cces with
                    match listCCEs ac path nearestCEs (nearestCEs+maxCheckDistance) 1 (Some candidate) cces with // magic constant
                    | cce :: empty -> 
                        assert(empty.IsEmpty) 
                        cces <- cce :: cces 
                    | [] -> // could not easily find a close CE
                        ac.CECache <- path2RPath ce_path :: ac.CECache 
                        report_0 2 "Did not find a close counter-example to exclude the current cube candidate. Continuing with searching close counter-examples" 
                        cubeIndependentCCEsToFind <- min 10 (cubeIndependentCCEsToFind + 1) // magic constant
                        // TODO: just use the path found earlier.
                    
                    // Optional: Find another close counter-example, 
                    // that is not related to the candidate cube. 
                    let mutable found : int = 0
                    while found<cubeIndependentCCEsToFind do
                        let xs = listCCEs ac path nearestCEs nearestCEs (cubeIndependentCCEsToFind-found) None cces
                        if xs.IsEmpty 
                        then 
                            found <- found+1 // safety mechanism against infinite loop
                            nearestCEs <- nearestCEs+1
                            if nearestCEs > globalMaxCubeSize problem prismModel 
                            then raise (InnerError "Could not find any counter-example, but there must be one." )
                            // else continue
                        else 
                            found <- found+xs.Length
                            cces <- xs @ cces
                    cubeIndependentCCEsToFind <- max (cubeIndependentCCEsToFind-1) 1
                    //cubeIndependentCCEsToFind <- min (cubeIndependentCCEsToFind+1) 3 // magic constant

                | None -> 
                    match problem.configs.MultipleCubesPerPath with 
                    | true -> 
                        // TODO: Add the newly found cube ("candidate") to the rest and determine unique volume. 
                        // When should we stop? After a random/maximal number of cubes? Whenever they get too small? 
                        raise NotYetImplemented
                    | false ->
                        result <- candidate::result // Success! 
                        terminate <- true

            | None -> 
                if cubeSize< min (ac.LargestCubeSizeFound+8) numberOfProbabilisticBits // magic constant
                then cubeSize <- cubeSize+1 
                else 
                    let ce = path2RPath path
                    ac.CECache <- ce :: ac.CECache
                    terminate <- true
                    // TODO: we could actually try to count that cube.

                // Optional todo: we should restrict the maximal cube size at probabilitySearchedFor+20 ... see referenceCubeSize

            report_1 3 "Current cube size: %s" (cubeSize.ToString())
            // end while loop

        // Remember CCEs:
        let newCEs = 
            List.map 
                (CCE2RPath ac path)
                cces
        ac.CECache <- newCEs @ ac.CECache

        match result with 
        | [cube] ->
            report_1 3 "This path lead to the following cube %s" (printConcreteCube_bitSelectorOnly cube)

            report_1 4 "Found a cube of size %d" cubeSize
            let ac = 
                if cubeSize<ac.LargestCubeSizeFound 
                then ac.LargestCubeSizeFound <- cubeSize
                ac

            if problem.configs.OverlappingCubes 
            then 
                let (volume,otherCubes) = additionalVolume ac.co.z3 cube ac.PositiveCubes
                ac.AccumulatedProbability <- ac.AccumulatedProbability+volume
                ac.PositiveCubes <- otherCubes
                ac.CECache <- []
            else
                ac.AccumulatedProbability <- ac.AccumulatedProbability+2.0**(-Convert.ToDouble(cubeSize))
                ac.PositiveCubes <- cube::ac.PositiveCubes
                ac.CECache <- []
            report_1 4 "Current accumulated probability %f" ac.AccumulatedProbability
            ac
        | [] ->
            report_0 4 "No (positive) cube found."
            ac
        | multiplecubes ->
            raise NotYetImplemented

    // TODO: shouldn't we restructure to avoid computing a list of cubes? This should be one iterative process. The only problem is to get rid of the assumption that the path is not in one of the existing cubes. 
        


    let analyze_pathAffine_fullPaths (problem:Problem) (prismModel:PrismModel) : Result = 
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable ac = initialAC co
        ac.CurrentStepBound <- problem.GlobalStepBound
        ac <- updateBMCFormulas ac
        ac <- bakeBMCFormulas ac
        let globalMaxCubeSize = globalMaxCubeSize problem prismModel
        let referenceCubeSize = referenceCubeSize problem globalMaxCubeSize


        let mutable terminateSearch = false  
        let mutable timeout = false
        try 
            while not terminateSearch do
                let pathOpt = findSinglePath ac None false problem.AssumeGoalRegionIsAbsorbing
                match pathOpt with
                | Some path -> 
                    ac <- pathBasedCubeSearch problem prismModel ac path
                    if satisfiesBound ac then 
                        terminateSearch <- true
                | None -> 
                    terminateSearch <- true
        with | :? System.TimeoutException as e -> timeout <- true
        
        report_1 5 "Probability mass found: %s " (ac.AccumulatedProbability.ToString())
        report_1 4 "%s" <| printStatistics ac.Statistics

        if problem.ProbabilityBound.IsNone || timeout then UNKNOWN
        elif satisfiesBound ac then HOLDS 
        else VIOLATED




    let analyze_pathAffine (problem:Problem) (prismModel:PrismModel) : Result = 
        assert (problem.AssumeGoalRegionIsAbsorbing)
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable ac = initialAC co
        let globalMaxCubeSize = globalMaxCubeSize problem prismModel
        let referenceCubeSize = referenceCubeSize problem globalMaxCubeSize

        let mutable res : Result option = None
        let mutable timeout = false
        let mutable is_baked = false 
        try 
            while res.IsNone do
                
                let path = findSinglePath ac None false true
                if path.IsSome then 
                    if not is_baked then 
                        ac <- bakeBMCFormulas ac
                        is_baked <- true
                    ac <- pathBasedCubeSearch problem prismModel ac path.Value
                    if satisfiesBound ac then res <- Some HOLDS 
                    ()
                else 
                    ac.NoPathToGoalRegionUntilStep <- Some ac.CurrentStepBound
                    if ac.CurrentStepBound < problem.GlobalStepBound  
                    then 
                        if problem.configs.IncreaseStepBoundCautious
                        then 
                            ac.CurrentStepBound <- ac.CurrentStepBound+1
                            ac <- updateBMCFormulas ac
                            is_baked <- false
                        else 
                            let newStepNumber : int = Convert.ToInt32 (ceil ((Convert.ToDouble ac.CurrentStepBound)*1.3)) // magic constant
                            ac.CurrentStepBound <- min newStepNumber problem.GlobalStepBound
                            ac <- updateBMCFormulas ac
                            is_baked <- false
                    else res <- Some VIOLATED
        with 
            | :? System.TimeoutException -> timeout <- true
        
        report_1 5 "Probability mass found: %s " (ac.AccumulatedProbability.ToString())
        report_1 4 "%s" <| printStatistics ac.Statistics

        let str = String.concat "\r\n  cube: " << Seq.map printConcreteCube << Seq.ofList <| ac.PositiveCubes
        report_1 3 "cube: %s" str
        
        if problem.ProbabilityBound.IsNone || timeout then UNKNOWN
        elif satisfiesBound ac then HOLDS 
        else VIOLATED