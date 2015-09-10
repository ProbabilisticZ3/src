// MN Rabe

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
open CustomQEAnalyzer
open CounterExamples
open Statistics 

module TacticEvaluationAnalyzer =

    // Searches for a single cube (or maybe a small number of partially overlapping cubes) along a single path. 
    let pathBasedCubeSearch_TacticEval (problem:Problem) (prismModel:PrismModel) (ac:AnalyzerContext) (path:Path) : AnalyzerContext =
        report_0 4 "Searching for a path to start cube search."
        report_1 4 "Current path: %s" (printPath path)
            
        // First test whether the path hit a boundary region. In this case we would waste a lot of time. 
        match listCCEs ac path 0 0 1 None [] with // magic constant
        | cce :: empty -> 
            let ce = CCE2RPath ac path cce
//            let ce = path2RPath path
            ac.CECache <- ce :: ac.CECache
            ac
        | [] -> // continue 
        
        // Find all close counterexamples with distance 1. These are critical to 
        // know and there are not too many. 
        let mutable cces : ConcreteCCE list = listCCEs ac path 1 1 Int32.MaxValue None []

        // The current size of cubes we are searching for. 
        let mutable cubeSize = max 1 cces.Length 
        
        // Minimal distance of counter-examples
        let mutable nearestCEs = 2
        // Maximal distance to check for counter-examples
        let maxCheckDistance = 3  // magic constant  
        let mutable cubeIndependentCCEsToFind = 1 // magic constant

        let numberOfProbabilisticBits = ac.CurrentStepBound * numberOfProbabilisticModules prismModel * ac.co.problem.fractionsEncoding

        let mutable result : ConcreteCube list = []
        let mutable terminate : bool = false 
        while not terminate do
            // get a candidate cube
            match findCandidateCube ac cces path cubeSize with 
            | Some (candidate:ConcreteCube) -> 
                report_1 4 "Testing candidate cube: %s" (printConcreteCube_bitSelectorOnly candidate)
                // Check whether cube is correct ac
                match findSinglePath ac (Some candidate) true false with 
                | Some path -> // Extract a better CE:  
                    let cces = listCCEs ac path nearestCEs (nearestCEs+maxCheckDistance) 1 (Some candidate) [] // magic constant
                    terminate <- true
                | None -> 
                    result <- candidate::result // Success! 
                    terminate <- true

            | None -> 
                if cubeSize<numberOfProbabilisticBits // can probably be made stronger, like cubeSize< (-1/log expectedProbability)+20
                then cubeSize <- cubeSize+1 
                else raise NotYetImplemented // TODO: here we reached some tiny cube and we need to exclude some larger part of the probability space. 

            report_1 4 "Current cube size: %s" (cubeSize.ToString())
            // end while loop

        match result with 
        | [cube] ->
            report_1 4 "Found a cube of size %d" cubeSize
            if cubeSize<ac.LargestCubeSizeFound 
            then {ac with LargestCubeSizeFound = cubeSize}
            else ac

        | [] ->
            report_0 4 "No (positive) cube found."
            ac
        | multiplecubes ->
            raise NotYetImplemented


    let analyze_TacticEvaluation (problem:Problem) (prismModel:PrismModel) : Result = 
        assert (problem.AssumeGoalRegionIsAbsorbing)
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable ac = initialAC co
        let mutable step = 1 

        let mutable res : Result option = None
        let mutable timeout = false
        try 
            while res.IsNone do
                ac.CurrentStepBound <- step
                let path = findSinglePath ac None false true
                if path.IsSome then 
                    ac <- pathBasedCubeSearch_TacticEval problem prismModel ac path.Value
                    res <- Some HOLDS 
                else 
                    ac.NoPathToGoalRegionUntilStep <- Some step
                    if step < problem.GlobalStepBound  
                    then step <- step+1
                    else res <- Some VIOLATED
        with 
            | :? System.TimeoutException as e -> timeout <- true

        report_1 4 "%s" <| printStatistics ac.Statistics
        
        UNKNOWN

