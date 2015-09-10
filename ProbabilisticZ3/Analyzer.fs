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
open MonolythicAnalyzer
open CustomQEAnalyzer
open TacticEvaluationAnalyzer
open CounterExamples
open Statistics 


module Analyzer =  

    let analyze_exact (problem:Problem) (prismModel:PrismModel) : Result = 
        let z3 = configureZ3 problem 
        let co = initializeContext problem prismModel z3
        let mutable ac = initialAC co
        ac.CurrentStepBound <- problem.GlobalStepBound
        findExactDistribution ac

        UNKNOWN // TODO


    let analyze (problem:Problem) : Result = 
        match problem.RunName with 
        | Some s -> report_2 5 "\n\Analyzing problem: %s (%s steps)" s (problem.GlobalStepBound.ToString())
        | None   -> report_0 5 "\n\Analyzing problem"

        let prismModel : PrismModel = readPrismFile problem.FilePath problem.Constants problem.configs.SimplifiedGuardEncoding

        let result =
            match problem.configs.AnalyzerStrategy with
            | Monolythic -> analyze_stepAverse2 problem prismModel
//        analyze_precisionAverse problem prismModel
//        let result = analyze_stepAverse problem prismModel 
//        let result = analyze_stepAverse2 problem prismModel
//            | GeneralizePaths -> analyze_pathAffine problem prismModel
            | GeneralizePaths -> 
                match problem.configs.IncreasingPathLength with
                | true  -> analyze_pathAffine problem prismModel
                | false -> analyze_pathAffine_fullPaths problem prismModel
            | Exact -> analyze_exact problem prismModel
            | TacticEvaluation _ -> analyze_TacticEvaluation problem prismModel

        report_0 4 "Leaving analysis."

        match problem.ExpectedResult with
        | None -> result
        | Some expected ->
            if not (result = expected) && not (result.Equals UNKNOWN)
            then ERROR 
            else result



