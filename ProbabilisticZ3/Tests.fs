// CM Wintersteiger, MN Rabe

namespace ProbabilisticZ3

open System
open System.Diagnostics

open Problems
open Microsoft.Z3
open Analyzer
open Utils 
open Results
open SolverConfigs
open ExampleProblems

module Tests =

    let run () : int =
        let test (problem:Problem) : unit = 
            let result = analyze problem
            report_2 5 " %s  %s " (problem.RunName.Value.ToString()) (if result.Equals ERROR then (printResult result) else "")

        let testProblemSequence (problems:Problem list) : unit =
            let results : (Result*float) list = 
                List.map 
                    (fun p -> 
                        let stopWatch = Stopwatch.StartNew()
                        let result = analyze p
                        stopWatch.Stop()
                        (result,stopWatch.Elapsed.TotalSeconds)) 
                    problems 
            for (p, (result,time)) in List.zip problems results do
                report_3 5 " %s, %fs %s"  (p.RunName.Value.ToString()) time (if result.Equals ERROR then (printResult result) else "") 
            report_0 5 "Test sequence finished."

        try
            let stopWatch = Stopwatch.StartNew()
            match 8 with 
            | 0 -> // A bunch of small test models checking for expected results
                testProblemSequence (testSequenceForCorrectness @ syncTests)
            | 1 -> test <| crowds 15 3 5 0.005
            | 11 -> test <| herman 20 31 0.00000001
            | 2 -> 
                testProblemSequence 
                    [
                    brp16_2
//                    brp64_5
                    crowds 15 3 5 0.005
//                    crowds 15 3 5 0.007
                    crowds 15 6 20 0.005
//                    crowds_big 15 6 40 0.005
                    crowds_big 15 20 40 0.005
                    leader 4 3 2 0.75
                    leader 20 3 2 0.99
                    leader 5 4 8 0.1
                    leader 5 4 8 0.25
                    leader 5 4 64 0.1
                    egl 5 2 31 0.4
                    herman 20 3 0.99
                    herman 20 11 0.01
                    herman 20 21 0.00001
                    ]
            | 3 -> testProblemSequence // high volume benchmarks
                    [
                    leader 20 3 2 0.99 // 190s
                    crowds 15 3 5 0.009
                    ]
            | 4 -> // take quite long, but should be reached
                testProblemSequence 
                    [
                    herman 20 11 0.1 // this probability might be much smaller! like 0.0295, but try with say 0.02
                    egl 5 2 31 0.4
                    leader 7 6 8 0.50
                    leader 5 4 64 0.90
                    nand 100 20 2 0.000005 // takes like 1000s to find the first path
                    ]

            | 5 -> // tactic evaluations
                let perfSeq = 
                    List.map 
                        (fun p -> {p with configs = {defaultConfiguration with AnalyzerStrategy = TacticEvaluation}})
                        [
                        brp16_2
                        brp64_5
                        crowds 15 3 5 0.005
                        crowds 15 6 20 0.005
                        crowds_big 15 6 40 0.005
                        crowds_big 15 20 40 0.005
                        leader 20 3 2 0.99
                        leader 5 4 8 0.1
                        leader 5 4 64 0.1
                        egl 5 2 31 0.4
                        herman 20 3 0.99
                        herman 20 11 0.01
                        ]
                testProblemSequence perfSeq
            | 6 -> // negative // TODO: make negative
                testProblemSequence 
                    [
                    leader 4 3 2 0.25
                    leader 5 4 8 0.01
                    crowds 15 3 5 0.2
                    { egl 5 2 21 0.1 with GoalRegion = Negative "unfairA" }
                    ]
            | 7 -> 
                testProblemSequence 
                    [
                    leader_precision 4 5 4 11 0.25
                    leader_precision 5 5 4 11 0.25
                    leader_precision 6 5 4 11 0.25
                    leader_precision 7 5 4 11 0.25
                    leader_precision 8 5 4 11 0.25
                    leader_precision 9 5 4 11 0.25
                    ]
            | 8 -> 
                testProblemSequence 
                    [
                    brp 20 6 16 2 0.000001
                    brp 20 6 16 2 0.000002
                    brp 20 6 16 2 0.000003
                    brp 20 6 16 2 0.000004
                    brp 20 6 16 2 0.000005
                    brp 20 6 16 2 0.000006
                    brp 20 6 16 2 0.000007
                    brp 20 6 16 2 0.000008
//                    brp 20 6 16 2 0.000009
//                    brp 20 6 16 2 0.000010
//                    brp 20 6 16 2 0.000011
//                    brp 20 6 16 2 0.000012
//                    brp 20 6 16 2 0.000013
//                    brp 20 6 16 2 0.000014
//                    brp 20 6 16 2 0.000015
                    ]
            | _ -> ()

            stopWatch.Stop()
            report_1 4 "Test case checked in %f s." stopWatch.Elapsed.TotalSeconds

            // Wait for user
            printfn "Press any key to exit.";
            let _ =  Console.ReadKey(true)
            0 // return an integer exit code
        with 
            | :? System.ArgumentException as e -> 
                printfn "%A" e.Message
                raise e
    //                printfn "\nPress any key to exit.";
    //                let _ = Console.ReadKey(true)
    //                1
            | :? System.OutOfMemoryException as e -> 
                printfn "Exception: Out of memory"
                printfn "\nPress any key to exit.";
                let _ = Console.ReadKey(true)
                1
//            | e -> 
//                printfn "%s" e.Message
//                let _ = Console.ReadKey(true)
//                1

