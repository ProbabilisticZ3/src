// MN Rabe

namespace ProbabilisticZ3

open System
open Microsoft.Z3
open Utils
open Results
open Problems
open Cubes
open Paths
open CounterExamples
open EncodingContext
open PrismModelEncoding
open GuardEncoding
open Statistics

module AnalyzerContexts =
    
    type PrecomputedZ3Objects = {
            InitialCondition : BoolExpr
            TRDef_underApprox : BoolExpr
            TRDef_overApprox : BoolExpr
            VariableRangeDefs : BoolExpr
            FormulaDefs : BoolExpr
            GuardDefs : BoolExpr 
        }
    


//    // Keepps track of solver objects that are still satisfiable.
//    type SolverCache = {
//        mutable PathSolver : Solver option
//        mutable CCESolver : Solver option
//        mutable CubeCandidateSolver : Solver option
//        }

    type AnalyzerContext = {
        /// <summary>Name of the analyzer run to be performed (usefule for batch-jobs).</summary>
        mutable AbstractionName : String option

        /// <summary>Expected result of the analysis (for debugging).</summary>
        mutable ExpectedResult : Result option

        /// <summary>Enables the use of a consistent instance of Z3.</summary>
        mutable co : EncodingContext

        /// <summary>Selected large Z3 expressions that we use over and over again.</summary>
        mutable PrecomputedZ3Objects : PrecomputedZ3Objects
        mutable bmcFormula_underApprox : BoolExpr ; 
        mutable bmcFormula_overApprox_negatedGoal : BoolExpr ; 

        /// <summary>Current unwinding bound for the analyzer.</summary>
        mutable CurrentStepBound : int

        /// <summary>Label of the goal region</summary>
        mutable GoalRegion : String ample
        
        /// <summary>The cubes found already.</summary>
        mutable PositiveCubes : ConcreteCube list 

        /// <summary>The accumulated mass of the cubes found already.</summary>
        mutable AccumulatedProbability : double

        /// <summary>Encoding of variables for random choices of transitions.</summary>
        mutable BitRelevancy: int // RandomChoiceEncoding

        /// <summary>The step number until which we exhausted the search for paths to the goal region.</summary>
        mutable NoPathToGoalRegionUntilStep : int option

        /// <summary>The accumulated mass of the cubes found already.</summary>
        mutable LargestCubeSizeFound : int

        /// <summary>The maximal difference of the smallest cube size to the largest cube size. Only used in classical cube search. </summary>
        mutable CubeSizeSpread : int
        
        /// <summary>Maximal cube size to which the path based cube search will go.</summary>
        mutable MaximalCubeSize : int

        /// <summary>Value by which the maximal cube size is incremented when the probability space is depleted. </summary>
        mutable CubeSizeIncrement : int

        /// <summary> Bits which have been declared irrelevant. </summary>
        mutable IrrelevantBits : Set<int*int*int>

        /// <summary> Bits which have been positively checked for relevancy or for which the test timed out.</summary>
        mutable RelevantBits : Set<int*int*int>

//        mutable SolverCache : SolverCache

        mutable CECache : RPath list

        mutable Statistics : Statistics 
    }
//
//    // Updates time and returns true iff time up. 
//    let updateTime (ac:AnalyzerContext) (millisPassed) : bool = 
//        ac.TimeLeft <- ac.TimeLeft - millisPassed  
//        ac.TimeLeft <= 0

    let printAbstraction (a:AnalyzerContext) = 
        (if a.AbstractionName.IsSome then a.AbstractionName.Value else "abstr")
        + "(step " + a.CurrentStepBound.ToString() 
        + ", bit relevancy " + a.BitRelevancy.ToString() 
        + ", prob " + a.AccumulatedProbability.ToString() 
        + ", largest " + a.LargestCubeSizeFound.ToString() 
        + ", maxSpread " + a.CubeSizeSpread.ToString() + ")"

    let printAbstraction_short (a:AnalyzerContext) = 
        (if a.AbstractionName.IsSome then a.AbstractionName.Value else "abs")
        + "(" + a.CurrentStepBound.ToString() + "," + 
        a.BitRelevancy.ToString() + ",(" + 
        a.AccumulatedProbability.ToString() + ")," + 
        (if a.LargestCubeSizeFound=Int32.MaxValue then "_" else a.LargestCubeSizeFound.ToString()) + "," + 
        a.CubeSizeSpread.ToString() + ")"

        
    let satisfiesBound (ac:AnalyzerContext) : bool = 
        match ac.co.problem.ProbabilityBound with 
        | Some (bound, COMP_GE) -> ac.AccumulatedProbability >= bound
        | Some (bound, COMP_LE) -> ac.AccumulatedProbability <= bound
        | Some (bound, COMP_GT) -> ac.AccumulatedProbability > bound
        | Some (bound, COMP_LT) -> ac.AccumulatedProbability < bound
        | None -> false

