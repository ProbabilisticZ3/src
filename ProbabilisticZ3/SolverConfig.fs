// MN Rabe

namespace ProbabilisticZ3

open System
open Microsoft.Z3
open Utils
open Results

module SolverConfigs =

    type StrategyEncoding = 
    | StateTimeDependent // // function f_k x_k y_k z_k -> Choice ... or function f x y z step_k -> Choice
    | Memoryless // function f x y z -> Choice
    // | LimitedMemory of n // n bits

    type AnalyzerStrategy = 
        | Monolythic
        | GeneralizePaths
        | Exact
        | TacticEvaluation

    type SolverConfiguration = {
        /// <summary>Class of strategies to search in. Memoryless or 
        /// state-time-dependent</summary>
        StrategyEncoding : StrategyEncoding
        
        /// <summary>Indicates whether a BMC check is included in the 
        /// constraint system.</summary>
        IntegratedPositiveChecks : bool

        /// <summary>Enable/Disable variable range checks.</summary>
        VariableRangeEncodingCheckMode : bool

        /// <summary>Indicates whether a BMC check is included in the constraint 
        /// system.</summary>
        TwoSidedSearch : bool

        /// <summary>Check for dimensions in the probability space that have 
        /// no effect. Disallow them for the selectors.</summary>
        DetectIrrelevantBits : bool

        /// <summary> How to search for more cubes </summary>
        AnalyzerStrategy : AnalyzerStrategy

        /// <summary> Cube spread determines the size of cubes to search for relative 
        /// to the largest cube found. </summary>
        initialCubeSizeSpread : int

        /// <summary> Require the cubes to have fixed higher significance 
        /// bits in a number when a lower-significance bit is selected. </summary>
        NoIsolatedLowSignificanceBits : bool
        
        /// <summary> Allow cubes to overlap. </summary>
        OverlappingCubes : bool

        /// <summary> First check for small path lengths. </summary>
        IncreasingPathLength : bool

        /// <summary> Try to find multiple cubes per path. </summary>
        MultipleCubesPerPath : bool 

        /// <summary> Sets to increase the step bound only by one. Only has an 
        /// effect if IncreasingPathLength is set to true. </summary>
        IncreaseStepBoundCautious : bool

        /// <summary> Uses a simplified guard encoding. </summary>
        SimplifiedGuardEncoding : bool
        
        /// <summary> Uses a simplified update encoding. </summary>
        SimplifiedUpdateEncoding : bool

        /// <summary> Uses heavy preprocessing on the k-step transition relation (whenever going to a new k). </summary>
        CTXSimplifierBaking : bool 

        /// <summary> Adds constraints for the CCE search that help to eliminate CCE candidates locally. </summary>
        LocalCCEElimination : bool

        CCESumEncoding : bool
    }

    let defaultConfiguration = {
        StrategyEncoding = StateTimeDependent ;
        VariableRangeEncodingCheckMode = false ; // Not yet implemented
        TwoSidedSearch = false ; // Not yet implemented
        DetectIrrelevantBits = false ; 
        AnalyzerStrategy = GeneralizePaths ;
        initialCubeSizeSpread = 3 ;
        NoIsolatedLowSignificanceBits = false ;
        OverlappingCubes = true ; 
        IncreasingPathLength = true ;
        IncreaseStepBoundCautious = true ; // Caution! Turning off this option might cause an error. 
        IntegratedPositiveChecks = false ; 
        MultipleCubesPerPath = false ;
        SimplifiedGuardEncoding = true ;
        SimplifiedUpdateEncoding = false ;
        CTXSimplifierBaking = true ;
        LocalCCEElimination = false ;
        CCESumEncoding = false ;
        }