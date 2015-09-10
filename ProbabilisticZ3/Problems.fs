
namespace ProbabilisticZ3

open System
open System.Collections.Generic
open Microsoft.Z3
open Utils
open Results
open SolverConfigs
open Expressions

module Problems =

//    type Z3Interface = 
//    | DOTNET
//    | SMTLIB_File of String option

//    type IntEncoding = 
//    /// <summary>Automatically determines a sound fixed-witdth encoding of integers. Also determines the number of positions of the integer part of double variables.</summary>
//    | IE_Auto 
//    /// <summary>Fixed bit-width encoding of integers.</summary>
//    | IE_Fixed of int
//
//    type FractionsEncoding = 
//    /// <summary>Automatically determines a sound encoding of double variables.</summary>
//    | FE_Auto 
//    /// <summary>Fixedpoint encoding of fractional part of double variables parametrized by the position of the decimal.</summary>
//    | FE_FixedPoint of int
//    /// <summary>Floating-point encoding of double variables, parametrized by mantissa and exponent size.</summary>
//    | FE_FloatingPoint of int * int

    type Comparator =
    | COMP_GE
    | COMP_GT
    | COMP_LE
    | COMP_LT 

    type ample<'T> =
    | Empty 
    | Positive of 'T
    | Negative of 'T

    type Problem = {
        /// <summary>Name/Path of the problem file.</summary>
        mutable FilePath : String

        /// <summary>Constants used during model construction. Are only used when strings match exactly.</summary>
        mutable Constants : Variable list
                
        /// <summary>Name of the analyzer run to be performed (usefule for batch-jobs).</summary>
        mutable RunName : String option

        /// <summary>Expected result of the analysis (for debugging).</summary>
        mutable ExpectedResult : Result option

        /// <summary>Timeout for the analyzer (in milliseconds).</summary>
        mutable Timeout : int

        /// <summary>The maximal step bound the analyzer will ever consider. </summary>
        mutable GlobalStepBound : int

        /// <summary>Label of the goal region</summary>
        mutable GoalRegion : String ample

        /// <summary>The probability bound of interest. If no bound is specified, the solver searches until exhaustion of the search space.</summary>
        mutable ProbabilityBound : (Double * Comparator) option

        /// <summary>Encoding of integer variables.</summary>
        mutable intEncoding : int // IntEncoding

        /// <summary>Encoding of double variables.</summary>
        mutable fractionsEncoding : int // FractionsEncoding

        mutable AssumeGoalRegionIsAbsorbing : bool 

        /// <summary> Configuration of the solver </summary>
        mutable configs : SolverConfiguration
    }

    let defaultProblem = {
        FilePath = null ;
        Constants = [] ;
        RunName = None ;
        ExpectedResult = None ;
        Timeout = Int32.MaxValue ; 
        GlobalStepBound = Int32.MaxValue ;
        GoalRegion = Empty ;
        ProbabilityBound = None ; // Some (0.5,COMP_GT)
        intEncoding = 5 ;
        fractionsEncoding = 1 ;
        AssumeGoalRegionIsAbsorbing = true ;
        configs = defaultConfiguration ;
    }


    
    let configureZ3 (problem:Problem) : Context =
        report_0 1 "Configuring Z3."
        let settings = new Dictionary<string, string>()
        settings.["MODEL"] <- "true"
//        settings.["UNSAT_CORE"] <- "true" // seems it doesn't work
        settings.["TIMEOUT"] <- problem.Timeout.ToString() //"10000"

        Microsoft.Z3.Global.SetParameter("smt.mbqi.trace", "true")
//        Microsoft.Z3.Global.SetParameter("smt.ematching", "true")
        new Context(settings)

