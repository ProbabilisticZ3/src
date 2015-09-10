// Created by Markus Rabe
// Modified by Boyan Yordanov

namespace ProbabilisticZ3

open System

open Expressions
open Problems
open SolverConfigs
open Analyzer
open Results
open System.Text.RegularExpressions
open Utils

module mainmodule =

    let parseConstant (s:string) : Variable option = 
        let it = s.Split([|'='|])
        if it.Length <> 2 then 
            printfn "Ignoring illegal constant specification: %s" (it.ToString()) ; None
        else 
            Some (new Variable(None,None,it.[0],Some << Expr.IntExpr << I <| Convert.ToInt32 it.[1], DataType.TInteger,VariableType.GlobalConstant,None))

    let showHelp() =
            printfn "Probabilistic Z3; preliminary command line interface. \r\n
The following options are required: 
    -file <string>    the path to the file\r\n
    -label <string>   the Prism label defining the goal region  \r\n
    -steps <int>       maximal number of steps to be considered \r\n
If the model has open constants, it also requires to set the constants: \r\n
    e.g. -const N=5 \r\n
Other options are: \r\n
    -prob <double>     target probability [0.0, 1.0])\r\n
    -timeout <int>     timeout in milliseconds. Is usually a few percent off. \r\n
    -intBits <int>     number of bits to represent (signed) integers \r\n
    -fractBits <int>   number of bits to represent fractions, including probs. \r\n
Default values can be looked up in Problems.fs.\r\n"

    let parseCmdLine (args : string []) =
        let mutable opts = Some defaultProblem 
        let mutable i = 0 
        let mutable have_steps = false

        while i < args.Length && opts.IsSome do            
            match args.[i] with
            | "-help" -> 
                showHelp() ;    
                opts <- None
            | "-file" -> i <- i + 1 ; opts.Value.FilePath <- args.[i]
            | "-const" -> i <- i + 1 ; opts.Value.Constants <- (Option.toList <| parseConstant args.[i]) @ opts.Value.Constants
            | "-steps" -> 
                i <- i + 1 ;
                let v = Convert.ToInt32(args.[i]) in
                (if v <= 0 then
                    raise(Exception("-steps requires a value > 0"))
                else
                    opts.Value.GlobalStepBound <- v) ;
                have_steps <- true
            | "-timout" -> i <- i + 1 ; opts.Value.Timeout <- Convert.ToInt32(args.[i])
            | "-intBits" -> i <- i + 1 ; opts.Value.intEncoding <- Convert.ToInt32(args.[i])
            | "-fractBits" -> i <- i + 1 ; opts.Value.fractionsEncoding <- Convert.ToInt32(args.[i])
            | "-prob" -> 
                i <- i + 1 ; 
                let v = Convert.ToDouble(args.[i]) in
                if v < 0.0 || v > 1.0 then
                    raise(Exception("target probability must be in [0.0, 1.0]"))
                else
                    opts.Value.ProbabilityBound <- Some (v,COMP_GE)
            | "-label" -> i <- i + 1 ; opts.Value.GoalRegion <- Positive args.[i]
            | arg -> i <- i + 1 ; printfn "Ignoring illegal argument: %s"  arg 
//            | "-smtlib" -> i <- i + 1 ; opts.Z3Interface <- SMTLIB_File None
            i <- i + 1
        if opts.Value.FilePath = null then
            raise(Exception("required argument `-file' missing"));
        if opts.Value.GoalRegion = Empty then
            raise(Exception("required argument `-label' missing"));
        if not have_steps then
            raise(Exception("required argument `-steps' missing"));
        if opts.Value.ProbabilityBound = None then 
            printf("Warning: no probability bound provided.\r\n")
        opts


    [<EntryPoint>]
    let main args = 
         if args.Length = 0 then
             // Tests.run()
             showHelp(); 1
         else        
            let cfg = parseCmdLine args in 
            match cfg with
            | None -> 0
            | Some problem -> 
                match analyze problem with
                | HOLDS -> printfn "Property holds."; 0
                | VIOLATED -> printfn "Property is violated."; 0
                | UNKNOWN -> printfn "Unknown."; 0
                | ERROR -> printfn "Error."; 1
        
