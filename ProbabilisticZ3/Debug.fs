
namespace ProbabilisticZ3

open System
open System.Diagnostics
open EncodingContext
open Microsoft.Z3
open System.Text.RegularExpressions

module Debug =

    let ExportSmtLib (sol:Solver) = 
        //sol.Check() |> ignore
        let Const = Seq.fold(fun acc x-> acc + x.ToString() + "\n") "" sol.Model.ConstDecls
        let Funcs = Seq.fold(fun acc x-> acc + x.ToString() + "\n") "" sol.Model.FuncDecls
        let Assert = Seq.fold(fun acc x-> acc + "(assert " + x.ToString() + ")\n") "" sol.Assertions
        Const + Funcs + Assert

    let EnumerateStates (context:EncodingContext) (sol:Solver) vars = 
        sol.Check()|>ignore;
        let sbv = context.stepBVSize
        let z3 = context.z3
        let Evaluate (k:int) = Seq.map(fun (name,f)-> sol.Model.Eval(z3.MkApp(f,z3.MkBV(k,sbv)),true).ToString()) vars
        let Format vals = Seq.map2(fun(name,f) y-> name + "=" + y) vars vals |> Seq.fold(fun acc x-> acc + x + ", ") ""
        let Unique (k:int) = 
            let step = z3.MkBV(k,sbv)
            let cst = Evaluate k
                      |> Seq.map2(fun (name,f:FuncDecl) v -> 
                        if f.Range = (z3.BoolSort:>Sort) then  //boolean functions
                            if v="true" then 
                                z3.MkEq(z3.MkApp(f,step), z3.MkTrue())
                            else
                                z3.MkEq(z3.MkApp(f,step), z3.MkFalse())
                        else             
                            let bv = (f.Range:?>BitVecSort).Size
                            let bVal = z3.MkBV(v,bv)
                            z3.MkEq(z3.MkApp(f,step),bVal)) vars
                      |> Array.ofSeq    
            z3.MkNot(z3.MkAnd(cst)) 

        let mutable log = ""
        let mutable sat = true
        while sat do
            sat <- sol.Check()=Status.SATISFIABLE
            log <- log + "\n" + Format(Evaluate(0))
            sol.Assert(Unique(0))        
        log


    // Find all probabilistic reactions and replace them with nondeterministic ones
    let AbstractKinetics (model:string) =         
        let mutable result = model
        for m in Regex.Matches(model,@"\[.+->[^:;]+:[^;]*;") do
            let P = m.Value.Replace(";","").Split(Array.ofList(["->"]),StringSplitOptions.RemoveEmptyEntries)
            let Pn = (P.[1]).Split('+') 
                      |> Seq.map(fun (x:string)-> (P.[0] + "->" + (x.Split(':')).[1] + ";"))
                      |> Seq.fold(fun acc x-> acc + x + "\n") ""
            result<- model.Replace(m.Value,Pn)        
        result


