
namespace ProbabilisticZ3

open System
open Microsoft.Z3
open Utils
open Results
open Problems
open Cubes
open EncodingContext

module CounterExamples =

    // Close counter-examples are always relative to a path, they only 
    // comprise a list of positions where the CE deviates from the path. 
    type CloseCounterExample = BitSelector list
    type ConcreteCCE = ConcreteBitSelector list

    // Concretizes a close counter-example
    let extractCounterExample (solver:Solver) (cce:CloseCounterExample) : ConcreteCCE = 
        List.map
            (fun (bitSel:BitSelector) -> 
                let stepExpr : BitVecNum = downcast solver.Model.Eval(bitSel.StepSelector,true) 
                let moduleExpr : BitVecNum = downcast solver.Model.Eval(bitSel.ModuleSelector,true)
                let posExpr : BitVecNum = downcast solver.Model.Eval(bitSel.PosSelector,true)
                let cbs : ConcreteBitSelector = {
                    StepSelector = stepExpr
                    ModuleSelector = moduleExpr
                    PosSelector = posExpr
                }
                cbs)
            cce

    let excludeOtherCCEs (co:EncodingContext) (cce:CloseCounterExample) (otherCCCEs:ConcreteCCE list) : BoolExpr =
        let z3 = co.z3
        let c = z3mkAnd z3
                << List.map
                    (fun (ccce:ConcreteCCE) -> 
                        z3mkOr z3 
                        << List.map
                            (fun (cbit:ConcreteBitSelector) -> 
                                z3mkAnd z3
                                << List.map 
                                    (fun (bitSel:BitSelector) -> 
                                        z3.MkNot
                                        <| z3mkAnd z3 
                                            [
                                            z3.MkEq(bitSel.StepSelector,  cbit.StepSelector) ; 
                                            z3.MkEq(bitSel.ModuleSelector, cbit.ModuleSelector) ; 
                                            z3.MkEq(bitSel.PosSelector, cbit.PosSelector) ; 
                                            ]
                                    )
                                <| cce
                            )
                        <| ccce)
                <| otherCCCEs
//        let simp = c.Simplify()
        c

