

namespace ProbabilisticZ3

open System
open PrismParser
open Irony.Parsing
open Microsoft.FSharp.Reflection // for printing union types
open Microsoft.Z3

module Utils =

    exception InnerError of string
    exception NotYetImplemented

    let flip f x y = f y x
    let curry f a b = f (a,b)
    let uncurry f (a,b) = f a b

    let toList (xs : Collections.Generic.List<ParseTreeNode>) : ParseTreeNode list = List.ofArray(xs.ToArray())
    let nameIs (name:String) (node : ParseTreeNode) : bool = node.Term.Name.Equals(name)
    let depthOneObjects name (node : ParseTreeNode) = if nameIs name (node.ChildNodes.Item(0)) then [node.ChildNodes.Item(0)] else []

    ///Returns the case name of the object with union type 'ty.
    let GetUnionCaseName (x:'a) = 
        match FSharpValue.GetUnionFields(x, typeof<'a>) with
        | case, _ -> case.Name  


    let rec multiplySets (xs : 'a list list) : 'a list list = 
        match xs with 
        | []    -> []
        | x::[] -> List.map (fun y -> [y]) x
        | _     -> 
            let rest : 'a list list = multiplySets xs.Tail
            List.collect (fun (y:'a) -> List.map (fun (r:'a list) -> y::r) rest) xs.Head

    //let asdf (z3:Context) a : BoolExpr = z3.MkAnd a // BoolExpr[]
    //let asdf2 (z3:Context) : BoolExpr list -> BoolExpr = asdf z3 << Array.ofList // TODO: replace the function below by this stuff, then test whether it works. 
    let z3mkAnd (z3:Context) (es:BoolExpr list) : BoolExpr = z3.MkAnd (Array.ofList es)
    let z3mkOr  (z3:Context) (es:BoolExpr list) : BoolExpr = z3.MkOr  (Array.ofList es)

    let transpose (xs : 'a list list) : 'a list list = 
        List.rev 
        << fst 
        << List.fold (fun (ys, zs) _ -> (List.map List.head zs :: ys, List.map List.tail zs)) ([],xs)
        <| [0..(List.head xs).Length-1]

    let reportLevel = 4
    let report_0 lvl s = if lvl>=reportLevel then printf ">>"; printfn s else ()
    let report_1 lvl s arg1 = if lvl>=reportLevel then printf ">>"; printfn s arg1 else ()
    let report_2 lvl s arg1 arg2 = if lvl>=reportLevel then printf ">>"; printfn s arg1 arg2 else ()
    let report_3 lvl s arg1 arg2 arg3 = if lvl>=reportLevel then printf ">>"; printfn s arg1 arg2 arg3 else ()
    let report_4 lvl s arg1 arg2 arg3 arg4 = if lvl>=reportLevel then printf ">>"; printfn s arg1 arg2 arg3 arg4 else ()

    
    let take (n : int) (xs : 'a list) : 'a list = 
        List.ofSeq << Seq.take n <| xs

    let rec takeAsMany (ys : 'b list) (xs : 'a list) : 'a list = 
        match ys with 
        | [] -> []
        | _ -> xs.Head :: takeAsMany ys.Tail xs.Tail
//    let rec truncateList (n : int) (xs : 'a list) : 'a list =
//        if n=0 
//        then []
//        else xs.Head :: truncateList (n-1) xs.Tail
            