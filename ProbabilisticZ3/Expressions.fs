

namespace ProbabilisticZ3

open System
open System.Numerics
open Irony.Parsing
open Microsoft.Z3
open Utils 

module Expressions =

    type Update = 
            | BoolVarUp of Variable * BoolExpr
            | IntVarUp of Variable * IntExpr
            | DoubleVarUp of Variable * DoubleExpr // This kind of updates is not part of the Prism language
            | NoUpdate // gets created whenever it is written "true" as an update in the prism file

    and PChoice = DoubleExpr * Update list

    and Transition =
            | TDet of string * BoolExpr * Update list 
            | TProb of string * BoolExpr * PChoice list

    and DataType = 
        | TInteger
        | TDouble
        | TBool
        | TBD

    and Range =
        | Eval of Int32 * Int32
        | Raw of ParseTreeNode * ParseTreeNode

    and VariableType =
        | GlobalConstant
        | GlobalVariable
        | LocalVariable
        | Formula 
        | Guard of string
        | Sync of string
        | Update of PChoice

    and Expr =
        | IntExpr of IntExpr
        | DoubleExpr of DoubleExpr
        | BoolExpr of BoolExpr

    and BoolExpr =
        | Or of BoolExpr * BoolExpr
        | And of BoolExpr * BoolExpr
        | IFF of BoolExpr * BoolExpr
        | Not of BoolExpr 
        | Eq of IntExpr * IntExpr
        | LEq of IntExpr * IntExpr
        | Lesser of IntExpr * IntExpr 
//        | GEq of IntExpr * IntExpr // "greater (than)" replaced by reversed lesser (than)
//        | Greater of IntExpr * IntExpr
        | DEq of DoubleExpr * DoubleExpr
        | DLEq of DoubleExpr * DoubleExpr
        | DLesser of DoubleExpr * DoubleExpr
//        | DGEq of DoubleExpr * DoubleExpr
//        | DGreater of DoubleExpr * DoubleExpr
        | ITE of BoolExpr * BoolExpr * BoolExpr
        | BoolVar of Variable
        | B of bool

    and IntExpr =
        | Plus of IntExpr * IntExpr
        | Minus of IntExpr * IntExpr
        | Mult of IntExpr * IntExpr
        | ITE of BoolExpr * IntExpr * IntExpr
        | UMinus of IntExpr 
        | Min of IntExpr list
        | Max of IntExpr list
        | Floor of DoubleExpr
        | Ceil of DoubleExpr
        | Pow of IntExpr * IntExpr
        | Mod of IntExpr * IntExpr
        | IntVar of Variable
        | I of int

    and DoubleExpr =
        | Plus of DoubleExpr * DoubleExpr
        | Minus of DoubleExpr * DoubleExpr
        | Mult of DoubleExpr * DoubleExpr
        | Div of DoubleExpr * DoubleExpr
        | ITE of BoolExpr * DoubleExpr * DoubleExpr
        | UMinus of DoubleExpr
        | Log of DoubleExpr * DoubleExpr
        | Min of DoubleExpr list
        | Max of DoubleExpr list
        | DoubleVar of Variable
        | D of double
        | Cast of IntExpr
    
    and Variable (node:ParseTreeNode option, exprNode:ParseTreeNode option, name:String, init:Expr option, myType:DataType, nodeType:VariableType, range:Range option) as self =
        member this.Node : ParseTreeNode option = node
        member this.ExprNode : ParseTreeNode option = exprNode
        member val Name = name with get, set
        member val Init : Expr option = init with get, set 
        member val DataType : DataType = myType with get, set
        member val VariableType = nodeType with get, set
        member val Range : Range option = range with get, set
        
        static member createWithName (node:ParseTreeNode,name:String) : Variable = 
            let nodeType =
                match node.Term.Name with 
                | "GlobalConstant" -> GlobalConstant
                | "GlobalVariable" -> GlobalVariable
                | "Declaration"    -> LocalVariable
                | "Formula"        -> Formula
                | _ -> invalidArg "node" ("Expected constant, global variable, local variable, or formula declaration. Read: " + node.Term.Name)
            let nameNode = 
                match nodeType with 
                | GlobalConstant -> node.ChildNodes.Item(2)
                | GlobalVariable -> node.ChildNodes.Item(1).ChildNodes.Item(0)
                | LocalVariable  -> node.ChildNodes.Item(0)
                | Formula        -> node.ChildNodes.Item(1)
                | _ -> raise (InnerError "Unexpected node type")
            let typeNode = 
                match nodeType with 
                | GlobalConstant -> node.ChildNodes.Item(1)
                | GlobalVariable -> node.ChildNodes.Item(1).ChildNodes.Item(1).ChildNodes.Item(0)
                | LocalVariable  -> node.ChildNodes.Item(1).ChildNodes.Item(0)
                | Formula        -> node.ChildNodes.Item(0)
                | _ -> raise (InnerError "Unexpected node type")
            let exprNode : ParseTreeNode option =
                match nodeType with 
                | GlobalConstant -> 
                    let nodesOfInterest = node.ChildNodes.Item(3).ChildNodes
                    if nodesOfInterest.Count > 0
                    then Some (nodesOfInterest.Item(1))
                    else None 
                | GlobalVariable -> 
                    if node.ChildNodes.Item(1).ChildNodes.Item(2).ChildNodes.Count > 0 
                    then Some (node.ChildNodes.Item(1).ChildNodes.Item(2).ChildNodes.Item(1))
                    else None
                | LocalVariable -> 
                    if node.ChildNodes.Item(2).ChildNodes.Count > 0 
                    then Some (node.ChildNodes.Item(2).ChildNodes.Item(1))
                    else None
                | Formula ->
                     Some (node.ChildNodes.Item(3))
                | _ -> raise (InnerError "Unexpected node type")
            let myType = 
                match nodeType with 
                | GlobalConstant -> 
                    if typeNode.ChildNodes.Count = 0 
                    then TBD 
                    else 
                        match typeNode.ChildNodes.Item(0).Token.Text.ToLower() with 
                        | "int" -> TInteger
                        | "double" -> TDouble
                        | "rate" -> TDouble
                        | "prob" -> TDouble
                        | "bool" -> TBool
                        | _ -> invalidArg (typeNode.ChildNodes.Item(0).Term.Name) "Type of constant or variable is inconsistent. Expected int, double, rate, prob, or bool. "
                | Formula -> DataType.TBD
                | _ -> // either GlobalVariable or LocalVariable, but both use the same declaration nodes
                    let typeIndicator = typeNode.Term.Name.ToLower()
                    match typeIndicator with 
                    | "range" -> TInteger
                    | "bool" -> TBool
                    | _ -> invalidArg (typeNode.ChildNodes.Item(0).Term.Name) ("Type of constant or variable '"+name+"' is inconsistent. Expected range or bool at position " + typeNode.Span.Location.ToString())
            let range : Range option = 
                match (myType, nodeType) with
                | (_, GlobalConstant) -> None
                | (TInteger, _)       -> Some (Raw (typeNode.ChildNodes.Item(1),typeNode.ChildNodes.Item(3)))
                | _                   -> None
            new Variable(Some node, exprNode, name,None,myType,nodeType,range)

        static member createVarFromNode(node:ParseTreeNode) = 
            let nodeType =
                match node.Term.Name with 
                | "GlobalConstant" -> GlobalConstant
                | "GlobalVariable" -> GlobalVariable
                | "Declaration"    -> LocalVariable
                | "Formula"        -> Formula
                | _ -> invalidArg "node" ("Expected constant, global variable, local variable, or formula declaration. Read: " + node.Term.Name)
            let nameNode = 
                match nodeType with 
                    | GlobalConstant -> node.ChildNodes.Item(2)
                    | GlobalVariable -> node.ChildNodes.Item(1).ChildNodes.Item(0)
                    | LocalVariable  -> node.ChildNodes.Item(0)
                    | Formula        -> node.ChildNodes.Item(1)
                    | _ -> raise (InnerError "Unexpected node type")
            Variable.createWithName(node, nameNode.Token.Text)

        interface IComparable with
            member this.CompareTo (other:Object) = 
                match other with 
                | :? Variable as other -> this.Name.CompareTo(other.Name)
                | _ -> invalidArg "other" "not a Variable"

        override this.Equals other = self.Name.Equals(other)

        override this.GetHashCode () = this.Name.GetHashCode ()
        
    let createIntConstant (name:String, e:IntExpr) : Variable =
        Variable(None,None,name,Some (Expr.IntExpr e),DataType.TInteger,VariableType.GlobalConstant,None)

    let printDataType t = 
        match t with 
            | TInteger -> "Integer"
            | TDouble -> "Double"
            | TBool -> "Bool"
            | TBD -> "'no type yet'"

    let isConstant (e:Expr) : bool = 
        match e with
        | BoolExpr   (B _) -> true
        | IntExpr    (I _) -> true
        | DoubleExpr (D _) -> true
        | _                -> false

    let rec parseInitialVal (context:Variable list) (renaming : string -> string) (variable:Variable) : unit = 
        match variable.ExprNode with
            | Some x -> 
                let e = simplifyExpr context [variable] (createExpr context renaming x)
                match e with 
                    | BoolExpr e -> 
                        if variable.DataType = TBool || variable.DataType = TBD
                        then 
                            variable.DataType <- TBool
                            variable.Init <- Some (BoolExpr e) 
                        else invalidArg "variable" ("Type mismatch occurred in connection with variable/constant/formula '"+variable.Name+"'. Specified type " + variable.DataType.ToString() + " does not match with expression type 'Bool'.")
                    | IntExpr e -> 
                        match variable.DataType with
                        | TInteger -> variable.Init <- Some (IntExpr e)
                        | TDouble  -> variable.Init <- Some (simplifyExpr context [variable] (DoubleExpr (Cast e)))
                        | TBD      -> 
                            variable.Init <- Some (IntExpr e) 
                            variable.DataType <- TInteger
                        | _        -> invalidArg "variable" ("Type mismatch. Specified type " + printDataType variable.DataType + " does not match with expression type 'Int'.")
                    | DoubleExpr e -> 
                        match variable.DataType with 
                        | TDouble -> variable.Init <- Some (DoubleExpr e) 
                        | TBD     -> 
                            variable.DataType <- TDouble
                            variable.Init <- Some (DoubleExpr e) 
                        | _ -> invalidArg "variable" ("Type mismatch. Specified type " + variable.DataType.ToString() + " does not match with expression type 'Double'.")
                if not (variable.VariableType = Formula) && not (isConstant e) then 
                    report_1 5 "Could not fully evaluate initial value of variable '%s'." variable.Name
            | None -> ()

    and evalConst (context:Variable list) (seen:Variable list) (variable:Variable) : Expr = 
        if List.exists (variable.Name.Equals << fun (x:Variable) -> x.Name) seen then invalidArg "variable" ("Cyclic dependency involving variable '" + variable.Name + "' or this variable occurs twice.")  else 
        if variable.VariableType=GlobalConstant
        then 
            match variable.Init with 
                | Some (BoolExpr (B b)) -> BoolExpr (B b)
                | Some (IntExpr (I i)) -> IntExpr (I i)
                | Some (DoubleExpr (D d)) -> DoubleExpr (D d)
                | Some x ->
                    let e = simplifyExpr context (variable::seen) x
                    do if variable.DataType = TBD then variable.DataType <- typify e else ()
                    if not (typify e = variable.DataType)
                    then invalidArg "variable" ("Type mismatch for variable "+variable.Name+". Specified type was " + printDataType variable.DataType + " but deduced type " + (printDataType << typify) e + (if variable.Node.Value=null then "" else ". See location " + variable.Node.Value.Span.Location.ToString() ))
                    else
                        variable.Init <- Some e;
                        e
                | None -> invalidArg "variable" "No epxression for constant available."
        else invalidArg "variable" "Tried to evaluate a variable that is not a constant ."
        
    and evalRanges (constants:Variable list) (variable:Variable) : unit = 
        match (variable.DataType,variable.Range) with
            | (TInteger, Some (Raw(n1,n2))) -> 
                let lowerBound = simplifyExpr constants [variable] (createExpr constants id n1)
                let upperBound = simplifyExpr constants [variable] (createExpr constants id n2)
                match (lowerBound,upperBound) with
                    | (IntExpr (I l), IntExpr (I u)) -> variable.Range <- Some (Eval (l,u))
                    | _ -> invalidArg "variable" ("Could not evaluate variable ranges of variable '" + variable.Name + ".")
            | _ -> ()
        

    and typify (expr:Expr) = 
        match expr with
            | BoolExpr _ -> TBool
            | IntExpr _ -> TInteger
            | DoubleExpr _ -> TDouble

    and allEqual xs = 
        match xs with 
            | (a::b::xr) -> a=b && allEqual (b::xr)
            | _ -> true

    and unpackInts xs = 
        match xs with
            | IntExpr x :: xr -> x :: unpackInts xr
            | []              -> []
            | _               -> invalidArg "xs" ("Unexpected type in 'max' or 'min' arguments. Expected an integer.")

    and unpackDoubles xs = 
        match xs with
            | IntExpr x :: xr -> (Cast x) :: unpackDoubles xr
            | DoubleExpr x :: xr -> x :: unpackDoubles xr
            | _ -> invalidArg "xs" ("Unexpected type in 'max' or 'min' arguments. Expected an integer or double.")

    and createBoolExpr (context:Variable list) (renaming : string -> string) (node:ParseTreeNode) : BoolExpr = 
        let e = createExpr context renaming node
        match e with
            | BoolExpr b -> b
            | _ -> invalidArg "node" ("Expected boolean expression but found type " + printDataType (typify e) + " at location " + node.Span.Location.ToString())

    and createIntExpr (context:Variable list) (renaming : string -> string) (node:ParseTreeNode) : IntExpr = 
        let e = createExpr context renaming node
        match e with
            | IntExpr i -> i
            | _ -> invalidArg "node" ("Expected integer expression but found type " + printDataType (typify e) + " at location " + node.Span.Location.ToString())

    and createDoubleExpr (context:Variable list) (renaming : string -> string) (node:ParseTreeNode) : DoubleExpr = 
        let e = createExpr context renaming node
        match e with
            | DoubleExpr d -> d
            | IntExpr (I i) -> D (Convert.ToDouble i)
            | _ -> invalidArg "node" ("Expected double expression but found type " + printDataType (typify e) + " at location " + node.Span.Location.ToString())

    and createExpr (context:Variable list) (renaming : string -> string) (node:ParseTreeNode) : Expr = 
        match node.Term.Name.ToLower() with 
            | "number" -> 
                match node.Token.Value with
                    | :? int as newInt -> IntExpr (I newInt)
                    | :? double as newDouble -> DoubleExpr (D newDouble)
                    | _ -> invalidArg "node" ("Unexpected type in number node: " + node.ToString())
            | "false" -> BoolExpr (B false)
            | "true" -> BoolExpr (B true)
            | "identifier" -> 
                let varname = renaming node.Token.Text
                let var = List.tryFind (varname.Equals << fun (x:Variable) -> x.Name)  context 
                in match var with
                    | None -> invalidArg "Identifier" ("Unknown identifier '"+renaming node.Token.Text+"' (corresponding to '" + node.Token.Text + "') at " + node.Span.Location.ToString() + ". Possible use of variable to initialize a second variable.")
                    | Some x -> 
                        match x.DataType with
                            | TBool -> BoolExpr (BoolVar x)
                            | TInteger -> IntExpr (IntVar x)
                            | TDouble -> DoubleExpr (DoubleVar x)
                            | TBD -> invalidArg "Identifier" ("Identifier with unknown type: '"+node.Token.Text+"' at " + node.Span.Location.ToString() + ".") // happens only for formulas
            | "binexpr" -> 
                let leftarg   = createExpr context renaming (node.ChildNodes.Item(0))
                let rightarg  = createExpr context renaming (node.ChildNodes.Item(2))
                in
                    match node.ChildNodes.Item(1).Term.Name with
                            | "=>" -> 
                                match (leftarg, rightarg) with 
                                    | (BoolExpr b1, BoolExpr b2) -> BoolExpr (Or (Not b1,b2))
                                    | _       -> invalidArg "node" ("Types of operator '=>' do not match at " + node.Span.Location.ToString())
                            | "<=>" -> 
                                match (leftarg, rightarg) with 
                                    | (BoolExpr b1, BoolExpr b2) -> BoolExpr (IFF (b1,b2))
                                    | _       -> invalidArg "node" ("Types of operator '<=>' do not match at " + node.Span.Location.ToString())
                            | "|" -> 
                                match (leftarg, rightarg) with 
                                    | (BoolExpr b1, BoolExpr b2) -> BoolExpr (Or (b1,b2))
                                    | _       -> invalidArg "node" ("Types of operator '|' do not match at " + node.Span.Location.ToString())
                            | "&" -> 
                                match (leftarg, rightarg) with 
                                    | (BoolExpr b1, BoolExpr b2) -> BoolExpr (And (b1,b2))
                                    | _       -> invalidArg "node" ("Types of operator '&' do not match at " + node.Span.Location.ToString())
                            | "=" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> BoolExpr (Eq(i1,i2))
                                    | (IntExpr i, DoubleExpr d) -> BoolExpr (DEq(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> BoolExpr (DEq(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> BoolExpr (DEq(d1,d2))
                                    | (BoolExpr b1, BoolExpr b2) -> BoolExpr (IFF (b1,b2))
                                    | _       -> invalidArg "node" ("Types of operator '=' do not match at " + node.Span.Location.ToString())
                            | "!=" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> BoolExpr (Not (Eq(i1,i2)))
                                    | (IntExpr i, DoubleExpr d) -> BoolExpr (Not (DEq(Cast i, d)))
                                    | (DoubleExpr d, IntExpr i) -> BoolExpr (Not (DEq(d,Cast i)))
                                    | (DoubleExpr d1, DoubleExpr d2) -> BoolExpr (Not (DEq(d1,d2)))
                                    | (BoolExpr b1, BoolExpr b2) -> BoolExpr (Not (IFF (b1,b2)))
                                    | _       -> invalidArg "node" ("Types of operator '!=' do not match at " + node.Span.Location.ToString())
                            | "+" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> IntExpr (IntExpr.Plus(i1,i2))
                                    | (IntExpr i, DoubleExpr d) -> DoubleExpr (Plus(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> DoubleExpr (Plus(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> DoubleExpr (Plus(d1,d2))
                                    | _       -> invalidArg "node" ("Types of operator '+' do not match at " + node.Span.Location.ToString())
                            | "-" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> IntExpr (IntExpr.Minus(i1,i2))
                                    | (IntExpr i, DoubleExpr d) -> DoubleExpr (Minus(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> DoubleExpr (Minus(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> DoubleExpr (Minus(d1,d2))
                                    | _       -> invalidArg "node" ("Types of operator '-' do not match at " + node.Span.Location.ToString())
                            | "*" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> IntExpr (IntExpr.Mult(i1,i2))
                                    | (IntExpr i, DoubleExpr d) -> DoubleExpr (Mult(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> DoubleExpr (Mult(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> DoubleExpr (Mult(d1,d2))
                                    | _       -> invalidArg "node" ("Types of operator '*' do not match at " + node.Span.Location.ToString())
                            | "/" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> DoubleExpr (Div(Cast i1, Cast i2))
                                    | (IntExpr i, DoubleExpr d) -> DoubleExpr (Div(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> DoubleExpr (Div(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> DoubleExpr (Div(d1,d2))
                                    | _       -> invalidArg "node" ("Types of operator '/' do not match at " + node.Span.Location.ToString())
                            | "<" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> BoolExpr (Lesser(i1, i2))
                                    | (IntExpr i, DoubleExpr d) -> BoolExpr (DLesser(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> BoolExpr (DLesser(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> BoolExpr (DLesser(d1,d2))
                                    | _       -> invalidArg "node" ("Types of operator '<' do not match at " + node.Span.Location.ToString())
                            | "<=" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> BoolExpr (LEq(i1, i2))
                                    | (IntExpr i, DoubleExpr d) -> BoolExpr (DLEq(Cast i, d))
                                    | (DoubleExpr d, IntExpr i) -> BoolExpr (DLEq(d,Cast i))
                                    | (DoubleExpr d1, DoubleExpr d2) -> BoolExpr (DLEq(d1,d2))
                                    | _       -> invalidArg "node" ("Types of operator '<=' do not match at " + node.Span.Location.ToString())
                            | ">=" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> BoolExpr (LEq(i2,i1))
                                    | (IntExpr i, DoubleExpr d) -> BoolExpr (DLEq(d, Cast i))
                                    | (DoubleExpr d, IntExpr i) -> BoolExpr (DLEq(Cast i, d))
                                    | (DoubleExpr d1, DoubleExpr d2) -> BoolExpr (DLEq(d2,d1))
                                    | _       -> invalidArg "node" ("Types of operator '>=' do not match at " + node.Span.Location.ToString())
                            | ">" -> 
                                match (leftarg, rightarg) with 
                                    | (IntExpr i1, IntExpr i2) -> BoolExpr (Lesser(i2,i1))
                                    | (IntExpr i, DoubleExpr d) -> BoolExpr (DLesser(d, Cast i))
                                    | (DoubleExpr d, IntExpr i) -> BoolExpr (DLesser(Cast i, d))
                                    | (DoubleExpr d1, DoubleExpr d2) -> BoolExpr (DLesser(d2,d1))
                                    | _       -> invalidArg "node" ("Types of operator '<=' do not match at " + node.Span.Location.ToString())
                            | x -> invalidArg "node" ("Expected operator symbol, but read: " + x + " at " + node.Span.Location.ToString())
            | "unexpr" -> 
                let arg = createExpr context renaming (node.ChildNodes.Item(1))
                in match node.ChildNodes.Item(0).Token.Text with
                    | "!" -> 
                        match arg with 
                            | BoolExpr b -> BoolExpr (Not b)
                            | _ -> invalidArg "arg" ("Argument type of unary operator '!' does not match at " + node.Span.Location.ToString())
                    | "+" -> 
                        match arg with 
                            | IntExpr i -> IntExpr i
                            | DoubleExpr d -> DoubleExpr d
                            | _ -> invalidArg "arg" ("Argument type of unary operator '+' does not match at " + node.Span.Location.ToString())
                    | "-" -> 
                        match arg with 
                            | IntExpr i -> IntExpr (IntExpr.UMinus i)
                            | DoubleExpr d -> DoubleExpr (UMinus d)
                            | _ -> invalidArg "arg" ("Argument type of unary operator '-' does not match at " + node.Span.Location.ToString())
                    | x -> invalidArg "node" ("Expected operator symbol, but read: " + x + " at " + node.Span.Location.ToString())
            | "ternaryexpr" ->
                let firstarg  = createExpr context renaming (node.ChildNodes.Item(0))
                let secondarg  = createExpr context renaming (node.ChildNodes.Item(2))
                let thirdarg  = createExpr context renaming (node.ChildNodes.Item(3))
                match (firstarg,secondarg,thirdarg) with
                    | (BoolExpr x1, BoolExpr x2, BoolExpr x3) -> BoolExpr (BoolExpr.ITE (x1,x2,x3))
                    | (BoolExpr x1, IntExpr x2, IntExpr x3) -> IntExpr (IntExpr.ITE (x1,x2,x3))
                    | (BoolExpr x1, DoubleExpr x2, DoubleExpr x3) -> DoubleExpr (DoubleExpr.ITE (x1,x2,x3))
                    | _ -> invalidArg "node" ("Type mismatch for If-then-else expression at: " + node.Span.Location.ToString())
            | "functioncall" -> 
                let argList = List.map (createExpr context renaming) (Utils.toList (node.ChildNodes.Item(1).ChildNodes))
                in if not argList.IsEmpty then
                    match node.ChildNodes.Item(0).Token.Text with 
                        | "min" -> 
                            if List.forall ((=) TInteger << typify) argList then IntExpr (IntExpr.Min (unpackInts argList)) 
                            else if List.forall ((fun x -> x = TDouble || x = TInteger) << typify) argList then DoubleExpr (DoubleExpr.Min (unpackDoubles argList)) 
                            else invalidArg "node" ("Type mismatch in argument list of 'min' at " + node.Span.Location.ToString()) 
                        | "max" -> 
                            if List.forall ((=) TInteger << typify) argList then IntExpr (IntExpr.Max (unpackInts argList)) 
                            else if List.forall ((fun x -> x = TDouble || x = TInteger) << typify) argList then DoubleExpr (DoubleExpr.Max (unpackDoubles argList)) 
                            else invalidArg "node" ("Type mismatch in argument list of 'max' at " + node.Span.Location.ToString()) 
                        | "ceil" -> 
                            match argList with
                                | [IntExpr i] -> IntExpr i
                                | [DoubleExpr d] -> IntExpr (Ceil d)
                                | [BoolExpr _] -> invalidArg "node" ("Cannot apply function 'ceil' to boolean arguments. See " + node.Span.Location.ToString()) 
                                | _ -> invalidArg "node" ("Too many arguments for 'ceil' at " + node.Span.Location.ToString()) 
                        | "floor" -> 
                            match argList with
                                | [IntExpr i] -> IntExpr i
                                | [DoubleExpr d] -> IntExpr (Floor d)
                                | [BoolExpr _] -> invalidArg "node" ("Cannot apply function 'floor' to boolean arguments. See " + node.Span.Location.ToString()) 
                                | _ -> invalidArg "node" ("Too many arguments for 'floor' at " + node.Span.Location.ToString()) 
                        | "pow" -> 
                            match argList with
                                | [IntExpr i1; IntExpr i2] -> IntExpr (Pow (i1,i2))
                                | [x] -> invalidArg "node" ("Missing arguments for 'pow' at " + node.Span.Location.ToString()) 
                                | _ -> invalidArg "node" ("Type mismatch or too many arguments for 'pow' at " + node.Span.Location.ToString()) 
                        | "mod" -> 
                            match argList with
                                | [IntExpr i1; IntExpr i2] -> IntExpr (Mod (i1,i2))
                                | [x] -> invalidArg "node" ("Missing arguments for 'mod' at " + node.Span.Location.ToString()) 
                                | _ -> invalidArg "node" ("Type mismatch or too many arguments for 'mod' at " + node.Span.Location.ToString()) 
                        | "log" -> 
                            match argList with
                                | [IntExpr i1; IntExpr i2] -> DoubleExpr (Log (Cast i1, Cast i2))
                                | [DoubleExpr d; IntExpr i] -> DoubleExpr (Log (d, Cast i))
                                | [DoubleExpr d1; DoubleExpr d2] -> DoubleExpr (Log (d1, d2))
                                | [x] -> invalidArg "node" ("Missing arguments for 'log' at " + node.Span.Location.ToString()) 
                                | _ -> invalidArg "node" ("Type mismatch or too many arguments for 'mod' at " + node.Span.Location.ToString()) 
                        | "func" -> invalidArg "node" ("Function calls via the keyword func are not supported. Please update your model to the new Prism standard.")
                        | x -> invalidArg "node" ("Unknown function name: " + x + " at " + node.Span.Location.ToString()) 
                    else invalidArg "node" ("Operands of function " + node.ChildNodes.Item(0).Term.Name + " at "+node.Span.Location.ToString()+" are missing.") 
            | x -> invalidArg "node" ("Unknown expression subtype: " + x)


    and simplifyExpr (context:Variable list) (seen:Variable list) (expr:Expr) = 
        match expr with
            | BoolExpr b -> BoolExpr (simplifyBoolExpr context seen b)
            | IntExpr i -> IntExpr (simplifyIntExpr context seen i)
            | DoubleExpr d -> DoubleExpr (simplifyDoubleExpr context seen d)
            
    and simplifyBoolExpr (context:Variable list) (seen:Variable list) (expr:BoolExpr) : BoolExpr = 
        match expr with 
            | BoolExpr.Or (a,b) -> 
                let a' = simplifyBoolExpr context seen a
                let b' = simplifyBoolExpr context seen b
                match (a',b') with
                    | (B true, _) -> B true
                    | (_, B true) -> B true
                    | (B false, _) -> b'
                    | (_, B false) -> a'
                    | _ -> Or (a',b') 
            | BoolExpr.And (a,b) -> 
                let a' = simplifyBoolExpr context seen a
                let b' = simplifyBoolExpr context seen b
                match (a',b') with
                    | (B true, _) -> b'
                    | (_, B true) -> a'
                    | (B false, _) -> B false
                    | (_, B false) -> B false
                    | _ -> And (a',b') 
            | BoolExpr.IFF (a,b) -> 
                let a' = simplifyBoolExpr context seen a
                let b' = simplifyBoolExpr context seen b
                match (a',b') with
                    | (B true, _) -> b'
                    | (_, B true) -> a'
                    | (B false, _) -> Not b'
                    | (_, B false) -> Not a'
                    | _ -> IFF(a',b') // alternatively compute normal form and check for identity
            | BoolExpr.Not a -> 
                let a' = simplifyBoolExpr context seen a
                match a' with
                    | B b -> B (not b)
                    | Not a'' -> a'' // alternatively compute nnf here
                    | _ -> Not a'
            | BoolExpr.Eq (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with
                    | (I i1, I i2) -> B (i1=i2)
                    | _ -> Eq(a',b') // alternatively compute normal form and check for identity
            | BoolExpr.LEq (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with
                    | (I i1, I i2) -> B (i1<=i2)
                    | _ -> LEq(a',b') // alternatively compute normal form and check for identity
            | BoolExpr.Lesser (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with
                    | (I i1, I i2) -> B (i1<i2)
                    | _ -> Lesser (a',b') // alternatively compute normal form and check for identity
            | BoolExpr.DEq (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with
                    | (D d1, D d2) -> B (d1=d2)
                    | _ -> DEq (a',b') // alternatively compute normal form and check for identity
            | BoolExpr.DLesser (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with
                    | (D d1, D d2) -> B (d1<d2)
                    | _ -> DLesser (a',b') // alternatively compute normal form and check for identity
            | BoolExpr.DLEq (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with
                    | (D d1, D d2) -> B (d1<=d2)
                    | _ -> DLEq (a',b') // alternatively compute normal form and check for identity
            | BoolExpr.ITE (a,b,c) -> 
                let a' = simplifyBoolExpr context seen a
                let b' = simplifyBoolExpr context seen b
                let c' = simplifyBoolExpr context seen c
                match (a',b',c') with
                    | (B true, _, _) -> b'
                    | (B false, _, _) -> c'
                    | (_, B false, B false) -> B false
                    | (_, B true, B true) -> B true
                    | (_, B true, _) -> Or (a',c')
                    | (_, _, B true) -> Or (Not a',b')
                    | (_, B false, _) -> And (Not a',c')
                    | (_, _, B false) -> And (a',b')
                    | _ -> BoolExpr.ITE (a',b',c') // alternatively compute normal form and check for identity
            | BoolExpr.BoolVar v -> 
                if v.VariableType = GlobalConstant then 
                    let varVal = evalConst context seen v
                    match varVal with
                        | BoolExpr (B i) -> B i
                        | BoolExpr _ -> invalidArg "v" ("Could not properly evaluate constant" + v.Name) 
                        | _ -> invalidArg "v" ("Type mismatch of variable " + v.Name) 
                else 
                    BoolVar v
            | B b -> B b
    
    and getMaximalDouble xs max = 
        match xs with
            | [] -> max
            | (D x) :: xr -> if x>max then getMaximalDouble xr x else getMaximalDouble xr max
            | _ :: xr -> raise (Utils.InnerError "Not evaluated correctly.")

    and getMinimalDouble xs min = 
        match xs with
            | [] -> min
            | (D x) :: xr -> if x<min then getMinimalDouble xr x else getMinimalDouble xr min
            | _ :: xr -> raise (Utils.InnerError "Not evaluated correctly.")

    and simplifyDoubleExpr (context:Variable list) (seen:Variable list) (expr:DoubleExpr) : DoubleExpr = 
        match expr with 
            | DoubleExpr.Plus (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with
                    | (D 0.0, _) -> b'
                    | (_, D 0.0) -> a'
                    | (D a'', D b'') -> D (a'' + b'')
                    | _ -> DoubleExpr.Plus (a',b') 
            | DoubleExpr.Minus (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with 
                    | (D a'', D b'') -> D (a'' - b'')
                    | (D 0.0, b'') -> DoubleExpr.UMinus(b'')
                    | (_, D 0.0) -> a'
                    | _ -> DoubleExpr.Minus (a',b') 
            | DoubleExpr.Mult (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with 
                    | (D 0.0, _) -> D 0.0
                    | (_, D 0.0) -> D 0.0
                    | (D 1.0, _) -> b'
                    | (_, D 1.0) -> a' 
                    | (D a'', D b'') -> D (a'' * b'')
                    | _ -> DoubleExpr.Mult (a',b') 
            | DoubleExpr.Div (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with 
                    | (_, D 0.0) -> invalidArg "expr" ("Division by zero while simplifying expressions.")
                    | (D 0.0, _) -> D 0.0
                    | (_, D 1.0) -> a' 
                    | (D a'', D b'') -> D (a'' / b'')
                    | _ -> DoubleExpr.Div (a',b') 
            | DoubleExpr.ITE (a,b,c) -> 
                let a' = simplifyBoolExpr context seen a
                match a' with
                    | B true -> 
                        simplifyDoubleExpr context seen b
                    | B false -> 
                        simplifyDoubleExpr context seen c
                    | _ -> DoubleExpr.ITE (a', simplifyDoubleExpr context seen b, simplifyDoubleExpr context seen c)
            | DoubleExpr.UMinus a -> 
                let a' = simplifyDoubleExpr context seen a
                match a' with
                    | D a'' -> D (-a'')
                    | _ -> DoubleExpr.UMinus (a')
            | DoubleExpr.Min dlist -> 
                let dlist' = List.map (simplifyDoubleExpr context seen) dlist
                if List.forall (fun x -> match x with D _ -> true | _ -> false) dlist' then D (getMinimalDouble dlist' Double.MaxValue) else DoubleExpr.Min dlist'
            | DoubleExpr.Max ilist -> 
                let ilist' = List.map (simplifyDoubleExpr context seen) ilist
                if List.forall (fun x -> match x with D _ -> true | _ -> false) ilist' then D (getMaximalDouble ilist' Double.MinValue) else DoubleExpr.Max ilist'
            | DoubleExpr.Log (a,b) -> 
                let a' = simplifyDoubleExpr context seen a
                let b' = simplifyDoubleExpr context seen b
                match (a',b') with 
                    | (D a'', D b'') -> if a'' <= 0.0 || b''<= 0.0 then invalidArg "expr" "Cannot compute log <= 0 or log to with base <= 0." else  D (log a'' / log b'')
                    | _ -> DoubleExpr.Log (a',b') 
            | DoubleExpr.DoubleVar a -> 
                if a.VariableType = GlobalConstant then 
                    let varVal = evalConst context seen a
                    match varVal with
                        | DoubleExpr (D d) -> D d
                        | DoubleExpr d -> invalidArg "a" ("Could not properly evaluate constant" + a.Name) 
                        | IntExpr (I i) -> D (Convert.ToDouble(i))
                        | _ -> invalidArg "a" ("Type mismatch of variable " + a.Name) 
                else 
                    DoubleVar (List.find (a.Name.Equals << fun x -> x.Name) context)
            | D d -> D d
            | DoubleExpr.Cast i -> 
                let i' = simplifyIntExpr context seen i
                match i' with 
                    | I i -> D (Convert.ToDouble(i))
                    | _ -> Cast i'
            


    and getMaximalInt xs max = 
        match xs with
            | [] -> max
            | (I x) :: xr -> if x>max then getMaximalInt xr x else getMaximalInt xr max
            | _ :: xr -> raise (Utils.InnerError "Not evaluated correctly.")

    and getMinimalInt xs min = 
        match xs with
            | [] -> min
            | (I x) :: xr -> if x<min then getMinimalInt xr x else getMinimalInt xr min
            | _ :: xr -> raise (Utils.InnerError "Not evaluated correctly.")

    and simplifyIntExpr (context:Variable list) (seen:Variable list) (expr:IntExpr) : IntExpr = 
        match expr with 
            | IntExpr.Plus (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with
                    | (I 0, _) -> b'
                    | (_, I 0) -> a'
                    | (I a'', I b'') -> I (a'' + b'')
                    | _ -> IntExpr.Plus (a',b') 
            | IntExpr.Minus (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with 
                    | (I a'', I b'') -> I (a'' - b'')
                    | (I 0, b'') -> IntExpr.UMinus(b'')
                    | (_, I 0) -> a'
                    | _ -> IntExpr.Minus (a',b') 
            | IntExpr.Mult (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with 
                    | (I 0, _) -> I 0
                    | (_, I 0) -> I 0
                    | (I 1, _) -> b'
                    | (_, I 1) -> a' 
                    | (I a'', I b'') -> I (a'' * b'')
                    | _ -> IntExpr.Mult (a',b') 
            | IntExpr.ITE (a,b,c) -> 
                let a' = simplifyBoolExpr context seen a
                let b' = simplifyIntExpr context seen b
                let c' = simplifyIntExpr context seen c
                match (a',b',c') with
                    | (B true, _, _) -> b'
                    | (B false, _, _) -> c'
                    | _ -> IntExpr.ITE (a',b',c') // alternatively compute normal form and check for identity
            | IntExpr.UMinus a -> 
                let a' = simplifyIntExpr context seen a
                match a' with
                    | I a'' -> I (-a'')
                    | _ -> IntExpr.UMinus (a')
            | IntExpr.Min ilist -> 
                let ilist' = List.map (simplifyIntExpr context seen) ilist
                if List.forall (fun x -> match x with I i -> true | _ -> false) ilist' then I (getMinimalInt ilist' Int32.MaxValue) else IntExpr.Min ilist'
            | IntExpr.Max ilist -> 
                let ilist' = List.map (simplifyIntExpr context seen) ilist
                if List.forall (fun x -> match x with I i -> true | _ -> false) ilist' then I (getMaximalInt ilist' Int32.MinValue) else IntExpr.Max ilist'
            | IntExpr.Floor d -> 
                let d' = simplifyDoubleExpr context seen d
                match d' with 
                    | D d'' -> I (Convert.ToInt32(floor d''))
                    | _ -> Floor d'
            | IntExpr.Ceil d -> 
                let d' = simplifyDoubleExpr context seen d
                match d' with 
                    | D d'' -> I (Convert.ToInt32(ceil d''))
                    | _ -> Ceil d'
            | IntExpr.Pow (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with 
                    | (_, I 0) -> I 1
                    | (I 0, _) -> I 0
                    | (I 1, _) -> I 1
                    | (_, I 1) -> a'
                    | (I a'', I b'') -> I (BigInteger.op_Explicit(bigint.Pow(new BigInteger(a''),b''))) 
                    | _ -> IntExpr.Pow (a',b') 
            | IntExpr.Mod (a,b) -> 
                let a' = simplifyIntExpr context seen a
                let b' = simplifyIntExpr context seen b
                match (a',b') with 
                    | (_, I 0) -> invalidArg "b'" "Modulo 0, seriously?"
                    | (_, I 1) -> I 0
                    | (I 0, _) -> I 0
                    | (I a'', I b'') -> I (a'' % b'') 
                    | _ -> IntExpr.Mod (a',b')
            | IntExpr.IntVar a -> 
                if a.VariableType = GlobalConstant then 
                    let varVal = evalConst context seen a
                    match varVal with
                        | IntExpr (I i) -> I i
                        | IntExpr _ -> invalidArg "a" ("Could not properly evaluate constant" + a.Name) 
                        | _ -> invalidArg "a" ("Type mismatch of variable " + a.Name) 
                else 
                    IntVar a
            | I a -> I a

    
    

    