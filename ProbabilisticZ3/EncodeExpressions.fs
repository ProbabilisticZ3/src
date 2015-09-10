// MN Rabe

namespace ProbabilisticZ3

open System

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open EncodingContext

module ExpressionEncodings =

    type RoundingType =
        | ROUND_DOWN
        | ROUND_UP

    // Depending on the context, expressions might have to refer to the variables of a particular step, or to a generic variable. This is indicated by the option type step number. 
    let rec translateExpr (co : EncodingContext) (step : int option) (at:RoundingType option) : Expressions.Expr -> Microsoft.Z3.Expr = function
        | BoolExpr e -> upcast translateBoolExpr co step at e 
        | IntExpr e -> upcast translateIntExpr co step at e
        | DoubleExpr e -> upcast translateDoubleExpr co step at e

    and translateBoolExpr (co:EncodingContext) (step:int option) (at:RoundingType option) : Expressions.BoolExpr -> Microsoft.Z3.BoolExpr = function
        | Or (b1,b2)      -> co.z3.MkOr(List.toArray (List.map (translateBoolExpr co step at) [b1;b2]))
        | And (b1,b2)     -> co.z3.MkAnd(List.toArray (List.map (translateBoolExpr co step at) [b1;b2]))
        | IFF (b1,b2)     -> co.z3.MkIff(translateBoolExpr co step at b1, translateBoolExpr co step at b2)
        | Not b           -> co.z3.MkNot(translateBoolExpr co step at b)
        | Eq (i1,i2)      -> co.z3.MkEq(translateExpr co step at (Expr.IntExpr i1), translateExpr co step at (Expr.IntExpr i2))
        | LEq (i1,i2)     -> co.z3.MkBVSLE(translateIntExpr co step at i1, translateIntExpr co step at i2)
        | Lesser (i1,i2)  -> co.z3.MkBVSLT(translateIntExpr co step at i1, translateIntExpr co step at i2)
        | DEq (d1,d2)     -> co.z3.MkEq(translateExpr co step at (Expr.DoubleExpr d1), translateExpr co step at (Expr.DoubleExpr d2))
        | DLEq (d1,d2)    -> co.z3.MkBVULE(translateDoubleExpr co step at d1, translateDoubleExpr co step at d2)
        | DLesser (d1,d2) -> co.z3.MkBVULT(translateDoubleExpr co step at d1, translateDoubleExpr co step at d2)
        | BoolExpr.ITE (b1,b2,b3) -> downcast co.z3.MkITE(translateBoolExpr co step at b1, translateExpr co step at (Expr.BoolExpr b2), translateExpr co step at (Expr.BoolExpr b3))
        | BoolVar v       -> 
            match step with
            | Some s -> downcast variable2Z3Const_step co v s // applyBoolVarStep co v s
            | None   -> downcast variable2Z3Const_arg co v // varArgConst co v
        | B b             -> co.z3.MkBool(b)

    and translateIntExpr (co:EncodingContext) (step:int option) (at:RoundingType option) : Expressions.IntExpr -> Microsoft.Z3.BitVecExpr = function
        | IntExpr.Plus (i1,i2)  -> co.z3.MkBVAdd(translateIntExpr co step at i1, translateIntExpr co step at i2)  // TODO with or without overflow? cf z3.MkBVAddNoOverflow
        | IntExpr.Minus (i1,i2) -> co.z3.MkBVSub(translateIntExpr co step at i1, translateIntExpr co step at i2)
        | IntExpr.Mult (i1,i2)  -> co.z3.MkBVMul(translateIntExpr co step at i1, translateIntExpr co step at i2) // TODO 
        | IntExpr.ITE (b,i1,i2) -> downcast co.z3.MkITE(translateBoolExpr co step at b, translateExpr co step at (Expr.IntExpr i1), translateExpr co step at (Expr.IntExpr i2))
        | IntExpr.UMinus i      -> co.z3.MkBVSub(co.z3.MkBV(0,uint32 co.problem.intEncoding),translateIntExpr co step at i)
        | IntExpr.Min is        -> 
            List.fold (fun x -> fun y -> downcast co.z3.MkITE(co.z3.MkBVSLE(x,y),x,y)) (translateIntExpr co step at (List.head is)) (List.map (translateIntExpr co step at) (List.tail is)) 
        | IntExpr.Max is        -> 
            List.fold (fun x -> fun y -> downcast co.z3.MkITE(co.z3.MkBVSGE(x,y),x,y)) (translateIntExpr co step at (List.head is)) (List.map (translateIntExpr co step at) (List.tail is)) 
        | Floor d               -> raise NotYetImplemented // cut off ... fixed point representation
        | Ceil d                -> raise NotYetImplemented // cut off ... fixed point representation
        | Pow (i1,i2)           -> raise NotYetImplemented
        | Mod (i1,i2)           -> raise NotYetImplemented
        | IntVar v              -> 
            match step with
            | Some s -> downcast variable2Z3Const_step co v s // applyBVVarStep co v s
            | None   -> downcast variable2Z3Const_arg co v // varArgConst co v
        | I i                   -> upcast co.z3.MkBV(i, co.intBVSize)

    and translateDoubleExpr (co:EncodingContext) (step:int option) (at:RoundingType option) : Expressions.DoubleExpr -> Microsoft.Z3.BitVecExpr = function // TODO: introduce rounding mode as one of the parameters
        | DoubleExpr.Plus (d1,d2)  -> co.z3.MkBVAdd(translateDoubleExpr co step at d1, translateDoubleExpr co step at d2) 
        | DoubleExpr.Minus (d1,d2) -> co.z3.MkBVSub(translateDoubleExpr co step at d1, translateDoubleExpr co step at d2) 
        | DoubleExpr.Mult (d1,d2)  -> 
            let operand1 = co.z3.MkConcat(co.doubleZero,translateDoubleExpr co step at d1)
            let operand2 = co.z3.MkConcat(co.doubleZero,translateDoubleExpr co step at d2)
            co.z3.MkExtract(
                uint32(co.problem.fractionsEncoding)+co.doubleBVSize-1u,
                uint32(co.problem.fractionsEncoding),
                co.z3.MkBVMul(operand1, operand2)) 
        | DoubleExpr.Div (d1,d2)   -> 
            // TODO: this is optimized for the case that the numerator is small, and the other number is fairly large. It might cut off the most significant bits of the first number. Good luck. 
            // TODO: the numbers might potentially be negative. we would have to treat the first bit specially, by pulling it to the front. 
            report_0 5 "Warning: dangerous use of division for fractional numbers. When using divisions involving variables, we currently use an underapproximation." 
            let d1' = translateDoubleExpr co step at d1
            let d2' = translateDoubleExpr co step at d2
            let d1'' = co.z3.MkConcat(d1',co.z3.MkBV(0, uint32 co.problem.fractionsEncoding))
            let d2'' = co.z3.MkConcat(co.z3.MkBV(0, uint32 co.problem.fractionsEncoding),d2')
            let res = co.z3.MkBVUDiv(d1'',d2'')
            let resTruncated = co.z3.MkExtract(uint32 (co.problem.fractionsEncoding+co.problem.intEncoding-1),0u,res)
            let resTSimp : BitVecExpr = downcast resTruncated.Simplify()
            resTSimp
        | DoubleExpr.ITE (b,d1,d2) -> downcast co.z3.MkITE(translateBoolExpr co step at b, translateExpr co step at (Expr.DoubleExpr d1), translateExpr co step at (Expr.DoubleExpr d2))
        | DoubleExpr.UMinus i      -> co.z3.MkBVSub(co.z3.MkBV(0,uint32(co.problem.fractionsEncoding+co.problem.intEncoding)),translateDoubleExpr co step at i)
        | DoubleExpr.Log (d1,d2)   -> raise NotYetImplemented // z3.MkBV(translateDoubleExpr z3 i) // TODO 
        | DoubleExpr.Min ds        -> 
            List.fold (fun x -> fun y -> downcast co.z3.MkITE(co.z3.MkBVSLE(x,y), x, y)) (translateDoubleExpr co step at (List.head ds)) (List.map (translateDoubleExpr co step at) (List.tail ds)) 
        | DoubleExpr.Max ds        -> 
            List.fold (fun x -> fun y -> downcast co.z3.MkITE(co.z3.MkBVSGE(x,y), x, y)) (translateDoubleExpr co step at (List.head ds)) (List.map (translateDoubleExpr co step at) (List.tail ds))
        | DoubleVar v              -> 
            match step with
            | Some s -> downcast variable2Z3Const_step co v s // applyBVVarStep co v s
            | None   -> downcast variable2Z3Const_arg co v // varArgConst co v
        | D d                      -> 
            let v = d*(2.0**Convert.ToDouble(uint32(co.problem.fractionsEncoding)))
            let integerizedValue_lower : Int64 = Convert.ToInt64(floor v)
            let integerizedValue_upper : Int64 = Convert.ToInt64(ceil v)
            match at with
            | Some ROUND_DOWN -> 
                upcast co.z3.MkBV(integerizedValue_lower, co.doubleBVSize)
            | Some ROUND_UP ->
                upcast co.z3.MkBV(integerizedValue_upper, co.doubleBVSize)
            | None -> 
                assert(integerizedValue_lower=integerizedValue_upper)
                upcast co.z3.MkBV(integerizedValue_lower, co.doubleBVSize)
        | Cast i                   -> // TODO: this is an unsafe operation at the moment! Shifting numbers might have funny effects. 
            match i with 
            | I x -> translateDoubleExpr co step at (D (Convert.ToDouble(x)))
            | _ -> 
                let requiredInitialZeros : uint32 = co.doubleBVSize - uint32(co.problem.fractionsEncoding) - co.intBVSize
                let res = 
                    if requiredInitialZeros>0u then 
                        let initialZeros : BitVecExpr  = upcast co.z3.MkBV(0u, requiredInitialZeros)
                        let finalZeros : BitVecExpr    = upcast co.z3.MkBV(0u, uint32(co.problem.fractionsEncoding))
                        co.z3.MkConcat(co.z3.MkConcat(initialZeros, translateIntExpr co step at i),finalZeros)
                    else 
                        let finalZeros : BitVecExpr    = upcast co.z3.MkBV(0u, uint32(co.problem.fractionsEncoding))
                        co.z3.MkConcat(translateIntExpr co step at i, finalZeros)
                let resSimp = downcast res.Simplify()
                resSimp