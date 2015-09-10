// MN Rabe

namespace ProbabilisticZ3

open System // for Conversions of basic data types

open PrismModel
open Utils
open Expressions
open Microsoft.Z3
open Problems
open EncodingContext
open ExpressionEncodings
open Cubes
open CounterExamples
open AnalyzerContexts

module CubeEncoding =
        
    // The exact numbers of random variables may have shifted partially compared to the 
    // module numbers, due to the elimination of random variables for modules with no 
    // random decisions. This function inserts empty elements where they have been deleted previously. 
//    let rec matchRandomVariablesToModules (co:EncodingContext) (randoms:Expr list) (modules:PrismModule list) : (Expr option) list = 
//        match modules with
//        | m::mr -> 
//            if   co.moduleInfos.Item(m.Name).localRandomVar_arg.IsSome 
//            then Some randoms.Head :: matchRandomVariablesToModules co randoms.Tail mr
//            else None :: matchRandomVariablesToModules co randoms mr
//        | [] -> assert(randoms.IsEmpty); [] 
            

    // Connects the cubes with the random variables
    let encodeCube (co:EncodingContext) (cube:Cube) (randomVars:Expr list list) : BoolExpr = 
        // The following computation is rather expensive and could be improved. It is quadratic in the number 
        // of steps and the number of modules. The resulting expression should not be too complex, though. 

        // This constraint requires that the randomVars accord to the values specified by the cube 
        let oneCubeOneStep (randomVarsForThisStep:Expr list, step:int) : BoolExpr list = 
            let stepExpr = co.z3.MkBV(step, co.stepBVSize)
            List.collect
                (fun (moduleCount:int, rvar:Expr option, m:PrismModule) -> 
                    if co.moduleInfos.Item(m.Name).localRandomVar_arg.IsSome // then we know that in this case also rvars.IsSome
                    then
                        let moduleCountExpr : BitVecExpr = upcast co.z3.MkBV(moduleCount, co.moduleNumberBVSize)
                        List.map 
                            (fun (bitSelector:BitSelector,bitVal:BitVecExpr) ->
                                let (paddedRandomArg:BitVecExpr,paddedBitS:BitVecExpr) = 
                                    if co.randomBVSize = co.positionBVSize // positionBVSize is log(randomBVSize) hence it is always lesser or equal
                                    then (downcast rvar.Value, bitSelector.PosSelector)
                                    else (downcast rvar.Value, co.z3.MkConcat(co.z3.MkBV(0, co.randomBVSize - co.positionBVSize), bitSelector.PosSelector))

                                co.z3.MkImplies(
                                    z3mkAnd co.z3 [
                                        co.z3.MkEq(bitSelector.StepSelector, stepExpr); 
                                        co.z3.MkEq(bitSelector.ModuleSelector, moduleCountExpr)], 
                                    co.z3.MkEq(
                                        co.z3.MkExtract(0u, 0u, co.z3.MkBVLSHR(paddedRandomArg,paddedBitS)), 
                                        bitVal) 
                                        ))
                            cube // this is also a list of BitSelectors
                    else 
                        [])
                << List.zip3 
                    [0.. co.prismModel.Modules.Length - 1] 
                    (matchRandomVariablesToModules co randomVarsForThisStep co.prismModel.Modules)
                <| co.prismModel.Modules
        z3mkAnd co.z3 
        << List.collect oneCubeOneStep 
        << List.zip randomVars 
        <| [0..randomVars.Length-1]
        

    // Connects a concrete cube with the random variables
    let encodeConcreteCube (co:EncodingContext) (randomVars:Expr list list) (cube:ConcreteCube) : BoolExpr =         
        // The following computation is rather expensive and could be improved. It is quadratic in the number 
        // of steps and the number of modules. The resulting expression should not be too complex, though. 

        // This constraint requires that the randomVars accord to the values specified by the cube 
        let oneCubeOneStep (randomVarsForThisStep:Expr list, step:int) : BoolExpr list = 
            List.collect
                (fun (moduleCount:int, rvars:Expr option, m:PrismModule) -> 
                    if co.moduleInfos.Item(m.Name).localRandomVar_arg.IsSome // then we know that in this case also rvars.IsSome
                    then
                        let randomVar : BitVecExpr = downcast rvars.Value
                        List.collect 
                            (fun (bitSelector:ConcreteBitSelector,bitVal:BitVecNum) ->
                                let (paddedRandomArg:BitVecExpr,paddedBitS:BitVecExpr) = 
                                    if co.randomBVSize = co.positionBVSize // positionBVSize is log(randomBVSize) hence it is always lesser or equal
                                    then (randomVar, bitSelector.PosSelector :> BitVecExpr)
                                    else (randomVar,co.z3.MkConcat(co.z3.MkBV(0, co.randomBVSize - co.positionBVSize), bitSelector.PosSelector))

                                if bitSelector.StepSelector.Int = step && bitSelector.ModuleSelector.Int = moduleCount 
                                then 
                                    co.z3.MkEq(
                                        co.z3.MkExtract(0u, 0u, co.z3.MkBVLSHR(paddedRandomArg,paddedBitS)), 
                                        bitVal) :: []
                                else []
                                )
                            <| fst cube // this is also a list of BitSelectors
                    else 
                        [])
                << List.zip3 
                    [0.. co.prismModel.Modules.Length - 1] 
                    (matchRandomVariablesToModules co randomVarsForThisStep co.prismModel.Modules)
                <| co.prismModel.Modules
        z3mkAnd co.z3 << List.collect oneCubeOneStep << List.zip randomVars <| [0..randomVars.Length-1]


    let createBitSelector (co:EncodingContext) (bitIndex:int) : BitSelector * BoolExpr = 
        let stepDecl = co.z3.MkFreshConstDecl("stepSelector_" + bitIndex.ToString(), co.stepSort)
        co.declarations <- stepDecl :: co.declarations
        let modDecl = co.z3.MkFreshConstDecl("moduleSelector_" + bitIndex.ToString(), co.moduleNumberSort)
        co.declarations <- modDecl :: co.declarations
        let posDecl = co.z3.MkFreshConstDecl("posSelector_" + bitIndex.ToString(), co.positionSort)
        co.declarations <- posDecl :: co.declarations
        
        let bs = {
            StepSelector = downcast co.z3.MkConst(stepDecl)
            ModuleSelector = downcast co.z3.MkConst(modDecl)
            PosSelector = downcast co.z3.MkConst(posDecl)
            }

        // bounds on stepSelectors, moduleSelectors and bitSelectors
        let upperModuleBound = co.z3.MkBVULE(bs.ModuleSelector,co.moduleNumberSortMaxValue)
        let maxPosition : BitVecExpr = upcast co.z3.MkBV(co.randomBVSize-1u, co.positionBVSize)
        let upperPosBound = co.z3.MkBVULE(bs.PosSelector,maxPosition)

        // modules that have no random variable must not be selected:
        let moduleRestrictions : BoolExpr list = 
            List.collect 
                (fun (moduleCount:int,m:PrismModule) -> 
                    let moduleInfo = co.moduleInfos.Item m.Name 
                    if moduleInfo.localRandomVar_arg.IsNone
                    then [co.z3.MkNot (co.z3.MkEq(bs.ModuleSelector, co.z3.MkBV(moduleCount, co.moduleNumberBVSize)))]
                    else []
                    )
            << List.zip [0..co.prismModel.Modules.Length-1] 
            <| co.prismModel.Modules

        (bs, z3mkAnd co.z3 <| [upperModuleBound;upperPosBound] @ moduleRestrictions)


    let createCloseCE (co:EncodingContext) (bits:int) : CloseCounterExample * BoolExpr = 
        if bits=0 then ([],co.z3.MkTrue()) else
        let (cce : CloseCounterExample, bounds : BoolExpr list) = 
            List.unzip 
            << List.map (fun i -> createBitSelector co i) 
            <| [0..bits-1]

        // The bits must not be equal. 
        // To break the symmetry, we stregthen the inequality to the claim that bs(i)>bs(i+1).
        let inequalityConstraints : BoolExpr list =
            List.fold
                (fun (lastBitS:BitSelector, accum : BoolExpr list) (bitS:BitSelector) -> 
                    (bitS,
                        (downcast 
                            co.z3.MkITE(
                                co.z3.MkEq(bitS.StepSelector, lastBitS.StepSelector),
                                co.z3.MkITE(co.z3.MkEq(bitS.ModuleSelector, lastBitS.ModuleSelector),
                                    co.z3.MkBVUGT(bitS.PosSelector, lastBitS.PosSelector),
                                    co.z3.MkBVUGT(bitS.ModuleSelector, lastBitS.ModuleSelector)),
                                    co.z3.MkBVUGT(bitS.StepSelector, lastBitS.StepSelector)) 
                        :: accum)))
                (cce.Head, [])
                (cce.Tail)  |> snd

        (cce, z3mkAnd co.z3 (inequalityConstraints@bounds))


    let createBitVal (co:EncodingContext) (bitIndex:int) : BitVecExpr= 
        let bitValDecl = co.z3.MkFreshConstDecl("bitVal_" + bitIndex.ToString(), co.z3.MkBitVecSort(1u))
        co.declarations <- bitValDecl :: co.declarations
        downcast co.z3.MkConst(bitValDecl)
        


    let createCube (co:EncodingContext) (bits:int) : Cube * BoolExpr = 
        assert(bits>=1)
        let (cube : Cube, bounds : BoolExpr list) = 
            List.unzip 
            << List.map (fun i -> 
                let (bs,constraints) = createBitSelector co i
                ((bs, createBitVal co i),constraints)) 
            <| [0..bits-1]

        // The bits must not be equal. 
        // To break the symmetry, we stregthen the inequality to the claim that pos1>pos2.
        let inequalityConstraints : BoolExpr list =
            if bits> 1 then 
                List.fold
                    (fun ((lastBitS:BitSelector,bitVal:BitVecExpr), accum : BoolExpr list) (bitS:BitSelector,bitVal:BitVecExpr) -> 
                        ((bitS,bitVal),
                            (downcast 
                                co.z3.MkITE(
                                    co.z3.MkEq(bitS.StepSelector, lastBitS.StepSelector),
                                    co.z3.MkITE(co.z3.MkEq(bitS.ModuleSelector, lastBitS.ModuleSelector),
                                        co.z3.MkBVUGT(bitS.PosSelector, lastBitS.PosSelector),
                                        co.z3.MkBVUGT(bitS.ModuleSelector, lastBitS.ModuleSelector)),
                                        co.z3.MkBVUGT(bitS.StepSelector, lastBitS.StepSelector)) 
                            :: accum)))
                    (cube.Head, [])
                    (cube.Tail)  |> snd
            else 
                []

        (cube, z3mkAnd co.z3 (inequalityConstraints@bounds))


    let allCubePairs cubes : (Cube * Cube) list = // upper half of the matrix, excluding those on the middle line, efficiently generated
        fst 
        <| List.fold 
            (fun (pairs:(Cube * Cube) list,restBs:Cube list) (curB:Cube) -> 
                let tmp = List.map (fun (rB:Cube) -> (curB,rB)) restBs.Tail
                (tmp @ pairs,restBs.Tail)) 
            ([],cubes) 
            cubes
    
    let cubePairIsDisjoint (co:EncodingContext) ((cube1,cube2):Cube * Cube) : BoolExpr = 
        co.z3.MkOr(Array.ofList <| 
            List.collect
                (fun (b1:BitSelector,bitVal1) -> 
                    List.map (fun (b2:BitSelector,bitVal2) -> 
                        co.z3.MkAnd(Array.ofList
                            <| [co.z3.MkEq(b1.StepSelector,b2.StepSelector);
                                co.z3.MkEq(b1.ModuleSelector,b2.ModuleSelector);
                                co.z3.MkEq(b1.PosSelector,b2.PosSelector);
                                co.z3.MkNot(co.z3.MkEq(bitVal1,bitVal2))]
                            )
                        ) cube2) 
                cube1
            )
                // usage of cubePairIsDisjoint: 
                // co.solver.Assert(z3mkAnd co.z3 << List.map (fun (b1,b2) -> cubePairIsDisjoint co (b1,b2)) <| allCubePairs cubes)

    let excludeConcreteCubes (ac:AnalyzerContext) (ccs:ConcreteCube list) : BoolExpr = 
        // TODO: This method should be rewritten for efficiency: map over all random variables and check whether 
        // some of the concrete cubes refers to it ...
        let co = ac.co
        z3mkAnd co.z3 
        << List.map
            (fun (ccube:ConcreteCube) ->
                z3mkOr co.z3
                << List.map
                    (fun (bs:ConcreteBitSelector,bitVal:BitVecNum)->
                        if bs.StepSelector.Int>=ac.CurrentStepBound // || bs.PosSelector> // this will crash eventually. 
                        then co.z3.MkTrue() else
                        let minfos : ModuleInfo = co.moduleInfos.Item (co.moduleNumbersMapInverse.Item bs.ModuleSelector.Int)
                        let randomVar : BitVecExpr = downcast minfos.localRandomVars.Item bs.StepSelector.Int
                        co.z3.MkNot 
                          (co.z3.MkEq(
                            co.z3.MkExtract(uint32(bs.PosSelector.Int), uint32(bs.PosSelector.Int), randomVar), 
                            bitVal)) )
                <| fst ccube)
        <| ccs
                
    
    // Requires that the new cube is not equal to the existing cubes. 
    // Filters for cubes that equal in size to prevent enecoding the pidgeon hole problem. 
    // It is not a problem that the new cubes might be a subcube of existing cubes, since the path along which
    // the search is performed is not insie the existing cubes. 
    // It is okay that the new cube contains other cubes (which means they will be replaced during some clean-up later)
    let cubeIsNotEqualToOtherCubes (ac:AnalyzerContext) (cube:Cube) (cubeSize:int) (otherCubes:ConcreteCube list) : BoolExpr = 
        let z3 = ac.co.z3

        // Assumes that otherCube is equal in size
        let cubeIsNotEqualToOtherCube ((otherCube,len:int):ConcreteCube) : BoolExpr list = 
            if cubeSize=len 
            then
                [
                z3.MkNot 
                << z3mkAnd z3
                << List.collect
                    (fun ((bs:BitSelector,v:BitVecExpr),(cbs:ConcreteBitSelector,cv:BitVecNum)) -> 
                        [
                        z3.MkEq(bs.StepSelector,cbs.StepSelector) ;
                        z3.MkEq(bs.ModuleSelector,cbs.ModuleSelector) ;
                        z3.MkEq(bs.PosSelector,cbs.PosSelector) ;
                        z3.MkEq(v,cv) ;
                        ]
                        )
                << List.zip cube 
                <| otherCube
                ]
            else []

        z3mkAnd z3
        << List.collect cubeIsNotEqualToOtherCube
        <| otherCubes

    let cubeIsDisjointToOtherCubes (ac:AnalyzerContext) (cube:Cube) (otherCubes:ConcreteCube list) : BoolExpr = 
        let z3 = ac.co.z3
        z3mkAnd z3
        << List.map
            (fun (ccube:ConcreteCube) -> 
                z3mkOr z3 
                << List.collect
                    (fun (cbit:ConcreteBitSelector,cBitVal:BitVecNum) -> 
                        if cbit.StepSelector.Int>=ac.CurrentStepBound then [] else
                        List.map 
                            (fun (bitSel:BitSelector,bitVal:BitVecExpr) -> 
                                z3mkAnd z3 
                                    [
                                    z3.MkEq(bitSel.StepSelector,  cbit.StepSelector) ; 
                                    z3.MkEq(bitSel.ModuleSelector, cbit.ModuleSelector) ; 
                                    z3.MkEq(bitSel.PosSelector, cbit.PosSelector) ; 
                                    z3.MkNot(z3.MkEq(bitVal,cBitVal))
                                    ]
                            )
                            cube
                    )
                <| fst ccube)
        <| otherCubes


    let excludeIrrelevantBits (co:EncodingContext) (irrelevantBits: Set<int*int*int>) (bitSels:BitSelector list) : BoolExpr =
        z3mkAnd co.z3
        << List.collect
            (fun (bitSel:BitSelector) -> 
                List.map
                    (fun (stepSel:int,modSel:int,posSel:int) -> 
                        co.z3.MkNot
                        << z3mkAnd co.z3 
                        <| [co.z3.MkEq(bitSel.StepSelector,co.z3.MkBV(stepSel,co.stepBVSize)) ;
                            co.z3.MkEq(bitSel.ModuleSelector,co.z3.MkBV(modSel,co.moduleNumberBVSize)) ;
                            co.z3.MkEq(bitSel.PosSelector,co.z3.MkBV(posSel,co.positionBVSize))]
                        )
                << Set.toList 
                <| irrelevantBits)
        <| bitSels


    let rec extractCube (solver:Solver) (cube:Cube) : ConcreteCube = 
        match cube with
        | [] -> ([],0)
        | (bitSel:BitSelector,bitVal:BitVecExpr)::restCube -> 
            // alternative way to extract values: let valueExpr = co.solver.Model.ConstInterp(bitSel.BitVal) 
            let cc : ConcreteBitSelector = {
                StepSelector = downcast solver.Model.Eval(bitSel.StepSelector,true) 
                ModuleSelector = downcast solver.Model.Eval(bitSel.ModuleSelector,true)
                PosSelector = downcast solver.Model.Eval(bitSel.PosSelector,true)
                }
            let valueExpr : BitVecNum = downcast solver.Model.Eval(bitVal,true)
            let (bsList,len) = extractCube solver restCube
            ((cc,valueExpr) :: bsList,len+1)

