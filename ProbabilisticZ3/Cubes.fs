
namespace ProbabilisticZ3

open System // for Conversions of basic data types
open Utils
open Microsoft.Z3

module Cubes =

    type ConcreteBitSelector = 
        {
        StepSelector : BitVecNum
        ModuleSelector : BitVecNum
        PosSelector: BitVecNum
        }
    // (Position and val list) * length
    type ConcreteCube = (ConcreteBitSelector * BitVecNum) list * int 

    type BitSelector = 
        {
        StepSelector : BitVecExpr 
        ModuleSelector : BitVecExpr 
        PosSelector: BitVecExpr  
        }
    type Cube = (BitSelector * BitVecExpr) list 
    


    let printConcreteCube_bitSelectorOnly (ccube:ConcreteCube) : String = 
        let sl : String list= 
            List.map 
                (fun (bitSel:ConcreteBitSelector,_) ->
                        (bitSel.StepSelector,bitSel.ModuleSelector,bitSel.PosSelector).ToString()
                    )
            <| fst ccube
        String.concat "." sl
        
    let printConcreteCube (ccube:ConcreteCube) : String = 
        let sl : String list= 
            List.map 
                (fun (bitSel:ConcreteBitSelector,v:BitVecNum) ->
                        ((bitSel.StepSelector,bitSel.ModuleSelector,bitSel.PosSelector),v.Int).ToString()
                    )
            <| fst ccube
        String.concat "." sl

    let cbsToString (bitSel:ConcreteBitSelector) : String =
        (bitSel.StepSelector,bitSel.ModuleSelector,bitSel.PosSelector).ToString()


    ////////////////////////////////////////
    // Tools to enable overlapping cubes. //
    ////////////////////////////////////////
    type ORD = GT | EQ | LT 
    let comp (cb:ConcreteBitSelector) (cb':ConcreteBitSelector) : ORD =
        match compare cb.StepSelector.Int cb'.StepSelector.Int with
        | 0 -> 
            match compare cb.ModuleSelector.Int cb'.ModuleSelector.Int with
            | 0 -> 
                match compare cb.PosSelector.Int cb'.PosSelector.Int with
                | 0 -> EQ
                | -1 -> LT
                | 1 -> GT
                | _ -> raise (InnerError "Unexpected result of a comparison.")
            | -1 -> LT
            | 1 -> GT
            | _ -> raise (InnerError "Unexpected result of a comparison.")
        | -1 -> LT
        | 1 -> GT
        | _ -> raise (InnerError "Unexpected result of a comparison.")

    // Compares two concrete cubes and returns those BitSelectors that 
    // occur in the other cube, but not in the new cube. 
    // These are the positions by which we have to split the new cube. 
    // If a position is detected at which the two cubes contradict each other, None is returned. 
    let rec stripMatchingBSs 
            ((newCC,lenNew):ConcreteCube) 
            ((otherCC,lenOther):ConcreteCube) 
            : ((ConcreteBitSelector * BitVecNum) list * int) option = 
        match (newCC, otherCC) with
        | (newBS::newCCr,otherBS::otherCCr) ->
            match comp (fst newBS) (fst otherBS) with
            | EQ -> 
                match (snd newBS).Int = (snd otherBS).Int with 
                | true  -> stripMatchingBSs (newCCr,lenNew-1) (otherCCr,lenOther-1) // cubes match in this position
                | false -> None // cubes are disjoint
            | LT -> 
                stripMatchingBSs (newCCr,lenNew-1) (otherCC,lenOther) // skip newBS
            | GT -> 
                match stripMatchingBSs (newCC,lenNew) (otherCCr,lenOther-1) with // skip otherBS 
                | Some (cube,len) -> 
                    Some (otherBS::cube,len+1)
                | None -> None
        | (_,[]) -> 
            Some ([], 0)
        | ([],other) -> 
            Some (other,lenOther)

    // Inserts all elements of the first list into the second ... in order. 
    let rec insertAll cc1 cc2 : (ConcreteBitSelector* 'b) list = 
        match (cc1,cc2) with 
        | ((bs1,v1)::cc1r,(bs2,v2)::cc2r) -> 
            match comp bs1 bs2 with
            | LT -> (bs1,v1) :: insertAll cc1r cc2 
            | EQ -> raise (InnerError "Equal positions should have been filtered already.")
            | GT -> (bs2,v2) :: insertAll cc1 cc2r
        | ([],cc2) -> cc2
        | (cc1,[]) -> cc1

    let rec splitBy (z3:Context) 
            (toSplit:(ConcreteBitSelector*BitVecNum) list, len:int) 
            (splitPositions:(ConcreteBitSelector*BitVecNum) list, lenPos:int) : ConcreteCube list = 
        match splitPositions with
        | [] -> []
        | (fstSplitPos::splitPositionsR) -> 
            // Flip the first bitval, then interleave the additional positons wit newCC. 
            // Finally, recurse without the first bit of splitPositions
            let additionalBits = 
                (fst fstSplitPos,
                    let asdf = z3.MkBVNot(snd fstSplitPos)
                    downcast asdf.Simplify()) ::splitPositionsR
            (insertAll additionalBits toSplit, len+lenPos) :: splitBy z3 (toSplit,len) (splitPositionsR,lenPos-1)


    let splitByNonMatchingBSs (z3:Context) (newCC:ConcreteCube) (otherCC:ConcreteCube) : ConcreteCube list = 
        match stripMatchingBSs newCC otherCC with
        | None -> // Cubes are disjoint
            [newCC]
        | Some ([],0) -> 
            // Cubes are not disjoint and otherCC has no positions that newCC doesn't. 
            //That means newCC is contained in otherCC. 
            []
        | Some (_,0) | Some ([],_) -> 
            raise (InnerError "Length value does not agree with length of the list.") 
        | Some (splitPositions,lenPos) -> 
            splitBy z3 newCC (splitPositions,lenPos)

    // Note: When is otherCC subsumed? If it fixes more positions than newCC. We do not 
    // clean up at the moment, but we should sort the cubes by size (decreasing) to avoid unnecessary splits. 


    // Given the length of a cube, it computes the volume. 
    let volume (cubeSize: int) : double = 
        2.0**( - Convert.ToDouble(cubeSize))

    let rec insert (y,leny:int) xs = 
        match xs with 
        | (x,lenx)::xr -> 
            if leny <= lenx
            then (x,lenx)::(y,leny)::xr
            else (x,lenx)::insert (y,leny) xr
        | [] -> [(y,leny)]

    // Computes the volume that newCC contributes to the union of newCC and otherCCs. 
    // Returns an updated list of concrete cubes. The new cube is added in the right position (maintaining decreasing ordering). 
    let rec additionalVolume (z3:Context) (newCC:ConcreteCube) (otherCCs:ConcreteCube list) : double*ConcreteCube list =  

        // debug assertion:
        let newCCseq= List.toSeq << fst <| newCC
        let result = Seq.forall (fun (x,y) -> not <| GT.Equals (compare x y)) << Seq.pairwise <| newCCseq
        assert(result)

//        let mutable vols : double list = []
        let mutable vol : double = 0.0
        let mutable worklist = [(newCC,otherCCs)]
        let mutable finished : bool = false
        while not finished do 
            match worklist with
            | ((cc, len), occ::occr)::worklistRest -> 
                let splitted = splitByNonMatchingBSs z3 (cc, len) occ
                // nonOverlappingCubes otherCCs (splitted @ newCCsRest) 
                worklist <- List.map (fun (cc, len) -> ((cc, len), occr)) splitted  @ worklistRest
            | ((cc,len),[])::worklistRest -> 
                vol <- vol + volume len // TODO: check if addition is stable (within a couple of orders of magnitude). If not, then open a new collector. In the end, sort the collectors and try to add up again. 
                worklist <- worklistRest
            | [] -> 
                finished <- true

        if vol>0.0 then
            (vol, insert newCC otherCCs)
        else 
            (vol, otherCCs)

