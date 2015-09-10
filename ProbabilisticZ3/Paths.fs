// MN Rabe


namespace ProbabilisticZ3

open System
open Microsoft.Z3
open Utils
open Results
open Problems
open Cubes
open CounterExamples
open EncodingContext
open PrismModel

module Paths =

    type RVar = NonProbModule | NonProbTransition | Prob of BitVecNum
    type RStep = RVar list // random decisions of one step, ordered to match modules
    type SysVar = BV of BitVecNum | B of BoolExpr 
    type SysState = SysVar list // sequence of system states
    type Path = (SysState*RStep) list
    type RPath = RStep list
    