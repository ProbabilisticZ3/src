// CM Wintersteiger, M Rabe

namespace ProbabilisticZ3

module Results = 
    type Result =   HOLDS // property holds
                  | VIOLATED // prroperty doesn't hold
                  | UNKNOWN
                  | ERROR

    let printResult result : string = 
        match result with
          HOLDS     -> "HOLDS"
        | VIOLATED  -> "VIOLATED"
        | UNKNOWN   -> "UNKNOWN"
        | ERROR     -> "ERROR"