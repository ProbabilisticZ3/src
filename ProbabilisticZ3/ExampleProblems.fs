// CM Wintersteiger, MN Rabe

namespace ProbabilisticZ3

open Problems
open Results
open Expressions
open System

module ExampleProblems =

    let syncTests = 
        [{defaultProblem with 
            FilePath = "../../../debugmodels/synctest.pm"
            RunName = Some "SyncTest1"
            ProbabilityBound = Some (0.25,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 2
            GoalRegion = Positive "fin"
        };
        {defaultProblem with 
            FilePath = "../../../debugmodels/synctest.pm"
            RunName = Some "SyncTest2"
            ProbabilityBound = Some (0.25,COMP_GE)
            ExpectedResult = Some VIOLATED
            Timeout = 5000
            GlobalStepBound = 1
            GoalRegion = Positive "fin"
        };
        {defaultProblem with 
            FilePath = "../../../debugmodels/synctestRenaming.pm"
            RunName = Some "SyncTest3"
            ProbabilityBound = Some (0.25,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 2
            GoalRegion = Positive "fin"
        };
        {defaultProblem with 
            FilePath = "../../../debugmodels/synctestRenaming.pm"
            RunName = Some "SyncTest4"
            ProbabilityBound = Some (0.25,COMP_GE)
            ExpectedResult = Some VIOLATED
            Timeout = 5000
            GlobalStepBound = 1
            GoalRegion = Positive "fin"
        };]
    
    let testSequenceForCorrectness = 
        [{defaultProblem with
            FilePath = "../../../debugmodels/test0.pm"
            RunName = Some "BasicTest1"
            ProbabilityBound = Some (0.0,COMP_GT)
            ExpectedResult = Some VIOLATED
            Timeout = 5000
            GlobalStepBound = 2
            GoalRegion = Empty // Positive "elected"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test1.pm"
            RunName = Some "BasicTest2"
            ProbabilityBound = Some (0.0,COMP_GT)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 3
            GoalRegion = Positive "testlabel"
        } ;

        {defaultProblem with
            FilePath = "../../../debugmodels/test1.pm"
            RunName = Some "BasicTest3"
            ProbabilityBound = Some (0.1,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 3
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test1.pm"
            RunName = Some "BasicTest4"
            ProbabilityBound = Some (0.9,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 3
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test1.pm"
            RunName = Some "BasicTest5"
            ProbabilityBound = Some (1.0,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 3
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test5.pm"
            RunName = Some "BasicTest6"
            ProbabilityBound = Some (0.0,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 5000
            GlobalStepBound = 1
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test5.pm"
            RunName = Some "BasicTest7"
            ProbabilityBound = Some (0.3,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 10000
            GlobalStepBound = 1
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test5.pm"
            RunName = Some "BasicTest8"
            ProbabilityBound = Some (0.8,COMP_GE)
            ExpectedResult = Some VIOLATED
            Timeout = 10000
            GlobalStepBound = 1
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test5.pm"
            RunName = Some "BasicTest9"
            ProbabilityBound = Some (0.5,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 10000
            GlobalStepBound = 2
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/test5.pm"
            RunName = Some "BasicTest10"
            ProbabilityBound = Some (0.8,COMP_GE)
            ExpectedResult = Some VIOLATED
            Timeout = 10000
            GlobalStepBound = 2
            GoalRegion = Positive "testlabel"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/formula0.pm"
            RunName = Some "FormulaTest1"
            ProbabilityBound = Some (1.0,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 10000
            GlobalStepBound = 3
            GoalRegion = Positive "threesteps"
        } ;
        
        {defaultProblem with
            FilePath = "../../../debugmodels/formula0.pm"
            RunName = Some "FormulaTest2"
            ProbabilityBound = Some (1.0,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 10000
            GlobalStepBound = 2
            GoalRegion = Positive "twosteps"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/formula0.pm"
            RunName = Some "FormulaTest3"
            ProbabilityBound = Some (1.0,COMP_GE)
            ExpectedResult = Some HOLDS
            Timeout = 10000
            GlobalStepBound = 3
            GoalRegion = Positive "twosteps"
        } ;
        {defaultProblem with
            FilePath = "../../../debugmodels/formula1.pm"
            RunName = Some "FormulaTest4"
            ProbabilityBound = Some (0.0,COMP_GT)
            ExpectedResult = Some HOLDS
            Timeout = 10000
            GlobalStepBound = 3
            GoalRegion = Positive "twosteps"
        } ;
        ]

    let leader_precision (prec:int) (steps:int) (n:int) (k:int) (p:double) = 
        {defaultProblem with
            FilePath = "../../../prismmodels/dtmcs/leader_sync/leader_sync" + n.ToString() + "_" + k.ToString() + ".pm"
            RunName = Some <| "Leader Election N=" + n.ToString() + ", K=" + k.ToString()
            ProbabilityBound = Some (p,COMP_GE)
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = 7
            fractionsEncoding = prec
            GoalRegion = Positive "elected"
        } ;

    let leader (steps:int) (n:int) (k:int) (p:double) = 
        let r = log (Convert.ToDouble(k)) / log 2.0
        let fE = Convert.ToInt32 (ceil <| r) //if k=2 then 1 elif k=4 then 2 elif k=8 then 3 elif
        {defaultProblem with
            FilePath = "../../../prismmodels/dtmcs/leader_sync/leader_sync" + n.ToString() + "_" + k.ToString() + ".pm"
            RunName = Some <| "Leader Election N=" + n.ToString() + ", K=" + k.ToString()
            ProbabilityBound = Some (p,COMP_GE)
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = 8
            fractionsEncoding = fE
            GoalRegion = Positive "elected"
        } ;


    let crowds (steps:int) (tRuns:int) (crowdsize:int) (bound) : Problem = 
        {defaultProblem with
            FilePath = "../../../prismmodels/dtmcs/crowds/crowds.pm"
            RunName = Some <| "Crowds " + tRuns.ToString() + "," + crowdsize.ToString()
            Constants = [createIntConstant("TotalRuns",I tRuns) ; createIntConstant("CrowdSize",I crowdsize)]
            ProbabilityBound = Some (bound,COMP_GE) //was 0.005
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = 8 ;
            fractionsEncoding = 9
            GoalRegion = Positive "PCTL"
        } 
        
    let crowds_big (steps:int) (tRuns:int) (crowdsize:int) (bound) : Problem = 
        {crowds steps tRuns crowdsize bound with FilePath = "../../../prismmodels/dtmcs/crowds/crowds_big.pm";intEncoding = 9} 

    let brp (steps:int) (ints:int) (n:int) (max:int) (bound) : Problem = 
        {defaultProblem with
            RunName = Some ("Bounded Retransmission Protocol N=" + n.ToString() + " MAX=" + max.ToString())
            Constants = [createIntConstant("N",I n) ; createIntConstant("MAX",I max)] 
            FilePath = "../../../prismmodels/dtmcs/brp/brp.pm"
            ProbabilityBound = Some (bound,COMP_GE)
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = ints 
            fractionsEncoding = 8
            GoalRegion = Positive "p1"
            Timeout = 1000000
        }
    let brp16_2 = brp 20 6 16 2 0.000000001
        
    let brp32_4 = brp 20 7 32 4 0.000000001

    let brp64_5 = brp 20 64 8 5 0.00000000001

    let nand (steps:int) (n:int) (k:int) p : Problem = 
        {defaultProblem with
//            FilePath = "../../../prismmodels/dtmcs/nand/nand_flat.pm"
            FilePath = "../../../prismmodels/dtmcs/nand/nand.pm"
            RunName = Some ("NAND N=" + n.ToString() + " K=" + k.ToString() + ", p=" + p.ToString())
            Constants = [createIntConstant("N",I n) ; createIntConstant("K",I k)] 
            ProbabilityBound = Some (p,COMP_GE)
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = 15
            fractionsEncoding = 8
            GoalRegion = Positive "lessThan10PercentAreErroneous"
        }

    let egl (n:int)(l:int)(steps:int)(p:double) : Problem = 
        {defaultProblem with
            RunName = Some <| "EGL N=" + n.ToString() + " L=" + l.ToString()
            Constants = [createIntConstant("N",I n) ; createIntConstant("L",I l)] 
            FilePath = "../../../prismmodels/dtmcs/egl/egl.pm"
            ProbabilityBound = Some (p,COMP_GE)
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = 6 ;
            fractionsEncoding = 1
            GoalRegion = Positive "unfairA"
        }
    let egl5_2 = egl 5 2 31 0.4 
        
    let egl10_4 = egl 10 4 50 0.00001

    let egl20_8 = egl 20 8 50 0.00001

    let herman (steps:int) (n:int) (p:double) : Problem = 
        {defaultProblem with
            RunName = Some <| "Herman N=" + n.ToString()
            FilePath = "../../../prismmodels/dtmcs/herman/herman" + n.ToString() + ".pm"
            ProbabilityBound = Some (p,COMP_GT) //(0.2,COMP_GE)
            ExpectedResult = Some HOLDS
            GlobalStepBound = steps
            intEncoding = 6 ;
            fractionsEncoding = 1
            GoalRegion = Positive "stable"
        }
    

