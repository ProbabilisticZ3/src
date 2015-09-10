// MN Rabe

namespace ProbabilisticZ3

open System
open System.Diagnostics

module Statistics = 

    type Statistics = {
        /// <summary> </summary>
        mutable Stopwatch : Stopwatch
        /// <summary> Number of calls to Z3. </summary>
        mutable QueriesCount : int
        /// <summary> Time spent on translating the model into internal data structures in seconds </summary>
        mutable EncodingTime : float
        /// <summary> Time spent on searching close counter-examples in seconds </summary>
        mutable CCEsSearchTime : float
        /// <summary> Time spent on searching cube candidates in seconds </summary>
        mutable CubeCandateSearchTime : float
        /// <summary> Time spent on searching checking cube candidates for correctness in seconds </summary>
        mutable CubeCheckSearchTime : float
        /// <summary> Time spent on searching example paths in seconds </summary>
        mutable PathSearchTime : float
        /// <summary> Time spent on simplifying the bounded model checking formulas for multiple uses (formula baking). </summary>
        mutable SimplifyTime : float
        }

    let freshStatisticsObject = {
        Stopwatch = Stopwatch.StartNew()
        QueriesCount = 0
        EncodingTime = 0.0
        CCEsSearchTime = 0.0
        CubeCandateSearchTime = 0.0
        CubeCheckSearchTime = 0.0
        PathSearchTime = 0.0
        SimplifyTime = 0.0
        }


    let printStatistics (st:Statistics) : string = 
        st.Stopwatch.Stop()
        let result = 
            "Total time: " + st.Stopwatch.Elapsed.ToString() + "\n\r  " +
            "Calls to Z3: " + st.QueriesCount.ToString() + "\n\r  " +
            "Time spent on encodings: " + st.EncodingTime.ToString() + "s\n\r  " +
            "Time spent on CCEs: " + st.CCEsSearchTime.ToString() + "s\n\r  " +
            "Time spent on searching cube candidates: " + st.CubeCandateSearchTime.ToString() + "s\n\r  " +
            "Time spent on checking cube candidates: " + st.CubeCheckSearchTime.ToString() + "s\n\r  " +
            "Time spent on searching paths: " + st.PathSearchTime.ToString() + "s\n\r  " +
            "Time spent on simplifying formulas: " + st.SimplifyTime.ToString() + "s\n\r  " 
        st.Stopwatch.Start()
        result
