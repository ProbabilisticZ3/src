#Probabilistic Z3
Copyright (C) 2014 Microsoft Research

Probabilistic Z3 is a solver for the bounded reachability problem that uses the
symbolic approximation technique described in: Markus N. Rabe, Christoph
M. Wintersteiger, Hillel Kugler, Boyan Yordanov, and Youssef Hamadi: "Symbolic
Approximation of the Bounded Reachability Probability in Large Markov Chains",
QEST, LNCS vol. 8657, Springer, 2014.

#Requirements: 
 - Windows
 - Visual Studio 2013
 - [F#](http://fsharp.org)
 - [Irony](http://irony.codeplex.com)
 - [Z3](http://z3.codeplex.com)

The references to Irony are resolved via NuGet packages that are installed 
automatically. The reference to Z3 needs to be updated to point to a local 
copy of Microsoft.Z3.dll and the (native) libz3.dll needs to be in the path
at runtime. 
