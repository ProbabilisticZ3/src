
namespace ProbabilisticZ3

open System
open System.Diagnostics
open PrismParser
open Irony.Parsing
open Debug
open Microsoft.Z3
//
//open Microsoft.Msagl
//open System.Drawing

module Visualizer =

    //let listRandomChoices (x::xr : ) : (string*Expr) list = 

    // this drawing method is designed specifically for the structured variable encoding
//    let draw (co:Z3Context) (model:Model) : unit =
////        let graph = new Microsoft.Msagl.Drawing.Graph("")
//        
//        //let asdf1 : Expr = co.Sol.Model.Eval(co.Z3.MkTrue(),true)
//        //let asdf3 = co.Z3.MkNot(co.Z3.MkEq(bv,co.Z3.MkBV(co.Sol.Model.Eval(bv,true).ToString(),23u)))
//        //let asdf2 = co.Sol.Model.Eval(f[co.Z3.MkBV(0,3)],true)
//        
//        // get initial state
//        let initVals : Expr list = 
//            List.map 
//                (fun v -> 
//                    let e0 : Expr = model.Eval(applyAnyVarStep co v 0, true)
//                    //let e1 : Expr = model.Eval(applyAnyVarStep co v 1, true)
//                    e0)
//                co.PrismModel.Vars
//        
//        let functions =  (List.ofArray model.FuncDecls)
//        let constants = List.ofArray model.ConstDecls
//
//
//        ///////////////////// Debug printouts:
//
//        printf "\nThe numbers of globalChoices are resolved as follows:\n"
//        Map.iter
//            (fun (key:String) number -> 
//                printf " SyncWord %A has number %d \n" key number
//            )
//            co.DebugInfo.SyncActionNumbersMap
//            
//
//        report_0 2 "\nThe evaluation of all constants:\n"
//        for c in constants do
//            report_3 2 "   %A  %A...  %A\n" c.Name  (String.Concat (List.replicate (32-String.length (c.Name.ToString())) " ")) ((model.Eval(model.ConstInterp(c),true)).ToString())
//
//        //let init = graph.AddNode("init")
//        //graph.FindNode("init").Attr.FillColor <- Drawing.Color.Red
//
//
//
//        let interps (step:int) = 
//            List.map
//                (fun (v:Variable) ->  model.FuncInterp(co.VariableDeclarations.Item(v.Name + "_Step_" + step.ToString())))
//                co.prismModel.Vars
//        let allInterps = 
//            List.map
//                (fun i -> interps i)
//                [1..co.config.StepBound]
//        printf "\n\nThereafter, the functions look like this:\n"
//        for step in [1..co.Config.StepBound] do
//            printf "Step %d\n" step
//            for (v,interp:FuncInterp) in List.zip co.PrismModel.Variables (interps step) do
//                printf "  %A  %A\n" v.Name (interp.ToString())


//        let renderer = new GraphViewerGdi.GraphRenderer(graph)
//        renderer.CalculateLayout()
//        let width : int = 1400 // pixels
//        let bitMap : Bitmap = new Bitmap(width, Convert.ToInt32( graph.Height * (Convert.ToDouble(width) / graph.Width)))
//        renderer.Render(bitMap)
//        bitMap.Save("../../../asdf.png")

        ()

//    let drawExample () =
//        let graph = new Microsoft.Msagl.Drawing.Graph("")
//
//        let edge = graph.AddEdge("node1","node2")
//        edge.LabelText <- "lalala"
//        graph.FindNode("node1").Attr.FillColor <- Drawing.Color.Red
//
//        let renderer = new GraphViewerGdi.GraphRenderer(graph)
//        renderer.CalculateLayout()
//
//        let width : int = 1400 // pixels
//
//        let bitMap : Bitmap = new Bitmap(width, Convert.ToInt32( graph.Height * (Convert.ToDouble(width) / graph.Width)))
//
//        renderer.Render(bitMap)
//        bitMap.Save("../../../asdf.png")




