(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.GraphGen

open System.ComponentModel.Composition
open System.IO
open System.Text
open SpecializedCollections
open Graph
open Ast
open Compile

// TODO : Move these into a separate assembly to avoid loading System.Xml.dll unless necessary.

// TODO : Implement back-ends which generate graph output, e.g., for debugging and presentation.
// DGML (for Visual Studio)
// dot (for graphviz)

[<RequireQualifiedAccess>]
module Dgml =
    open System.Xml
    open LanguagePrimitives

    //
    let inline private dfaStateUniqueNodeId (ruleId : RuleIdentifier) (dfaStateId : DfaStateId) =
        sprintf "%s_State_%i" ruleId (int dfaStateId)

    /// Escapes control characters.
    // NOTE : The backslash must be double-escaped so it is handled
    // correctly in the generated DGML file.
    let private escapedChar = function
        | '\u0000' -> "\\0x00"
        | '\u0001' -> "SOH"
        | '\u0002' -> "STX"
        | '\u0003' -> "ETX"
        | '\u0004' -> "EOT"
        | '\u0005' -> "ENQ"
        | '\u0006' -> "ACK"
        | '\u0007' -> "\\a"
        | '\u0008' -> "\\b"
        | '\u0009' -> "\\t"
        | '\u000a' -> "\\n"
        | '\u000b' -> "VT"
        | '\u000c' -> "\\f"
        | '\u000d' -> "\\r"
        | '\u000e' -> "SO"
        | '\u000f' -> "SI"
        | '\u0010' -> ""
        | '\u0011' -> ""
        | '\u0012' -> ""
        | '\u0013' -> ""
        | '\u0014' -> ""
        | '\u0015' -> ""
        | '\u0016' -> ""
        | '\u0017' -> ""
        | '\u0018' -> ""
        | '\u0019' -> ""
        | '\u001a' -> ""
        | '\u001b' -> ""
        | '\u001c' -> ""
        | '\u001d' -> ""
        | '\u001e' -> ""
        | '\u001f' -> ""
        | c ->
            if int c < 0x20 || int c = 0x7f then
                sprintf "\\0x%02x" (int c)
            else
                c.ToString ()


//    // Emits DGML where each DFA is a separate component of the graph.
//    let emitCombined (compiledSpec : CompiledSpecification) (options : CompilationOptions) =
//        //
//        let dgmlDoc = XmlDocument ()
//        let xmlDecl = dgmlDoc.CreateXmlDeclaration ("1.0", "utf-8", null)
//        
//        let directedGraphNode =
//            dgmlDoc.CreateElement ("DirectedGraph", "http://schemas.microsoft.com/vs/2009/dgml")
//            |> dgmlDoc.AppendChild
//
//        let nodes =
//            dgmlDoc.CreateElement "Nodes"
//            |> directedGraphNode.AppendChild
//
//        let links =
//            dgmlDoc.CreateElement "Links"
//            |> directedGraphNode.AppendChild
//
//        // Add the rules/states/transitions to the graph
//        (0, compiledSpec.CompiledRules)
//        ||> Map.fold (fun ruleStartDfaStateId ruleId compiledRule ->
//            //
//            let dfaStateCount = compiledRule.Dfa.Transitions.VertexCount
//
//            // Add the nodes for this rule's DFA.
//            for dfaStateId = 0 to dfaStateCount - 1 do
//                let dfaStateId = Int32WithMeasure dfaStateId
//
//                /// The Node element representing this DFA state.
//                let vertexNode =
//                    dgmlDoc.CreateElement "Node"
//                    |> nodes.AppendChild
//
//                // Set the Id attribute value.
//                // This isn't shown on the graph, it's only used as a unique identifier for the node.
//                let idAttr = dgmlDoc.CreateAttribute "Id"
//                vertexNode.Attributes.Append idAttr |> ignore
//                idAttr.Value <- dfaStateUniqueNodeId ruleId dfaStateId
//                
//                // Set the Label attribute value.
//                // This is the label shown for this node when the graph is rendered.
//                let labelAttr = dgmlDoc.CreateAttribute "Label"
//                vertexNode.Attributes.Append labelAttr |> ignore
//                labelAttr.Value <- string dfaStateId
//
//                // Set the Category attribute value.
//                // We use this to group the nodes from each DFA together.
//                let categoryAttr = dgmlDoc.CreateAttribute "Category"
//                vertexNode.Attributes.Append categoryAttr |> ignore
//                categoryAttr.Value <- ruleId
//
//            // Add the transitions for this rule's DFA.
//            compiledRule.Dfa.Transitions.AdjacencyMap
//            |> Map.iter (fun edgeKey edgeSet ->
//                
//
//
//                ())
//
//            // 
//            ruleStartDfaStateId + dfaStateCount)
//        |> ignore
//
//        // TEMP : Normally we'll write this directly to a file, but for testing
//        // purposes write the document to a StringBuilder.
//        let sb = StringBuilder ()
//        using (new StringWriter (sb)) dgmlDoc.Save        
//        sb.ToString ()

    // Emits DGML where each DFA is a separate component of the graph.
    let emitSeparate (compiledSpec : CompiledSpecification) (options : CompilationOptions) =
        //
        let dgmlDoc = XmlDocument ()
        let xmlDecl = dgmlDoc.CreateXmlDeclaration ("1.0", "utf-8", null)
        
        let directedGraph =
            dgmlDoc.CreateElement ("DirectedGraph", "http://schemas.microsoft.com/vs/2009/dgml")
            |> dgmlDoc.AppendChild

        let nodes =
            dgmlDoc.CreateElement ("Nodes", directedGraph.NamespaceURI)
            |> directedGraph.AppendChild

        let links =
            dgmlDoc.CreateElement ("Links", directedGraph.NamespaceURI)
            |> directedGraph.AppendChild

        let categories =
            dgmlDoc.CreateElement ("Categories", directedGraph.NamespaceURI)
            |> directedGraph.AppendChild

        // Add the rules/states/transitions to the graph
        compiledSpec.CompiledRules
        |> Map.iter (fun ruleId compiledRule ->
            // Add a category for this rule.
            let ruleCategory =
                dgmlDoc.CreateElement ("Category", directedGraph.NamespaceURI)
                |> categories.AppendChild

            // Set the Id attribute value.
            // This isn't shown on the graph, it's only used as a unique identifier for the node.
            let idAttr = dgmlDoc.CreateAttribute "Id"
            ruleCategory.Attributes.Append idAttr |> ignore
            idAttr.Value <- ruleId

            // Add the nodes for this rule's DFA.
            let dfaStateCount = compiledRule.Dfa.Transitions.VertexCount
            for dfaStateId = 0 to dfaStateCount - 1 do
                let dfaStateId = Int32WithMeasure dfaStateId

                /// The Node element representing this DFA state.
                let dfaStateNode =
                    dgmlDoc.CreateElement ("Node", directedGraph.NamespaceURI)
                    |> nodes.AppendChild

                // Set the Id attribute value.
                // This isn't shown on the graph, it's only used as a unique identifier for the node.
                let idAttr = dgmlDoc.CreateAttribute "Id"
                dfaStateNode.Attributes.Append idAttr |> ignore
                idAttr.Value <- dfaStateUniqueNodeId ruleId dfaStateId
                
                // Set the Label attribute value.
                // This is the label shown for this node when the graph is rendered.
                let labelAttr = dgmlDoc.CreateAttribute "Label"
                dfaStateNode.Attributes.Append labelAttr |> ignore
                labelAttr.Value <- string dfaStateId

                // Set the Category attribute value.
                // We use this to group the nodes from each DFA together.
                let categoryAttr = dgmlDoc.CreateAttribute "Category"
                dfaStateNode.Attributes.Append categoryAttr |> ignore
                categoryAttr.Value <- ruleId

            // Add the transitions for this rule's DFA.
            compiledRule.Dfa.Transitions.AdjacencyMap
            |> Map.iter (fun edgeKey edgeSet ->
                /// The Link element representing this transition edge.
                let transitionEdgeLink =
                    dgmlDoc.CreateElement ("Link", directedGraph.NamespaceURI)
                    |> links.AppendChild

                // Set the Source attribute value to the identifier for the source DFA state.
                let sourceAttr = dgmlDoc.CreateAttribute "Source"
                transitionEdgeLink.Attributes.Append sourceAttr |> ignore
                sourceAttr.Value <- dfaStateUniqueNodeId ruleId edgeKey.Source

                // Set the Target attribute value to the identifier for the target DFA state.
                let targetAttr = dgmlDoc.CreateAttribute "Target"
                transitionEdgeLink.Attributes.Append targetAttr |> ignore
                targetAttr.Value <- dfaStateUniqueNodeId ruleId edgeKey.Target

                // Set the Label attribute value.
                // This is the label shown for this edge when the graph is rendered.
                let labelAttr = dgmlDoc.CreateAttribute "Label"
                transitionEdgeLink.Attributes.Append labelAttr |> ignore
                labelAttr.Value <-
                    // Create a label for this edge, based on the intervals in the character set.
                    if CharSet.isEmpty edgeSet then
                        failwith "Empty edge set."
                    elif CharSet.intervalCount edgeSet = 1 then
                        let minElement = CharSet.minElement edgeSet
                        let maxElement = CharSet.maxElement edgeSet

                        if minElement = maxElement then
                            // Single element in the set.
                            escapedChar minElement
                        else
                            sprintf "%s-%s" (escapedChar minElement) (escapedChar maxElement)
                    else
                        // OPTIMIZE : If this represents a negated set, it could have a LOT of
                        // characters -- it would be better to represent negated sets using the
                        // usual negated character set notation, e.g., [^abc]
                        let sb = StringBuilder ()
                        edgeSet
                        |> CharSet.iterIntervals (fun lowerBound upperBound ->
                            if lowerBound = upperBound then
                                sb.Append (escapedChar lowerBound) |> ignore
                            else
                                sb.Append (escapedChar lowerBound) |> ignore
                                sb.Append "-" |> ignore
                                sb.Append (escapedChar upperBound) |> ignore

                            sb.Append "," |> ignore)
                        // Remove the trailing "," before returning.
                        sb.Length <- sb.Length - 1
                        sb.ToString ()
                ))

        // Write the document to a file.
        // TEMP : This is a hard-coded filename -- we should determine this from
        // the compiler options. Perhaps take the specified output filename and
        // change the extension to .dgml.
        dgmlDoc.Save "CompiledLexerDfa.dgml"

//        let sb = StringBuilder ()
//        using (new StringWriter (sb)) dgmlDoc.Save
//        sb.ToString ()


