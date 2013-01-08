(*
Copyright (c) 2012-2013, Jack Pappas
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
// TODO : Implement a backend for the dot (graphviz) format.

/// Functions for generating color palettes.
// Reference : http://martin.ankerl.com/2009/12/09/how-to-create-random-colors-programmatically/
[<RequireQualifiedAccess>]
module private Palette =
    open System.Drawing

    /// The conjugate of the golden ratio.
    let private phi_conj = ((1.0 + sqrt 5.0) / 2.0) - 1.0

    //
    let private colorFromHSV (hue : float, saturation : float, brightness : float) : Color =
        // Preconditions
        if hue < 0.0 || hue > 360.0 then
            invalidArg "hue" "The hue must be between 0.0 and 360.0 degrees."
        elif saturation < 0.0 || saturation > 1.0 then
            invalidArg "saturation" "The saturation must be in the range [0.0, 1.0]."
        elif brightness < 0.0 || brightness > 1.0 then
            invalidArg "brightness" "The brightness value must be in the range [0.0, 1.0]."

        let chroma = saturation * brightness
        
        let r', g', b' =
            let hue' = hue / 60.0
            let x =
                chroma * (1.0 - abs ((hue' % 2.0) - 1.0))

            if hue' < 0.0 then
                // This shouldn't ever happen, but just to be sure...
                0.0, 0.0, 0.0
            elif hue' < 1.0 then
                chroma, x, 0.0
            elif hue' < 2.0 then
                x, chroma, 0.0
            elif hue' < 3.0 then
                0.0, chroma, x
            elif hue' < 4.0 then
                0.0, x, chroma
            elif hue' < 5.0 then
                x, 0.0, chroma
            else // x >= 5 && x < 6
                chroma, 0.0, x

        let m = brightness - chroma

        Color.FromArgb (
            int ((r' + m) * 255.0),
            int ((g' + m) * 255.0),
            int ((b' + m) * 255.0))

    /// Returns a randomly-generated color palette
    /// with the specified number of colors.
    let random count =
        // Preconditions
        // TODO : Count must be non-negative.

        // TODO : If the count is zero return an empty array.

        let rng = System.Random ()
        // Create the random hue value for each color.
        Array.init count <| fun _ -> rng.NextDouble ()
        |> Array.map (fun hue ->
            // The saturation and brightness values can be tweaked as desired.
            let h = (hue + phi_conj) % 1.0
            colorFromHSV (h * 360.0, 0.5, 0.95))


[<RequireQualifiedAccess>]
module Dgml =
    open System.Xml
    open System.Xml.Linq
    open LanguagePrimitives

    (* TODO :   Apply styles to the start state of each rule (perhaps some distinct
                background color which is the same for the start states of all rules);
                apply a style, e.g., thicker border stroke, to final (accepting) states. *)

    //
    let inline private dfaStateUniqueNodeId (ruleId : RuleIdentifier) (dfaStateId : DfaStateId) =
        sprintf "%s_State_%i" ruleId (int dfaStateId)

    /// Escapes control characters.
    // NOTE : The backslash must be double-escaped so it is handled
    // correctly in the generated DGML file.
    let private escapedChar = function
        | '\u0000' -> "\\0"
        | '\u0007' -> "\\a"
        | '\u0008' -> "\\b"
        | '\u0009' -> "\\t"
        | '\u000a' -> "\\n"
        | '\u000c' -> "\\f"
        | '\u000d' -> "\\r"
        // For readability
        | ' ' -> "' '"
        | c ->
            if int c < 0x20 || int c = 0x7f then
                sprintf "\\0x%02x" (int c)
            else
                c.ToString ()

//    //
//    let private xlinqTest () =
//        let logged = XDocument ()
//
//        let name = "John Doe"
//        let category = "FooBar"
//        
//        logged.Add [|
//            XElement (XName.Get "Properties",
//                XElement (XName.Get "AcceptedRuleClauseIndex",
//                    XAttribute (XName.Get "Name", name),
//                    XAttribute (XName.Get "Category", category)))
//            |]
//        //logged.Save

    // Emits DGML where each DFA is a separate component of the graph.
    let emitSeparate (compiledSpec : CompiledSpecification) (options : CompilationOptions) =
        //
        let dgmlDoc = XmlDocument ()
        let xmlDecl = dgmlDoc.CreateXmlDeclaration ("1.0", "utf-8", null)
        
        let directedGraph =
            dgmlDoc.CreateElement ("DirectedGraph", "http://schemas.microsoft.com/vs/2009/dgml")
            |> dgmlDoc.AppendChild

        do
            // Add property definitions
            let properties =
                dgmlDoc.CreateElement ("Properties", directedGraph.NamespaceURI)
                |> directedGraph.AppendChild

            // Accepted Rule Clause Index property
            let acceptedRuleClauseIndexProperty =
                dgmlDoc.CreateElement ("Property", directedGraph.NamespaceURI)
                |> properties.AppendChild

            let idAttr = dgmlDoc.CreateAttribute "Id"
            acceptedRuleClauseIndexProperty.Attributes.Append idAttr |> ignore
            idAttr.Value <- "AcceptedRuleClauseIndex"

            let labelAttr = dgmlDoc.CreateAttribute "Label"
            acceptedRuleClauseIndexProperty.Attributes.Append labelAttr |> ignore
            labelAttr.Value <- "Accepted Rule-Clause Index"

            let dataTypeAttr = dgmlDoc.CreateAttribute "DataType"
            acceptedRuleClauseIndexProperty.Attributes.Append dataTypeAttr |> ignore
            dataTypeAttr.Value <- "System.Int32"

//        do
//            // Add style definitions
//            let styles =
//                dgmlDoc.CreateElement ("Styles", directedGraph.NamespaceURI)
//                |> directedGraph.AppendChild
//
//            // Final (accepting) state style
//            let finalStateStyle =
//                dgmlDoc.CreateElement ("Style", directedGraph.NamespaceURI)
//                |> styles.AppendChild
//
//            let targetTypeAttr = dgmlDoc.CreateAttribute "Id"
//            finalStateStyle.Attributes.Append targetTypeAttr |> ignore
//            targetTypeAttr.Value <- "Node"
//
//            let groupLabelAttr = dgmlDoc.CreateAttribute "Final"
//            finalStateStyle.Attributes.Append groupLabelAttr |> ignore
//            groupLabelAttr.Value <- "Final (Accepting) State"
//
//            // TODO
//            ()

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
        let categoryColors =
            Palette.random compiledSpec.CompiledRules.Count
        (0, compiledSpec.CompiledRules)
        ||> Map.fold (fun ruleIndex ruleId compiledRule ->
            // Add a category for this rule.
            let ruleCategory =
                dgmlDoc.CreateElement ("Category", directedGraph.NamespaceURI)
                |> categories.AppendChild

            // Set the Id attribute value.
            // This isn't shown on the graph, it's only used as a unique identifier for the node.
            let idAttr = dgmlDoc.CreateAttribute "Id"
            ruleCategory.Attributes.Append idAttr |> ignore
            idAttr.Value <- ruleId

            // Set the background color for this category.
            let backgroundAttr = dgmlDoc.CreateAttribute "Background"
            ruleCategory.Attributes.Append backgroundAttr |> ignore
            backgroundAttr.Value <-
                let color = categoryColors.[ruleIndex]
                sprintf "#%02x%02x%02x" color.R color.G color.B

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

                // If this is a final (accepting) DFA state, set the
                // AcceptedRuleClauseIndex attribute value.
                Map.tryFind dfaStateId compiledRule.Dfa.RuleAcceptedByState
                |> Option.iter (fun acceptedRuleClauseIndex ->
                    let acceptedRuleClauseIndexAttr = dgmlDoc.CreateAttribute "AcceptedRuleClauseIndex"
                    dfaStateNode.Attributes.Append acceptedRuleClauseIndexAttr |> ignore
                    acceptedRuleClauseIndexAttr.Value <- acceptedRuleClauseIndex.ToString ())

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
                        sb.ToString ())

            // Add the EOF transition if this rule has one.
            compiledRule.Dfa.Transitions.EofTransition
            |> Option.iter (fun edgeKey ->
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
                labelAttr.Value <- "EOF"
                )

            // Increment the rule index
            ruleIndex + 1)
        // Discard the rule index
        |> ignore

        // Write the document to a file.
        // TEMP : This is a hard-coded filename -- we should determine this from
        // the compiler options. Perhaps take the specified output filename and
        // change the extension to .dgml.
        dgmlDoc.Save "CompiledLexerDfa.dgml"

//        let sb = StringBuilder ()
//        using (new StringWriter (sb)) dgmlDoc.Save
//        sb.ToString ()


