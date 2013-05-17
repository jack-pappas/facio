(*

Copyright 2012-2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

namespace FSharpLex.Plugin

open System.ComponentModel.Composition
open System.IO
open System.Text
open FSharpLex
open FSharpLex.SpecializedCollections
open FSharpLex.Graph
open FSharpLex.Ast
open FSharpLex.Compile

(* TODO :   Move this backend into a separate assembly so the 'fsharplex' project
            won't have a dependency on System.Xml.dll. *)
(* TODO :   Implement a backend for the dot (graphviz) format. *)

/// Functions for creating Directed Graph Markup Language (DGML) files
/// from the transition graph of the pattern-matching automaton.
[<RequireQualifiedAccess>]
module private Dgml =
    open System.Xml
    open System.Xml.Linq
    open LanguagePrimitives
    open BackendUtils.Drawing

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
    let emitSeparate (compiledSpec : CompiledSpecification, graphOptions : GraphBackendOptions) =
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
                Map.tryFind dfaStateId compiledRule.Dfa.RuleClauseAcceptedByState
                |> Option.iter (fun acceptedRuleClauseIndex ->
                    let acceptedRuleClauseIndexAttr = dgmlDoc.CreateAttribute "AcceptedRuleClauseIndex"
                    dfaStateNode.Attributes.Append acceptedRuleClauseIndexAttr |> ignore
                    acceptedRuleClauseIndexAttr.Value <- acceptedRuleClauseIndex.ToString ())

            // Add the transitions for this rule's DFA.
            compiledRule.Dfa.Transitions.AdjacencyMap
            |> HashMap.iter (fun edgeKey edgeSet ->
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
        dgmlDoc.Save graphOptions.OutputPath


/// A backend which serializes the pattern-matching automaton into a
/// graph-based file format for use with a visualization tool.
//[<Export(typeof<IBackend>)>]  // TEMP : This is only disabled to avoid a fatal exception until we modify our Backends class to support multiple backends.
type GraphBackend () =
    interface IBackend with
        member this.EmitCompiledSpecification (compiledSpec, options) : unit =
            /// Compilation options specific to this backend.
            let graphOptions =
                match options.GraphBackendOptions with
                | None ->
                    raise <| exn "No backend-specific options were provided."
                | Some options ->
                    options

            // Serialize the automaton graph using the specified file format.
            match graphOptions.Format with
            | Dgml ->
                // Emit DGML.
                Dgml.emitSeparate (compiledSpec, graphOptions)

