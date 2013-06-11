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

namespace Graham


/// Tags an integer as denoting the zero-based index of a nonterminal
/// within the set of nonterminals in a grammar.
[<Measure>] type NonterminalIndexTag
/// The zero-based index of a nonterminal within the set of nonterminals in a grammar.
type NonterminalIndex = int<NonterminalIndexTag>

/// Tags an integer as denoting the zero-based index of a terminal
/// within the set of terminals in a grammar.
[<Measure>] type TerminalIndexTag
/// The zero-based index of a terminal within the set of terminals in a grammar.
type TerminalIndex = int<TerminalIndexTag>

/// Tags an integer as denoting the zero-based index of a production rule.
[<Measure>] type ProductionRuleIndexTag
/// The zero-based index of a production rule.
type ProductionRuleIndex = int<ProductionRuleIndexTag>

/// A production rule where the nonterminal and terminal symbols
/// have been replaced by their respective tagged-indices.
type TaggedProductionRule = Symbol<NonterminalIndex, TerminalIndex>[]

/// A context-free grammar (CFG) where each nonterminal, terminal, and production rule
/// has been indexed and tagged. This allows for efficient implementations of the grammar
/// analyses and parser-generation algorithms no matter which types are used for the
/// grammar's terminals and nonterminals.
type TaggedGrammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    /// The nonterminals of the grammar.
    Nonterminals : TagBimap<NonterminalIndexTag, 'Nonterminal>;
    /// The terminals of the grammar.
    Terminals : TagBimap<TerminalIndexTag, 'Terminal>;
    
    (* TODO : Change this so the value is a vector (from ExtCore) instead of an array, because it should be immutable. *)
    /// The production rules of the grammar.
    Productions : TagMap<ProductionRuleIndexTag, TaggedProductionRule>;
    
    (* OPTIMIZE : Can we implement a "TagMultiBimap" data structure to combine and simplify the next two fields? *)
    /// Maps the index of each nonterminal in the grammar to the set of production rules
    /// which produce the nonterminal when matched.
    ProductionsByNonterminal : TagMap<NonterminalIndexTag, TagSet<ProductionRuleIndexTag>>;
    /// Given a production-rule-index, returns the nonterminal-index produced by the rule when matched.
    NonterminalOfProduction : TagMap<ProductionRuleIndexTag, NonterminalIndex>;
}

/// Functional operators related to the TaggedGrammar<_,_> type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TaggedGrammar =
    /// An empty tagged-grammar.
    [<CompiledName("Empty")>]
    let empty<'Nonterminal, 'Terminal
        when 'Nonterminal : comparison
        and 'Terminal : comparison> : TaggedGrammar<'Nonterminal, 'Terminal> =
      { Nonterminals = TagBimap.empty;
        Terminals = TagBimap.empty;
        Productions = TagMap.empty;
        ProductionsByNonterminal = TagMap.empty;
        NonterminalOfProduction = TagMap.empty; }

    /// Create a tagged grammar from a grammar.
    [<CompiledName("OfGrammar")>]
    let ofGrammar (grammar : Grammar<'Nonterminal, 'Terminal>) : TaggedGrammar<'Nonterminal, 'Terminal> =
        // If the grammar is empty, return immediately.
        if Map.isEmpty grammar then empty
        else
            /// The nonterminal and terminal sets of the grammar.
            let nonterminals, terminals = Grammar.symbolSets grammar

            /// The nonterminals of the grammar, indexed and tagged.
            let taggedNonterminals =
                (TagBimap.empty, nonterminals)
                ||> Set.fold (fun taggedNonterminals nonterminal ->
                    /// The index of this nonterminal.
                    let nonterminalIndex = tag <| TagBimap.count taggedNonterminals

                    // Add the nonterminal and its tagged-index to the map.
                    TagBimap.add nonterminalIndex nonterminal taggedNonterminals)

            /// The terminals of the grammar, indexed and tagged.
            let taggedTerminals =
                (TagBimap.empty, terminals)
                ||> Set.fold (fun taggedTerminals terminal ->
                    /// The index of this terminal.
                    let terminalIndex = tag <| TagBimap.count taggedTerminals

                    // Add the terminal and its tagged-index to the map.
                    TagBimap.add terminalIndex terminal taggedTerminals)

            /// The tagged grammar, containing only the tagged nonterminals/terminals.
            let taggedGrammar =
                { empty with
                    Nonterminals = taggedNonterminals;
                    Terminals = taggedTerminals; }

            // Fold over the grammar to populate the remaining fields of the tagged grammar.
            (taggedGrammar, grammar)
            ||> Map.fold (fun taggedGrammar nonterminal productionRules ->
                /// The tagged-index of this nonterminal.
                let nonterminalIndex = TagBimap.findValue nonterminal taggedGrammar.Nonterminals

                (taggedGrammar, productionRules)
                ||> Array.fold (fun taggedGrammar productionRule ->
                    /// A copy of the production rule, where the original nonterminal and terminal
                    /// symbols have been replaced by their respective tagged-indices.
                    let taggedProductionRule : TaggedProductionRule =
                        productionRule
                        |> Array.map (function
                            | Nonterminal nonterminal ->
                                Nonterminal <| TagBimap.findValue nonterminal taggedNonterminals
                            | Terminal terminal ->
                                Terminal <| TagBimap.findValue terminal taggedTerminals)
                    
                    /// The index of this production rule.
                    let productionRuleIndex = tag <| TagMap.count taggedGrammar.Productions

                    // Add this production rule to the set of production rules which produce this nonterminal.
                    let nonterminalProductions =
                        match TagMap.tryFind nonterminalIndex taggedGrammar.ProductionsByNonterminal with
                        | None ->
                            TagSet.singleton productionRuleIndex
                        | Some productions ->
                            TagSet.add productionRuleIndex productions

                    // Add the 'tagged' production rule to the tagged grammar;
                    // also associate the rule with the nonterminal it produces.
                    { taggedGrammar with
                        Productions =
                            TagMap.add productionRuleIndex taggedProductionRule taggedGrammar.Productions;
                        NonterminalOfProduction =
                            TagMap.add productionRuleIndex nonterminalIndex taggedGrammar.NonterminalOfProduction;
                        ProductionsByNonterminal =
                            TagMap.add nonterminalIndex nonterminalProductions taggedGrammar.ProductionsByNonterminal;
                        }))

    /// Create a grammar from a tagged grammar.
    [<CompiledName("ToGrammar")>]
    let toGrammar (taggedGrammar : TaggedGrammar<'Nonterminal, 'Terminal>) : Grammar<'Nonterminal, 'Terminal> =
        (Map.empty, taggedGrammar.Nonterminals)
        ||> TagBimap.fold (fun grammar nonterminalIndex nonterminal ->
            /// The production rules for this nonterminal.
            let productionRules =
                taggedGrammar.ProductionsByNonterminal
                |> TagMap.find nonterminalIndex
                |> TagSet.toArray
                |> Array.map (fun productionRuleIndex ->
                    // Get the production rule, then map its symbols back to
                    // the original nonterminals and terminals.
                    taggedGrammar.Productions
                    |> TagMap.find productionRuleIndex
                    |> Array.map (function
                        | Symbol.Terminal terminalIndex ->
                            taggedGrammar.Terminals
                            |> TagBimap.find terminalIndex
                            |> Symbol.Terminal

                        | Symbol.Nonterminal nonterminalIndex ->
                            taggedGrammar.Nonterminals
                            |> TagBimap.find nonterminalIndex
                            |> Symbol.Nonterminal))

            // Add the production rules for this nonterminal to the grammar.
            Map.add nonterminal productionRules grammar)


/// A tagged, augmented grammar.
type TaggedAugmentedGrammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    TaggedGrammar<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>

