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
    
    /// The production rules of the grammar.
    // TODO : Change this so the value is a vector (from ExtCore) instead of an array, because it should be immutable.
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
    [<System.Obsolete(
       "This function should not be used except as a temporary aid for adapting \
        newer code based on TaggedGrammar to work with older code based on Grammar.")>]
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


/// A context-free grammar (CFG) where each nonterminal, terminal, and production rule
/// has been indexed and tagged. The grammar is "augmented" with an additional
/// nonterminal representing the start symbol, production rules associated with that
/// nonterminal, and an additional terminal representing the end-of-file marker.
/// Compared with TaggedGrammar, AugmentedTaggedGrammar also contains information about
/// the starting productions of a grammar and the declared types of the grammar's
/// terminals and nonterminals.
type AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType
    when 'Nonterminal : comparison
    and 'Terminal : comparison> = {
    /// The nonterminals of the grammar.
    Nonterminals : TagBimap<NonterminalIndexTag, AugmentedNonterminal<'Nonterminal>>;
    /// The terminals of the grammar.
    Terminals : TagBimap<TerminalIndexTag, AugmentedTerminal<'Terminal>>;
    
    /// The production rules of the grammar.
    // TODO : Change this so the value is a vector (from ExtCore) instead of an array, because it should be immutable.
    Productions : TagMap<ProductionRuleIndexTag, TaggedProductionRule>;
    
    (* OPTIMIZE : Can we implement a "TagMultiBimap" data structure to combine and simplify the next two fields? *)

    /// Maps the index of each nonterminal in the grammar to the set of production rules
    /// which produce the nonterminal when matched.
    ProductionsByNonterminal : TagMap<NonterminalIndexTag, TagSet<ProductionRuleIndexTag>>;
    /// Given a production-rule-index, returns the nonterminal-index produced by the rule when matched.
    NonterminalOfProduction : TagMap<ProductionRuleIndexTag, NonterminalIndex>;

    /// The set of starting nonterminals for the grammar.
    /// That is, the set of nonterminals which can represent a completely-parsed input string.
    /// Invariant: This set cannot be empty.
    StartNonterminals : TagSet<NonterminalIndexTag>;
    /// The declared type, if any, for the nonterminals of the grammar.
    /// This map only contains entries for nonterminals which have an explicitly-declared type.
    NonterminalTypes : TagMap<NonterminalIndexTag, 'DeclaredType>;
    /// The declared type, if any, for the terminals of the grammar.
    /// This map only contains entries for terminals which have an explicitly-declared type.
    TerminalTypes : TagMap<TerminalIndexTag, 'DeclaredType>;
}

/// Functional operators related to the AugmentedTaggedGrammar<_,_> type.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module AugmentedTaggedGrammar =
    /// An empty tagged, augmented grammar.
    [<CompiledName("Empty")>]
    let empty<'Nonterminal, 'Terminal, 'DeclaredType
        when 'Nonterminal : comparison
        and 'Terminal : comparison>
        : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType> =
      { Nonterminals = TagBimap.empty;
        Terminals = TagBimap.empty;
        Productions = TagMap.empty;
        ProductionsByNonterminal = TagMap.empty;
        NonterminalOfProduction = TagMap.empty;
        StartNonterminals = TagSet.empty;
        NonterminalTypes = TagMap.empty;
        TerminalTypes = TagMap.empty; }

    /// <summary>Augments a Grammar with a unique "start" symbol and the end-of-file marker.</summary>
    /// <param name="taggedGrammar">The grammar to be augmented.</param>
    /// <param name="startingNonterminals">The parser will begin parsing with any one of these symbols.</param>
    /// <returns>A grammar augmented with the Start symbol and the EndOfFile marker.</returns>
    [<CompiledName("AugmentWith")>]
    let augmentWith (taggedGrammar : TaggedGrammar<'Nonterminal, 'Terminal>) (startingNonterminals : Set<'Nonterminal>)
        : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType> =
        // Preconditions
        if Set.isEmpty startingNonterminals then
            invalidArg "startingNonterminals" "The set of starting nonterminals is empty."

        (*  Based on the input grammar, create a new grammar with an additional
            nonterminal and production rules for the start symbol and an additional
            terminal representing the end-of-file marker. *)

        let nonterminals' =
            (TagBimap.empty, taggedGrammar.Nonterminals)
            ||> TagBimap.fold (fun nonterminals' nonterminalIndex nonterminal ->
                let nonterminal' = AugmentedNonterminal.Nonterminal nonterminal
                TagBimap.add (nonterminalIndex + 1<_>) nonterminal' nonterminals')
            // The start symbol is assigned an index of zero (0).
            |> TagBimap.add 0<_> Start

        let terminals' =
            // OPTIMIZE : Use TagBimap.map from ExtCore.
            let terminals' =
                (TagBimap.empty, taggedGrammar.Terminals)
                ||> TagBimap.fold (fun terminals' terminalIndex terminal ->
                    TagBimap.add terminalIndex (AugmentedTerminal.Terminal terminal) terminals')
            
            // Add the end-of-file marker.
            TagBimap.add (tag <| TagBimap.count terminals') EndOfFile terminals'
            
        /// The tagged-indices of the starting nonterminals.
        let startingNonterminals' =
            (TagSet.empty, startingNonterminals)
            ||> Set.fold (fun startingNonterminals nonterminal ->
                let nonterminal' = AugmentedNonterminal.Nonterminal nonterminal
                match TagBimap.tryFindValue nonterminal' nonterminals' with
                | Some nonterminalIndex ->
                    TagSet.add nonterminalIndex startingNonterminals
                | None ->
                    let msg = sprintf "The set of starting nonterminals contains an item '%O' which is not a nonterminal of the grammar." nonterminal
                    raise <| exn msg)

        let startSymbolProductionCount = TagSet.count startingNonterminals'

        let productions' =
            let productions' =
                let endOfFileTerminalIndex = TagBimap.findValue EndOfFile terminals'
                // OPTIMIZE : Use TagMap.foldi from ExtCore.
                (TagMap.empty, startingNonterminals')
                ||> TagSet.fold (fun productions' startingNonterminalIndex ->
                    let productionRule =
                        [|  Symbol.Nonterminal startingNonterminalIndex;
                            Symbol.Terminal endOfFileTerminalIndex; |]
                    TagMap.add (tag <| TagMap.count productions') productionRule productions')
            
            (productions', taggedGrammar.Productions)
            ||> TagMap.fold (fun productions' productionIndex productionRule ->
                let productionIndex' = productionIndex + tag startSymbolProductionCount
                let productionRule' =
                    // Remember, we incremented the nonterminal indices when adding the Start nonterminal,
                    // so we need to adjust the production rules to match.
                    productionRule
                    |> Array.map (function
                        | Symbol.Terminal _ as terminal ->
                            terminal
                        | Symbol.Nonterminal nonterminalIndex ->
                            Symbol.Nonterminal (nonterminalIndex + 1<_>))

                // Add the updated production index and rule to the augmented production map.
                TagMap.add productionIndex' productionRule' productions')

        let startNonterminalIndex = TagBimap.findValue Start nonterminals'
        
        let productionsByNonterminal' =
            let productionsByNonterminal' =
                // Add the productions for the Start nonterminal to an empty map.
                (0, startSymbolProductionCount - 1, TagSet.empty)
                |||> Range.fold (fun startProductions i -> TagSet.add (tag i) startProductions)
                |> TagMap.singleton startNonterminalIndex

            (productionsByNonterminal', taggedGrammar.ProductionsByNonterminal)
            ||> TagMap.fold (fun productionsByNonterminal' nonterminalIndex productionIndices ->
                let nonterminalIndex' = nonterminalIndex + 1<_>
                let productionIndices' =
                    productionIndices
                    |> TagSet.map (fun productionIndex ->
                        productionIndex + tag startSymbolProductionCount)

                // Add the updated production index and production-index set to the map.
                TagMap.add nonterminalIndex' productionIndices' productionsByNonterminal')
            
        let nonterminalOfProduction' =
            let nonterminalOfProduction' =
                // Add the productions for the Start nonterminal to an empty map.
                (0, startSymbolProductionCount - 1, TagMap.empty)
                |||> Range.fold (fun nonterminalOfProduction i ->
                    TagMap.add (tag i) startNonterminalIndex nonterminalOfProduction)

            (nonterminalOfProduction', taggedGrammar.NonterminalOfProduction)
            ||> TagMap.fold (fun nonterminalOfProduction' productionIndex nonterminalIndex ->
                let productionIndex' = productionIndex + tag startSymbolProductionCount
                let nonterminalIndex' = nonterminalIndex + 1<_>
                TagMap.add productionIndex' nonterminalIndex' nonterminalOfProduction')

        {   Nonterminals = nonterminals';
            Terminals = terminals';
            Productions = productions';
            ProductionsByNonterminal = productionsByNonterminal';
            NonterminalOfProduction = nonterminalOfProduction';
            StartNonterminals = startingNonterminals';
            NonterminalTypes = TagMap.empty;
            TerminalTypes = TagMap.empty; }
                            
    /// <summary>Augments a Grammar with a unique "start" symbol and the end-of-file marker.</summary>
    /// <param name="taggedGrammar">The grammar to be augmented.</param>
    /// <param name="startingNonterminal">The parser will begin parsing with this symbol.</param>
    /// <returns>A grammar augmented with the Start symbol and the EndOfFile marker.</returns>
    [<CompiledName("Augment")>]
    let augment (taggedGrammar : TaggedGrammar<'Nonterminal, 'Terminal>) startingNonterminal
        : AugmentedTaggedGrammar<'Nonterminal, 'Terminal, 'DeclaredType> =
        augmentWith taggedGrammar (Set.singleton startingNonterminal)

