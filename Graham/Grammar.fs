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

open System.Diagnostics


/// A nonterminal or the start symbol.
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type AugmentedNonterminal<'Nonterminal when 'Nonterminal : comparison> =
    /// The start symbol.
    | Start
    /// A nonterminal symbol specified by a grammar.
    | Nonterminal of 'Nonterminal

    /// <inherit />
    override this.ToString () =
        match this with
        | Start ->
            "\xabStart\xbb"
        | Nonterminal nonterm ->
            nonterm.ToString ()        

/// A terminal (token) or the end-of-file marker.
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type AugmentedTerminal<'Terminal when 'Terminal : comparison> =
    /// A terminal symbol specified by a grammar.
    | Terminal of 'Terminal
    /// The end-of-file marker.
    | EndOfFile

    /// <inherit />
    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | EndOfFile ->
            "$"

/// A symbol within a context-free grammar (CFG).
type Symbol<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    /// An elementary symbol of the language described by the grammar.
    /// Terminal symbols are often called "tokens", especially when
    /// discussing lexical analysers and parsers.
    | Terminal of 'Terminal
    /// Nonterminal symbols are groups of zero or more terminal symbols;
    /// these groups are defined by the production rules of the grammar.
    | Nonterminal of 'Nonterminal

    /// <inherit />
    override this.ToString () =
        match this with
        | Terminal token ->
            token.ToString ()
        | Nonterminal nonterm ->
            nonterm.ToString ()

    /// 'Lift' the symbol into an equivalent augmented symbol.
    static member Augment (symbol : Symbol<'Nonterminal, 'Terminal>) =
        match symbol with
        | Symbol.Nonterminal nontermId ->
            AugmentedNonterminal.Nonterminal nontermId
            |> Symbol.Nonterminal
        | Symbol.Terminal token ->
            AugmentedTerminal.Terminal token
            |> Symbol.Terminal

/// The right-hand-side (RHS) of a production rule within a context-free grammar (CFG).
type ProductionRule<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Symbol<'Nonterminal, 'Terminal>[]

/// A context-free grammar (CFG).
type Grammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Map<'Nonterminal, ProductionRule<'Nonterminal, 'Terminal>[]>

/// A symbol within a context-free grammar (CFG) augmented with
/// the start symbol and end-of-file marker.
type AugmentedSymbol<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Symbol<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>

/// A production rule comprised of augmented symbols.
type AugmentedProductionRule<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    AugmentedSymbol<'Nonterminal, 'Terminal>[]

/// A grammar augmented with the "start" symbol and the end-of-file marker.
type AugmentedGrammar<'Nonterminal, 'Terminal
    when 'Nonterminal : comparison
    and 'Terminal : comparison> =
    Grammar<AugmentedNonterminal<'Nonterminal>, AugmentedTerminal<'Terminal>>

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Grammar =
    //
    [<CompiledName("Nonterminals")>]
    let nonterminals (grammar : Grammar<'Nonterminal, 'Terminal>) =
        (Set.empty, grammar)
        ||> Map.fold (fun nonterminals nonterminal productionRules ->
            let nonterminals = Set.add nonterminal nonterminals

            (nonterminals, productionRules)
            ||> Array.fold (Array.fold (fun nonterminals symbol ->
                match symbol with
                | Nonterminal nonterminal ->
                    Set.add nonterminal nonterminals
                | Terminal _ ->
                    nonterminals)))

    //
    [<CompiledName("Terminals")>]
    let terminals (grammar : Grammar<'Nonterminal, 'Terminal>) =
        (Set.empty, grammar)
        ||> Map.fold (fun terminals _ rules ->
            (terminals, rules)
            ||> Array.fold (Array.fold (fun terminals symbol ->
                match symbol with
                | Nonterminal _ ->
                    terminals
                | Terminal terminal ->
                    Set.add terminal terminals)))

    /// Computes sets containing the nonterminals and terminals used with the productions of a grammar.
    [<CompiledName("SymbolSets")>]
    let symbolSets (grammar : Grammar<'Nonterminal, 'Terminal>) =
        ((Set.empty, Set.empty), grammar)
        ||> Map.fold (fun (nonterminals, terminals) nonterminal productionRules ->
            let nonterminals = Set.add nonterminal nonterminals

            ((nonterminals, terminals), productionRules)
            ||> Array.fold (Array.fold (fun (nonterminals, terminals) symbol ->
                match symbol with
                | Nonterminal nonterminal ->
                    Set.add nonterminal nonterminals, terminals
                | Terminal terminal ->
                    nonterminals, Set.add terminal terminals)))


/// Active patterns which simplify pattern matching on augmented grammars.
module internal AugmentedPatterns =
    let inline (|Nonterminal|Start|) (augmentedNonterminal : AugmentedNonterminal<'Nonterminal>) =
        match augmentedNonterminal with
        | AugmentedNonterminal.Nonterminal nonterminal ->
            Nonterminal nonterminal
        | AugmentedNonterminal.Start ->
            Start

    let inline (|Terminal|EndOfFile|) (augmentedTerminal : AugmentedTerminal<'Terminal>) =
        match augmentedTerminal with
        | AugmentedTerminal.Terminal terminal ->
            Terminal terminal
        | AugmentedTerminal.EndOfFile ->
            EndOfFile
