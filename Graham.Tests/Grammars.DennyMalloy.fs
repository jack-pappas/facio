(*

Copyright 2014 Jack Pappas

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

/// Grammars from "The IELR(1) Algorithm for Generating Minimal LR(1) Parser Tables for Non-LR(1) Grammars with Conflict Resolution"
/// by Joel E. Denny and Brian A. Malloy.
module Tests.Graham.Grammars.DennyMalloy

open Graham.Grammar


/// Figure 1: An unambiguous grammar.
/// This grammar defines a language consisting of 4 sentences, each of which corresponds to 1 parse tree:
/// "aaa", "aaaa", "bab", "baab". Assuming that the parser is LR(1) and 'a' is left-associative,
/// the sentence "aaaa" is dropped from the language.
let ``Figure 1`` =
    let S =
        [|  [| Terminal 'a'; Nonterminal "A"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "A"; Terminal 'b' |];   |]

    let A =
        [|  [| Terminal 'a' |];
            [| Terminal 'a'; Terminal 'a' |];   |]

    let productions =
        Map.empty
        |> Map.add "S" S
        |> Map.add "A" A

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }

/// Figure 2: An ambiguous grammar.
/// This grammar is ambiguous because it can generate two parse trees for the sentence "baaa".
let ``Figure 2`` =
    let S =
        [|  [| Terminal 'a'; Nonterminal "A"; Terminal 'a' |];
            [| Terminal 'a'; Nonterminal "B"; Terminal 'b' |];
            [| Terminal 'a'; Nonterminal "C"; Terminal 'c' |];
            [| Terminal 'b'; Nonterminal "A"; Terminal 'b' |];
            [| Terminal 'b'; Nonterminal "B"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "C"; Terminal 'a' |];   |]

    let A =
        [|  [| Terminal 'a'; Terminal 'a' |];   |]

    let B =
        [|  [| Terminal 'a'; Terminal 'a' |];   |]

    let C =
        [|  [| Terminal 'a'; Terminal 'a' |];   |]

    let productions =
        Map.empty
        |> Map.add "S" S
        |> Map.add "A" A
        |> Map.add "B" B
        |> Map.add "C" C

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }

/// Figure 3: Another ambiguous grammar.
/// This grammar is the grammar of 'Figure 2' with the last token in each of production 2 and 3 replaced with 'a'.
/// This affects the lookahead sets in canonical LR(1) states 17 and 18 in 'Table 3' (see paper) such that they
/// now pass Pager's weak compatibility test with states 19 and 20.
let ``Figure 3`` =
    let S =
        [|  [| Terminal 'a'; Nonterminal "A"; Terminal 'a' |];
            [| Terminal 'a'; Nonterminal "B"; Terminal 'a' |];
            [| Terminal 'a'; Nonterminal "C"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "A"; Terminal 'b' |];
            [| Terminal 'b'; Nonterminal "B"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "C"; Terminal 'a' |];   |]

    let A =
        [|  [| Terminal 'a'; Terminal 'a' |];   |]

    let B =
        [|  [| Terminal 'a'; Terminal 'a' |];   |]

    let C =
        [|  [| Terminal 'a'; Terminal 'a' |];   |]

    let productions =
        Map.empty
        |> Map.add "S" S
        |> Map.add "A" A
        |> Map.add "B" B
        |> Map.add "C" C

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }

/// Figure 4. Pager vs Menhir
/// For this grammar, Pager's algorithm generates parser tables that contain a mysterious new conflict on 'b'
/// between reductions 6 and 7. However, Menhir rejects the isocore merge that creates this conflict.
let ``Figure 4`` =
    let S =
        [|  [| Terminal 'a'; Nonterminal "A"; Terminal 'a' |];
            [| Terminal 'a'; Nonterminal "A"; Terminal 'b' |];
            [| Terminal 'a'; Nonterminal "B"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "A"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "B"; Terminal 'b' |];   |]

    let A =
        [|  [| Terminal 'a' |];   |]

    let B =
        [|  [| Terminal 'a' |];   |]

    let productions =
        Map.empty
        |> Map.add "S" S
        |> Map.add "A" A
        |> Map.add "B" B

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }

/// Figure 5: Grammar Demonstrating Goto Follows
/// We assume production 9 [E -> (empty)] is declared with greater precedence than 'a'.
// TODO : Make sure the assumption holds correctly in Graham. It would be useful for testing purposes to expose an API
//        which allows the precedence of terminals and nonterminals to be determined, or at least provides a way to compare
//        the relative precedence of two symbols.
let ``Figure 5`` =
    let S =
        [|  [| Terminal 'a'; Nonterminal "A"; Nonterminal "B"; Terminal 'a' |];
            [| Terminal 'b'; Nonterminal "A"; Nonterminal "B"; Terminal 'b' |]; |]

    let A =
        [|  [| Terminal 'a'; Nonterminal "C"; Nonterminal "D"; Nonterminal "E" |];   |]

    let B =
        [|  [| Terminal 'c' |];
            [| (*empty*) |];    |]

    let C =
        [|  [| Nonterminal "D" |];   |]

    let D =
        [|  [| Terminal 'a' |];   |]

    let E =
        [|  [| Terminal 'a' |];
            [| (*empty*) |];    |]

    let productions =
        Map.empty
        |> Map.add "S" S
        |> Map.add "A" A
        |> Map.add "B" B
        |> Map.add "C" C
        |> Map.add "D" D
        |> Map.add "E" E

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }

/// Figure 6: Grammar For Goto Follows Caveats
let ``Figure 6`` =
    let S =
        [|  [| Terminal 'a'; Nonterminal "A"; Terminal 'a' |];
            [| Terminal 'a'; Terminal 'a'; Terminal 'b' |];
            [| Terminal 'b'; Nonterminal "A"; Terminal 'b' |];  |]

    let A =
        [|  [| Nonterminal "B"; Nonterminal "C" |];   |]

    let B =
        [|  [| Terminal 'a' |]; |]

    let C =
        [|  [| Nonterminal "D" |];   |]

    let D =
        [|  [| (*empty*) |];   |]

    let productions =
        Map.empty
        |> Map.add "S" S
        |> Map.add "A" A
        |> Map.add "B" B
        |> Map.add "C" C
        |> Map.add "D" D

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }
