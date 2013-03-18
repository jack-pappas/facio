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

/// Grammars from Andrew W. Appel's "Modern Compiler Implementation in ML".
module Graham.Tests.Grammars.Appel

open Graham.Grammar


/// Grammar 3.5 from "Modern Compiler Implementation in ML".
let ``Grammar 3.5`` =
    let ``Grammar 3.5`` =
        let E =
            [|  [| Terminal "id" |];
                [| Terminal "num" |];
                [| Nonterminal 'E'; Terminal "*"; Nonterminal 'E' |];
                [| Nonterminal 'E'; Terminal "/"; Nonterminal 'E' |];
                [| Nonterminal 'E'; Terminal "+"; Nonterminal 'E' |];
                [| Nonterminal 'E'; Terminal "-"; Nonterminal 'E' |];
                [| Terminal "("; Nonterminal 'E'; Terminal ")" |]; |]

        let productions =
            Map.empty
            |> Map.add 'E' E

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Grammar 3.5``, 'E')

/// Grammar 3.8 from "Modern Compiler Implementation in ML".
let ``Grammar 3.8`` =
    let ``Grammar 3.8`` =
        /// Factor.
        let F =
            [|  [| Terminal "id" |];
                [| Terminal "num" |];
                [| Terminal "("; Nonterminal 'E'; Terminal ")" |]; |]

        /// Term.
        let T =
            [|  [| Nonterminal 'T'; Terminal "*"; Nonterminal 'F' |];
                [| Nonterminal 'T'; Terminal "/"; Nonterminal 'F' |];
                [| Nonterminal 'F' |]; |]

        /// Expression.
        let E =
            [|  [| Nonterminal 'E'; Terminal "+"; Nonterminal 'T' |];
                [| Nonterminal 'E'; Terminal "-"; Nonterminal 'T' |];
                [| Nonterminal 'T' |]; |]

        let productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T
            |> Map.add 'F' F

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        // Create the grammar from the productions.
        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    // TODO : Make sure this start symbol is correct.
    Grammar.Augment (``Grammar 3.8``, 'F')

/// Grammar 3.12 from "Modern Compiler Implementation in ML".
let ``Grammar 3.12`` =
    let ``Grammar 3.12`` =
        let Z =
            [|  [| Terminal 'd' |];
                [| Nonterminal 'X'; Nonterminal 'Y'; Nonterminal 'Z' |]; |]

        let Y =
            [|  [| (* Empty *) |];
                [| Terminal 'c' |]; |]
   
        let X =
            [|  [| Nonterminal 'Y' |];
                [| Terminal 'a' |]; |]

        let productions =
            Map.empty
            |> Map.add 'X' X
            |> Map.add 'Y' Y
            |> Map.add 'Z' Z

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    // TODO : Make sure this start symbol is correct.
    Grammar.Augment (``Grammar 3.12``, 'Z')

/// Grammar 3.20 from "Modern Compiler Implementation in ML".
let ``Grammar 3.20`` =
    let ``Grammar 3.20`` =
        // NOTE : This grammar does not include the first rule,
        // which is the production of the augmented start symbol.
        let S =
            [|  [| Terminal "("; Nonterminal 'L'; Terminal ")"; |];
                [| Terminal "x"; |]; |]

        let L =
            [|  [| Nonterminal 'S'; |];
                [| Nonterminal 'L'; Terminal ","; Nonterminal 'S'; |]; |]

        let productions =
            Map.empty
            |> Map.add 'L' L
            |> Map.add 'S' S

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Grammar 3.20``, 'S')

/// Grammar 3.23 from "Modern Compiler Implementation in ML".
let ``Grammar 3.23`` =
    let ``Grammar 3.23`` =
        // NOTE : This grammar does not include the first rule,
        // which is the production of the augmented start symbol.
        let E =
            [|  [| Nonterminal 'T'; Terminal "+"; Nonterminal 'E'; |];
                [| Nonterminal 'T' |]; |]

        let T =
            [|  [| Terminal "x" |]; |]

        let productions =
            Map.empty
            |> Map.add 'E' E
            |> Map.add 'T' T

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Grammar 3.23``, 'E')

/// Grammar 3.26 from "Modern Compiler Implementation in ML".
let ``Grammar 3.26`` =
    let ``Grammar 3.26`` =
        // NOTE : This grammar does not include the first
        // rule of the grammar, which is the augmented start production.
        let S =
            [|  [| Nonterminal 'V'; Terminal "="; Nonterminal 'E'; |];
                [| Nonterminal 'E' |]; |]

        let E =
            [|  [| Nonterminal 'V' |]; |]

        let V =
            [|  [| Terminal "x" |];
                [| Terminal "*"; Nonterminal 'E'; |]; |]

        let productions =
            Map.empty
            |> Map.add 'S' S
            |> Map.add 'E' E
            |> Map.add 'V' V

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Grammar 3.26``, 'S')

/// Grammar 3.30 from "Modern Compiler Implementation in ML".
let ``Grammar 3.30`` =
    let ``Grammar 3.30`` =
        // prog
        let P =
            [|  [| Nonterminal 'P' |]; |]

        // stm
        let S =
            [|  [| Terminal "id"; Terminal ":="; Terminal "id"; |];
                [| Terminal "while"; Terminal "id"; Terminal "do"; Nonterminal 'S'; |];
                [| Terminal "begin"; Nonterminal 'L'; Terminal "end"; |];
                [| Terminal "if"; Terminal "id"; Terminal "then"; Nonterminal 'S'; |];
                [| Terminal "if"; Terminal "id"; Terminal "then"; Nonterminal 'S'; Terminal "else"; Nonterminal 'S'; |]; |]

        // stmlist
        let L =
            [|  [| Nonterminal 'S' |];
                [| Nonterminal 'L'; Terminal ";"; Nonterminal 'S'; |]; |]

        let productions =
            Map.empty
            |> Map.add 'P' P
            |> Map.add 'S' S
            |> Map.add 'L' L

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Grammar 3.30``, 'P')

/// Grammar 4.6 from "Modern Compiler Implementation in ML".
let ``Grammar 4.6`` =
    let ``Grammar 4.6`` =
        let S =
            [|  [| Nonterminal 'S'; Terminal ";"; Nonterminal 'S'; |];
                [| Terminal "id"; Terminal ":="; Nonterminal 'E'; |];
                [| Terminal "print"; Nonterminal 'L'; |]; |]

        let E =
            [|  [| Terminal "id"; |];
                [| Terminal "num"; |];
                [| Nonterminal 'E'; Nonterminal 'B'; Nonterminal 'E'; |];
                [| Nonterminal 'S'; Terminal ","; Nonterminal 'E'; |]; |]

        let L =
            [|  [| (* Empty *) |];
                [| Nonterminal 'L'; Nonterminal 'E'; |]; |]

        let B =
            [|  [| Terminal "+"; |];
                [| Terminal "-"; |];
                [| Terminal "*"; |];
                [| Terminal "/"; |]; |]

        let productions =
            Map.empty
            |> Map.add 'S' S
            |> Map.add 'E' E
            |> Map.add 'L' L
            |> Map.add 'B' B

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Grammar 4.6``, 'S')


