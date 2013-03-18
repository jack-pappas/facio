(*

Copyright 2013 Jack Pappas

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

/// Grammars from Dick Grune's "Parsing Techniques, A Practical Guide".
module Graham.Tests.Grammars.Grune

open Graham.Grammar


/// Figure 4.4: A grammar describing numbers in scientific notation.
let ``Figure 4.4`` =
    let ``Figure 4.4`` =
        // NOTE : This is the start symbol.
        let Number =
            [|  [| Nonterminal "Integer" |];
                [| Nonterminal "Real" |];   |]

        let Integer =
            [|  [| Nonterminal "Digit" |];
                [| Nonterminal "Integer"; Nonterminal "Digit" |];   |]

        let Real =
            [|  [| Nonterminal "Integer"; Nonterminal "Fraction"; Nonterminal "Scale" |];   |]

        let Fraction =
            [|  [| Terminal '.'; Nonterminal "Integer" |];  |]

        let Scale =
            [|  [| Terminal 'e'; Nonterminal "Sign"; Nonterminal "Integer" |];
                [| Nonterminal "Empty" |];  |]

        let Digit =
            [|  [| Terminal '0' |];
                [| Terminal '1' |];
                [| Terminal '2' |];
                [| Terminal '3' |];
                [| Terminal '4' |];
                [| Terminal '5' |];
                [| Terminal '6' |];
                [| Terminal '7' |];
                [| Terminal '8' |];
                [| Terminal '9' |]; |]

        let Empty =
            [|  [| |] |]

        let Sign =
            [|  [| Terminal '+' |];
                [| Terminal '-' |]; |]

        let productions =
            Map.empty
            |> Map.add "Number" Number
            |> Map.add "Integer" Integer
            |> Map.add "Real" Real
            |> Map.add "Fraction" Fraction
            |> Map.add "Scale" Scale
            |> Map.add "Digit" Digit
            |> Map.add "Empty" Empty
            |> Map.add "Sign" Sign

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (``Figure 4.4``, "Number")

/// Figure 4.8: An example grammar to test epsilon-rule elimination schemes.
let ``Figure 4.8`` =
    let S =
        [|  [| Nonterminal 'L'; Terminal 'a'; Nonterminal 'M' |];   |]

    let L =
        [|  [| Nonterminal 'L'; Nonterminal 'M' |];
            [| |];  |]

    let M =
        [|  [| Nonterminal 'M'; Nonterminal 'M' |];
            [| |];  |]

    let productions =
        Map.empty
        |> Map.add 'S' S
        |> Map.add 'L' L
        |> Map.add 'M' M

    let nonterminals, terminals =
        Grammar.SymbolSets productions

    {   Terminals = terminals;
        Nonterminals = nonterminals;
        Productions = productions; }



