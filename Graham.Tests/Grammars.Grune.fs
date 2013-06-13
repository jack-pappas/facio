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
module Tests.Graham.Grammars.Grune

open Graham


/// Figure 4.4: A grammar describing numbers in scientific notation.
let ``Figure 4.4`` : AugmentedTaggedGrammar<_,_,unit> =
    let ``Figure 4.4`` =
        // NOTE : This is the start symbol.
        let Number =
            [|  [| Symbol.Nonterminal "Integer" |];
                [| Symbol.Nonterminal "Real" |];   |]

        let Integer =
            [|  [| Symbol.Nonterminal "Digit" |];
                [| Symbol.Nonterminal "Integer"; Symbol.Nonterminal "Digit" |];   |]

        let Real =
            [|  [| Symbol.Nonterminal "Integer"; Symbol.Nonterminal "Fraction"; Symbol.Nonterminal "Scale" |];   |]

        let Fraction =
            [|  [| Symbol.Terminal '.'; Symbol.Nonterminal "Integer" |];  |]

        let Scale =
            [|  [| Symbol.Terminal 'e'; Symbol.Nonterminal "Sign"; Symbol.Nonterminal "Integer" |];
                [| Symbol.Nonterminal "Empty" |];  |]

        let Digit =
            [|  [| Symbol.Terminal '0' |];
                [| Symbol.Terminal '1' |];
                [| Symbol.Terminal '2' |];
                [| Symbol.Terminal '3' |];
                [| Symbol.Terminal '4' |];
                [| Symbol.Terminal '5' |];
                [| Symbol.Terminal '6' |];
                [| Symbol.Terminal '7' |];
                [| Symbol.Terminal '8' |];
                [| Symbol.Terminal '9' |]; |]

        let Empty =
            [|  [| |] |]

        let Sign =
            [|  [| Symbol.Terminal '+' |];
                [| Symbol.Terminal '-' |]; |]

        Map.empty
        |> Map.add "Number" Number
        |> Map.add "Integer" Integer
        |> Map.add "Real" Real
        |> Map.add "Fraction" Fraction
        |> Map.add "Scale" Scale
        |> Map.add "Digit" Digit
        |> Map.add "Empty" Empty
        |> Map.add "Sign" Sign

    // Tag, then augment the grammar.
    let taggedGrammar = TaggedGrammar.ofGrammar ``Figure 4.4``
    AugmentedTaggedGrammar.augment taggedGrammar "Number"

/// Figure 4.8: An example grammar to test epsilon-rule elimination schemes.
let ``Figure 4.8`` =
    let S =
        [|  [| Symbol.Nonterminal 'L'; Symbol.Terminal 'a'; Symbol.Nonterminal 'M' |];   |]

    let L =
        [|  [| Symbol.Nonterminal 'L'; Symbol.Nonterminal 'M' |];
            [| |];  |]

    let M =
        [|  [| Symbol.Nonterminal 'M'; Symbol.Nonterminal 'M' |];
            [| |];  |]

    Map.empty
    |> Map.add 'S' S
    |> Map.add 'L' L
    |> Map.add 'M' M

