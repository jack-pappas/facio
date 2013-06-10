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
module Tests.Graham.Grammars.Appel

open Graham


/// Grammar 3.5 from "Modern Compiler Implementation in ML".
let ``Grammar 3.5`` =
    let ``Grammar 3.5`` =
        let E =
            [|  [| Symbol.Terminal "id" |];
                [| Symbol.Terminal "num" |];
                [| Symbol.Nonterminal 'E'; Symbol.Terminal "*"; Symbol.Nonterminal 'E' |];
                [| Symbol.Nonterminal 'E'; Symbol.Terminal "/"; Symbol.Nonterminal 'E' |];
                [| Symbol.Nonterminal 'E'; Symbol.Terminal "+"; Symbol.Nonterminal 'E' |];
                [| Symbol.Nonterminal 'E'; Symbol.Terminal "-"; Symbol.Nonterminal 'E' |];
                [| Symbol.Terminal "("; Symbol.Nonterminal 'E'; Symbol.Terminal ")" |]; |]

        Map.empty
        |> Map.add 'E' E

    // Augment the grammar.
    Grammar.augment ``Grammar 3.5`` 'E'

/// Grammar 3.8 from "Modern Compiler Implementation in ML".
let ``Grammar 3.8`` =
    let ``Grammar 3.8`` =
        /// Factor.
        let F =
            [|  [| Symbol.Terminal "id" |];
                [| Symbol.Terminal "num" |];
                [| Symbol.Terminal "("; Symbol.Nonterminal 'E'; Symbol.Terminal ")" |]; |]

        /// Term.
        let T =
            [|  [| Symbol.Nonterminal 'T'; Symbol.Terminal "*"; Symbol.Nonterminal 'F' |];
                [| Symbol.Nonterminal 'T'; Symbol.Terminal "/"; Symbol.Nonterminal 'F' |];
                [| Symbol.Nonterminal 'F' |]; |]

        /// Expression.
        let E =
            [|  [| Symbol.Nonterminal 'E'; Symbol.Terminal "+"; Symbol.Nonterminal 'T' |];
                [| Symbol.Nonterminal 'E'; Symbol.Terminal "-"; Symbol.Nonterminal 'T' |];
                [| Symbol.Nonterminal 'T' |]; |]

        Map.empty
        |> Map.add 'E' E
        |> Map.add 'T' T
        |> Map.add 'F' F

    // Augment the grammar.
    // TODO : Make sure this start symbol is correct.
    Grammar.augment ``Grammar 3.8`` 'F'

/// Grammar 3.12 from "Modern Compiler Implementation in ML".
let ``Grammar 3.12`` =
    let ``Grammar 3.12`` =
        let Z =
            [|  [| Symbol.Terminal 'd' |];
                [| Symbol.Nonterminal 'X'; Symbol.Nonterminal 'Y'; Symbol.Nonterminal 'Z' |]; |]

        let Y =
            [|  [| (* Empty *) |];
                [| Symbol.Terminal 'c' |]; |]
   
        let X =
            [|  [| Symbol.Nonterminal 'Y' |];
                [| Symbol.Terminal 'a' |]; |]

        Map.empty
        |> Map.add 'X' X
        |> Map.add 'Y' Y
        |> Map.add 'Z' Z

    // Augment the grammar.
    // TODO : Make sure this start symbol is correct.
    Grammar.augment ``Grammar 3.12`` 'Z'

/// Grammar 3.20 from "Modern Compiler Implementation in ML".
let ``Grammar 3.20`` =
    let ``Grammar 3.20`` =
        // NOTE : This grammar does not include the first rule,
        // which is the production of the augmented start symbol.
        let S =
            [|  [| Symbol.Terminal "("; Symbol.Nonterminal 'L'; Symbol.Terminal ")"; |];
                [| Symbol.Terminal "x"; |]; |]

        let L =
            [|  [| Symbol.Nonterminal 'S'; |];
                [| Symbol.Nonterminal 'L'; Symbol.Terminal ","; Symbol.Nonterminal 'S'; |]; |]

        Map.empty
        |> Map.add 'L' L
        |> Map.add 'S' S

    // Augment the grammar.
    Grammar.augment ``Grammar 3.20`` 'S'

/// Grammar 3.23 from "Modern Compiler Implementation in ML".
let ``Grammar 3.23`` =
    let ``Grammar 3.23`` =
        // NOTE : This grammar does not include the first rule,
        // which is the production of the augmented start symbol.
        let E =
            [|  [| Symbol.Nonterminal 'T'; Symbol.Terminal "+"; Symbol.Nonterminal 'E'; |];
                [| Symbol.Nonterminal 'T' |]; |]

        let T =
            [|  [| Symbol.Terminal "x" |]; |]

        Map.empty
        |> Map.add 'E' E
        |> Map.add 'T' T

    // Augment the grammar.
    Grammar.augment ``Grammar 3.23`` 'E'

/// Grammar 3.26 from "Modern Compiler Implementation in ML".
let ``Grammar 3.26`` =
    let ``Grammar 3.26`` =
        // NOTE : This grammar does not include the first
        // rule of the grammar, which is the augmented start production.
        let S =
            [|  [| Symbol.Nonterminal 'V'; Symbol.Terminal "="; Symbol.Nonterminal 'E'; |];
                [| Symbol.Nonterminal 'E' |]; |]

        let E =
            [|  [| Symbol.Nonterminal 'V' |]; |]

        let V =
            [|  [| Symbol.Terminal "x" |];
                [| Symbol.Terminal "*"; Symbol.Nonterminal 'E'; |]; |]

        Map.empty
        |> Map.add 'S' S
        |> Map.add 'E' E
        |> Map.add 'V' V

    // Augment the grammar.
    Grammar.augment ``Grammar 3.26`` 'S'

/// Grammar 3.30 from "Modern Compiler Implementation in ML".
let ``Grammar 3.30`` =
    let ``Grammar 3.30`` =
        // prog
        let P =
            [|  [| Symbol.Nonterminal 'P' |]; |]

        // stm
        let S =
            [|  [| Symbol.Terminal "id"; Symbol.Terminal ":="; Symbol.Terminal "id"; |];
                [| Symbol.Terminal "while"; Symbol.Terminal "id"; Symbol.Terminal "do"; Symbol.Nonterminal 'S'; |];
                [| Symbol.Terminal "begin"; Symbol.Nonterminal 'L'; Symbol.Terminal "end"; |];
                [| Symbol.Terminal "if"; Symbol.Terminal "id"; Symbol.Terminal "then"; Symbol.Nonterminal 'S'; |];
                [| Symbol.Terminal "if"; Symbol.Terminal "id"; Symbol.Terminal "then"; Symbol.Nonterminal 'S'; Symbol.Terminal "else"; Symbol.Nonterminal 'S'; |]; |]

        // stmlist
        let L =
            [|  [| Symbol.Nonterminal 'S' |];
                [| Symbol.Nonterminal 'L'; Symbol.Terminal ";"; Symbol.Nonterminal 'S'; |]; |]

        Map.empty
        |> Map.add 'P' P
        |> Map.add 'S' S
        |> Map.add 'L' L

    // Augment the grammar.
    Grammar.augment ``Grammar 3.30`` 'P'

/// Grammar 4.6 from "Modern Compiler Implementation in ML".
let ``Grammar 4.6`` =
    let ``Grammar 4.6`` =
        let S =
            [|  [| Symbol.Nonterminal 'S'; Symbol.Terminal ";"; Symbol.Nonterminal 'S'; |];
                [| Symbol.Terminal "id"; Symbol.Terminal ":="; Symbol.Nonterminal 'E'; |];
                [| Symbol.Terminal "print"; Symbol.Nonterminal 'L'; |]; |]

        let E =
            [|  [| Symbol.Terminal "id"; |];
                [| Symbol.Terminal "num"; |];
                [| Symbol.Nonterminal 'E'; Symbol.Nonterminal 'B'; Symbol.Nonterminal 'E'; |];
                [| Symbol.Nonterminal 'S'; Symbol.Terminal ","; Symbol.Nonterminal 'E'; |]; |]

        let L =
            [|  [| (* Empty *) |];
                [| Symbol.Nonterminal 'L'; Symbol.Nonterminal 'E'; |]; |]

        let B =
            [|  [| Symbol.Terminal "+"; |];
                [| Symbol.Terminal "-"; |];
                [| Symbol.Terminal "*"; |];
                [| Symbol.Terminal "/"; |]; |]

        Map.empty
        |> Map.add 'S' S
        |> Map.add 'E' E
        |> Map.add 'L' L
        |> Map.add 'B' B

    // Augment the grammar.
    Grammar.augment ``Grammar 4.6`` 'S'
