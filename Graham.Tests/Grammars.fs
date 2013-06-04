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

/// Miscellaneous grammars for testing purposes.
module Tests.Graham.Grammars.Misc

open Graham.Grammar


/// Expression grammar used for testing ambiguity resolution.
/// This grammar is not LR(k) for any value of 'k', but can be treated as
/// an LR(k) grammar through the use of associativity/precedence declarations.
let ambiguousExpression =
    let ambiguousExpression =
        let number =
            [| for i in '0' .. '9' do yield [| Terminal i |] |]

        let exp =
            [|  [| Nonterminal "exp"; Terminal '+'; Nonterminal "exp" |];
                [| Nonterminal "exp"; Terminal '-'; Nonterminal "exp" |];
                [| Nonterminal "exp"; Terminal '*'; Nonterminal "exp" |];
                [| Nonterminal "exp"; Terminal '/'; Nonterminal "exp" |];
                [| Nonterminal "number" |];
                [| Terminal '('; Nonterminal "exp"; Terminal ')' |];
                [| Nonterminal "exp"; Terminal '^'; Nonterminal "exp" |];
                [| Nonterminal "exp"; Terminal '='; Nonterminal "exp" |];
                [| Terminal '!'; Nonterminal "exp" |]; |]

        let productions =
            Map.empty
            |> Map.add "number" number
            |> Map.add "exp" exp

        let nonterminals, terminals =
            Grammar.SymbolSets productions

        {   Terminals = terminals;
            Nonterminals = nonterminals;
            Productions = productions; }

    // Augment the grammar.
    Grammar.Augment (ambiguousExpression, "exp")

