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

open Graham


/// Expression grammar used for testing ambiguity resolution.
/// This grammar is not LR(k) for any value of 'k', but can be treated as
/// an LR(k) grammar through the use of associativity/precedence declarations.
let ambiguousExpression : AugmentedTaggedGrammar<_,_,unit> =
    let ambiguousExpression : Grammar<string, char> =
        let number : ProductionRule<string, char>[] =
            [| for i in '0' .. '9' do yield [| Symbol.Terminal i |] |]

        let exp : ProductionRule<string, char>[] =
            [|  [| Symbol.Nonterminal "exp"; Symbol.Terminal '+'; Symbol.Nonterminal "exp" |];
                [| Symbol.Nonterminal "exp"; Symbol.Terminal '-'; Symbol.Nonterminal "exp" |];
                [| Symbol.Nonterminal "exp"; Symbol.Terminal '*'; Symbol.Nonterminal "exp" |];
                [| Symbol.Nonterminal "exp"; Symbol.Terminal '/'; Symbol.Nonterminal "exp" |];
                [| Symbol.Nonterminal "number" |];
                [| Symbol.Terminal '('; Symbol.Nonterminal "exp"; Symbol.Terminal ')' |];
                [| Symbol.Nonterminal "exp"; Symbol.Terminal '^'; Symbol.Nonterminal "exp" |];
                [| Symbol.Nonterminal "exp"; Symbol.Terminal '='; Symbol.Nonterminal "exp" |];
                [| Symbol.Terminal '!'; Symbol.Nonterminal "exp" |]; |]

        Map.empty
        |> Map.add "number" number
        |> Map.add "exp" exp

    // Tag, then augment the grammar.
    let taggedGrammar = TaggedGrammar.ofGrammar ambiguousExpression
    AugmentedTaggedGrammar.augment taggedGrammar "exp"


