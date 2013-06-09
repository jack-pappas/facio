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


/// Associativity of a terminal (token).
/// This can be explicitly specified to override the
/// default behavior for resolving conflicts.
type Associativity =
    /// Non-associative.
    | NonAssociative
    /// Left-associative.
    | Left
    /// Right-associative.
    | Right

    /// <inherit />
    override this.ToString () =
        match this with
        | NonAssociative ->
            "NonAssociative"
        | Left ->
            "Left"
        | Right ->
            "Right"

/// Tags an integer as denoting an absolute precedence level.
[<Measure>] type AbsolutePrecedenceLevelTag
/// The absolute precedence level of a terminal or production rule.
type AbsolutePrecedenceLevel = int<AbsolutePrecedenceLevelTag>

/// Contains precedence and associativity settings for a grammar,
/// which can be used to resolve conflicts due to grammar ambiguities.
type PrecedenceSettings = {
    //
    RulePrecedence : TagMap<ProductionRuleIndexTag, Associativity * AbsolutePrecedenceLevel>;
    //
    TerminalPrecedence : TagMap<TerminalIndexTag, Associativity * AbsolutePrecedenceLevel>;
} with
    /// Returns an empty PrecedenceSettings instance.
    static member Empty : PrecedenceSettings = {
        RulePrecedence = TagMap.empty;
        TerminalPrecedence = TagMap.empty; }


(* TODO :   Un-comment the RelativePrecedence type whenever we get around to
            implementing the algorithm for creating operator-precedence parsers. *)
(*
//
[<DebuggerDisplay("{DebuggerDisplay,nq}")>]
type RelativePrecedence =
    //
    | LessThan
    //
    | Equal
    //
    | GreaterThan

    //
    member private this.DebuggerDisplay
        with get () =
            match this with
            | LessThan ->
                "\u22d6"
            | Equal ->
                "\u2250"
            | GreaterThan ->
                "\u22d7"

    /// <inherit />
    override this.ToString () =
        match this with
        | LessThan ->
            "LessThan"
        | Equal ->
            "Equal"
        | GreaterThan ->
            "GreaterThan"

    //
    static member Inverse prec =
        match prec with
        | LessThan ->
            GreaterThan
        | Equal ->
            Equal
        | GreaterThan ->
            LessThan
*)

