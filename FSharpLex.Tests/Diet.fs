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

/// Tests for the balanced DIET (Discrete Interval Encoding Tree).
module Tests.FSharpLex.SpecializedCollections

open FSharpLex.SpecializedCollections
open NUnit.Framework
open FsUnit
open FsCheck

(* TODO :   Modify these tests to use CharSet instead of CharDiet.
            Change the CharDiet type abbreviation and module back to 'private'.
            Remove any tests for CharDiet which don't have a corresponding method in CharSet. *)

[<TestCase>]
let dummy () : unit =
    Assert.Inconclusive "Test not yet implemented."


// Tests for CharDiet:
// find_del_left
// find_del_right
// isEmpty
// contains
// maxElement
// minElement
// bounds
// comparison
// equal
// count
// intervalCount
// singleton
// ofRange
// add
// addRange
// remove
// union
// intersect
// difference
// fold
// foldBack
// iter
// forall
// exists
// toSeq
// toList
// toArray
// toSet

// Tests for CharSet
// ofSeq
// ofList
// ofArray
// ofSet
