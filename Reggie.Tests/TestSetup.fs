(*

Copyright 2013-2015 Jack Pappas

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

namespace Tests.FSharpLex.SpecializedCollections

open FSharpLex.SpecializedCollections
open NUnit.Framework
open FsUnit
open FsCheck


/// FsCheck generators for CharSet.
type CharSetGenerator =
    /// Generates an arbitrary char value.
    /// FsCheck includes a generator for char but it's limited to ASCII characters
    /// only and we need the full range here for good test coverage.
    static member UnicodeChar () : Arbitrary<char> =
        gen {
        let! x = Arb.generate<int16>
        return char x
        } |> Arb.fromGen

    /// Generates an arbitrary CharSet instance.
    static member CharSet () : Arbitrary<CharSet> =
        gen {
        let! chars = Arb.generate
        return CharSet.ofSeq chars
        } |> Arb.fromGen


/// NUnit setup fixture.
/// This class provides functionality which NUnit uses to perform one-time initialization
/// for this test assembly before any tests are run.
/// The initialization performed by this class is used to register instances of some FsCheck
/// generators used by multiple test fixtures.
[<SetUpFixture>]
[<Sealed>]
type FSharpLexTestSetupFixture () =
    //
    [<SetUp>]
    member __.SetUp () =
        // Register FsCheck generators needed for CharSet tests.
        Arb.register<CharSetGenerator> () |> ignore
