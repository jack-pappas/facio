﻿(*

Copyright 2013-2014 Jack Pappas

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

/// Helper functions for implementing unit tests.
[<AutoOpen>]
module TestHelpers

open System
open System.Collections.Generic
open NUnit.Framework
open FsCheck


(* Fluent test helpers for use with NUnit and FsUnit. *)

/// Tests that the specified condition is true.
/// If not, calls Assert.Fail with a formatted string.
let inline assertf (condition : bool) format : 'T =
    Printf.ksprintf (fun str -> if not condition then Assert.Fail str) format

/// Asserts that two values are equal.
let inline assertEqual<'T when 'T : equality> (expected : 'T) (actual : 'T) =
    Assert.AreEqual (expected, actual)

/// Asserts that two values are NOT equal.
let inline assertNotEqual<'T when 'T : equality> (expected : 'T) (actual : 'T) =
    Assert.AreNotEqual (expected, actual)

/// Asserts that two objects are identical.
let inline assertSame<'T when 'T : not struct> (expected : 'T) (actual : 'T) =
    Assert.AreSame (expected, actual)

/// Asserts that two objects are NOT identical.
let inline assertNotSame<'T when 'T : not struct> (expected : 'T) (actual : 'T) =
    Assert.AreNotSame (expected, actual)

/// Asserts that a condition is true.
let inline assertTrue condition =
    Assert.IsTrue (condition)

/// Asserts that a condition is false.
let inline assertFalse condition =
    Assert.IsFalse (condition)


/// Assertion functions for collections.
[<RequireQualifiedAccess>]
module Collection =
    open System.Collections

    /// Asserts that two collections are exactly equal.
    /// The collections must have the same count, and contain the exact same objects in the same order.
    let inline assertEqual<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreEqual (expected, actual)

    /// Asserts that two collections are not exactly equal.
    let inline assertNotEqual<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreNotEqual (expected, actual)

    /// Asserts that two collections are exactly equal.
    /// The collections must have the same count, and contain the exact same objects but the match may be in any order.
    let inline assertEquiv<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreEquivalent (expected, actual)

    /// Asserts that two collections are not exactly equal.
    let inline assertNotEquiv<'T, 'U when 'T :> seq<'U>> (expected : 'T) (actual : 'T) =
        CollectionAssert.AreNotEquivalent (expected, actual)


(* Fluent test helpers for use with NUnit and FsCheck. *)

/// An FsCheck runner which reports FsCheck test results to NUnit.
type private NUnitRunner () =
    interface IRunner with
        member x.OnStartFixture _ = ()
        member x.OnArguments (_,_,_) = ()
        member x.OnShrink (_,_) = ()
        member x.OnFinished (name, result) =
            match result with
            | TestResult.True data ->
                // TODO : Log the result data.
                Runner.onFinishedToString name result
                |> stdout.WriteLine

            | TestResult.Exhausted data ->
                // TODO : Log the result data.
                Runner.onFinishedToString name result
                |> Assert.Inconclusive

            | TestResult.False (_,_,_,_,_) ->
                // TODO : Log more information about the test failure.
                Runner.onFinishedToString name result
                |> Assert.Fail

/// An FsCheck configuration which logs test results to NUnit.
let private nUnitConfig = {
    // Config.Verbose
    Config.Quick with
        MaxTest = 5000;
        Runner = NUnitRunner (); }

/// Tests that the specified property is correct.
let assertProp testName (property : 'Testable) =
    Check.One (testName, nUnitConfig, property)
