(*

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

namespace Tests.Reggie

open Reggie
open Reggie.SpecializedCollections
open NUnit.Framework
open FsCheck


/// Tests for the Regex type and module.
module RegexTests =
    [<Test>]
    let ``difference of CharSet regex with itself is the null language`` () : unit =
        // Create a CharacterSet regex for the low ASCII characters.
        let charSetRegex = Regex.CharacterSet (CharSet.ofRange (char 0) (char 127))

        // Take difference of the regex and itself.
        let diff = Regex.Difference (charSetRegex, charSetRegex)

        // The resulting regex should be the null language.
        diff
        |> assertEqual Regex.empty

    [<Test(Description =
        "Check whether Regex.Simplify terminates for doubly-nested And patterns.")>]
    let ``simplify terminates for doubly-nested And patterns`` () : unit =
        let inputRegex = And (And (Epsilon,Epsilon),And (Epsilon,Epsilon))

        // Try to simplify the input regex.
        let simplifiedRegex = Regex.Simplify inputRegex

        // If Regex.Simplify returned, it didn't get stuck in infinite recursion.
        Assert.Pass ()

    [<Test(Description =
        "Check whether Regex.Simplify terminates for doubly-nested Or patterns.")>]
    let ``simplify terminates for doubly-nested Or patterns`` () : unit =
        let inputRegex = Or (Or (Epsilon,Epsilon),Or (Epsilon,Epsilon))

        // Try to simplify the input regex.
        let simplifiedRegex = Regex.Simplify inputRegex

        // If Regex.Simplify returned, it didn't get stuck in infinite recursion.
        Assert.Pass ()

    [<Test(Description =
        "Test whether the rewrite rules in Regex.Simplify are confluent (at least for nested AND patterns). \
         If they're not this test fails. This test case was discovered using FsCheck.")>]
    let ``simplify works correctly for nested AND patterns with charset and epsilons`` () : unit =
        let inputRegex =
            And (
                CharacterSet (CharSet.ofRange '\u0056' '\u0056'),
                And (Epsilon, Epsilon))

        // The regex should be fully simplified in one pass.
        let simplifiedRegex = Regex.Simplify inputRegex

        // Try to simplify the regex again.
        let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

        // Check whether the double-simplified regex is the same as the simplified regex.
        assertEqual doubleSimplifiedRegex simplifiedRegex

    [<Test>]
    let ``Regex.Simplify test case 001`` () : unit =
        let inputRegex = And (CharacterSet (CharSet.ofRange '\u0037' '\u0037'), And (Epsilon, Concat (Epsilon, Epsilon)))

        // The regex should be fully simplified in one pass.
        let simplifiedRegex = Regex.Simplify inputRegex

        // Try to simplify the regex again.
        let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

        // Check whether the double-simplified regex is the same as the simplified regex.
        assertEqual doubleSimplifiedRegex simplifiedRegex

    [<Test>]
    let ``Regex.Simplify test case 002`` () : unit =
        let inputRegex = And (CharacterSet (CharSet.ofRange '\u0037' '\u0037'), Epsilon)

        // The regex should be fully simplified in one pass.
        let simplifiedRegex = Regex.Simplify inputRegex

        // Try to simplify the regex again.
        let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

        // Check whether the double-simplified regex is the same as the simplified regex.
        assertEqual doubleSimplifiedRegex simplifiedRegex

    [<Test>]
    let ``Regex.Simplify test case 003`` () : unit =
        let inputRegex = Or (Epsilon, Or (Star Epsilon, CharacterSet (CharSet.OfIntervals ([| '\u0042', '\u0042'; '\u004c', '\u004c' |]))))

        // The regex should be fully simplified in one pass.
        let simplifiedRegex = Regex.Simplify inputRegex

        // Try to simplify the regex again.
        let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

        // Check whether the double-simplified regex is the same as the simplified regex.
        assertEqual doubleSimplifiedRegex simplifiedRegex


/// Randomized tests for the Regex type and module.
[<TestFixture>]
module RegexRandomizedTests =
    [<Test(Description = "Checks that the PrintFSharpCode method always succeeds.")>]
    [<Ignore("This test takes a long time to run. Re-enable it after upgrading to FsCheck 2.2.2")>]
    let ``PrintFSharpCode always succeeds`` () : unit =
        assertProp "PrintFSharpCode always succeeds" <| fun regex ->
            // Try to run PrintFSharpCode against any Regex. If it doesn't raise an exception,
            // consider the operation to have succeeded.
            try
                Regex.PrintFSharpCode regex |> ignore
                true
            with ex ->
                stderr.WriteLine ex
                false

    [<Test(Description = "Checks that the 'simplify' operation is strongly normalizing; \
        i.e., once a regex is simplified, it can't be simplified further.")>]
    //[<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``simplify operation is normalizing`` () : unit =
        assertProp "simplify is strongly normalizing" <| fun regex ->
            // Simplify the regex.
            let simplifiedRegex = Regex.Simplify regex

            // Try to simplify the regex again.
            let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

            // Check whether the double-simplified regex is the same as the simplified regex.
            simplifiedRegex = doubleSimplifiedRegex

    [<Test>]
    [<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``difference of a language and itself is the null language`` () =
        assertProp "difference of a language and itself is the null language" <| fun regex ->
            // Calculate the difference of the regex and itself.
            let diff = Regex.Difference (regex, regex)

            // The difference should be the null language.
            diff = Regex.Epsilon

    [<Test>]
    [<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``a language AND-ed with itself then simplified returns the original language`` () =
        assertProp "a language AND-ed with itself then simplified returns the original language" <| fun regex ->
            // AND the langugage with itself, then simplify.
            let result = Regex.andr regex regex

            // Simplify the original regex.
            let simplifiedRegex = Regex.Simplify regex

            // The regex and'ed with itself and simplified should equal the simplified regex.
            simplifiedRegex = result

    [<Test>]
    [<Ignore("This test is a prototype and still needs to be verified against the implementation.")>]
    let ``a language OR-ed with itself then simplified returns the original language`` () =
        assertProp "a language OR-ed with itself then simplified returns the original language" <| fun regex ->
            // OR the langugage with itself, then simplify.
            let result = Regex.orr regex regex

            // Simplify the original regex.
            let simplifiedRegex = Regex.Simplify regex

            // The regex or'ed with itself and simplified should equal the simplified regex.
            simplifiedRegex = result
