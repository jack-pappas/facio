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

open FSharpLex
open FSharpLex.SpecializedCollections
open NUnit.Framework
open FsCheck


/// Tests for the Regex type and module.
module RegexTests =
    [<Test>]
    [<Ignore("This test fails and needs to be fixed; it's ignored for now until I have time to understand why it's failing.")>]
    let ``difference of CharSet regex with itself is the null language`` () : unit =
        // Create a CharacterSet regex for the low ASCII characters.
        let charSetRegex = Regex.CharacterSet (CharSet.ofRange (char 0) (char 127))

        // Take difference of the regex and itself.
        let diff = Regex.Difference (charSetRegex, charSetRegex)

        // The resulting regex should be epsilon (the null language).
        diff
        |> assertEqual Regex.Epsilon


/// Randomized tests for operations on Regex.
[<Ignore("This fixture is ignored for now because the tests cause FsCheck to crash.")>]
[<TestFixture>]
module RegexRandomizedTests =
    [<Test(Description = "Checks that the 'simplify' operation is strongly normalizing; \
        i.e., once a regex is simplified, it can't be simplified further.")>]
    let ``simplify operation is normalizing`` () : unit =
        // If the setup fixture hasn't completed, this test won't work correctly.
        if not ReggieTestSetupFixture.SetupComplete then
            Assert.Ignore "The setup fixture has not finished running."

        assertProp "simplify is strongly normalizing" <| fun regex ->
            // Simplify the regex.
            let simplifiedRegex = Regex.Simplify regex

            // Try to simplify the regex again.
            let doubleSimplifiedRegex = Regex.Simplify simplifiedRegex

            // Check whether the double-simplified regex is the same as the simplified regex.
            simplifiedRegex = doubleSimplifiedRegex

    [<Test>]
    let ``difference of a language and itself is the null language`` () =
        assertProp "difference of a language and itself is the null language" <| fun regex ->
            // Calculate the difference of the regex and itself.
            let diff = Regex.Difference (regex, regex)

            // The difference should be the null language.
            diff = Regex.Epsilon

    [<Test>]
    let ``a language AND-ed with itself then simplified returns the original language`` () =
        assertProp "a language AND-ed with itself then simplified returns the original language" <| fun regex ->
            // AND the langugage with itself, then simplify.
            let result = Regex.andr regex regex

            // Simplify the original regex.
            let simplifiedRegex = Regex.Simplify regex

            // The regex and'ed with itself and simplified should equal the simplified regex.
            simplifiedRegex = result

    [<Test>]
    let ``a language OR-ed with itself then simplified returns the original language`` () =
        assertProp "a language OR-ed with itself then simplified returns the original language" <| fun regex ->
            // OR the langugage with itself, then simplify.
            let result = Regex.orr regex regex

            // Simplify the original regex.
            let simplifiedRegex = Regex.Simplify regex

            // The regex or'ed with itself and simplified should equal the simplified regex.
            simplifiedRegex = result
