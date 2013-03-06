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

/// Internal helper classes for implementing unit tests.
module internal Graham.Tests.TestHelpers


/// Helper class that provides generic "overloads" of some Assert methods.
[<AbstractClass; Sealed>]
type Assert =
    /// <summary>Verifies that two values are equal.
    /// If they are not, then an NUnit.Framework.AssertException is thrown.</summary>
    /// <param name="expected">The expected value.</param>
    /// <param name="actual">The actual value.</param>
    static member AreEqual<'T when 'T : equality> (expected : 'T, actual : 'T) : unit =
        NUnit.Framework.Assert.AreEqual (expected, actual)


