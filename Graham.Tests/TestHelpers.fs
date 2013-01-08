(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
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


