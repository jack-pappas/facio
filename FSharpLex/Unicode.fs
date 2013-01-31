(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpLex


/// Maps Unicode categories to sets of characters they contain.
[<RequireQualifiedAccess>]
module internal UnicodeCharSet =
    open System
    open System.Collections.Generic
    open System.Globalization
    open FSharpLex.SpecializedCollections

    /// Maps each UnicodeCategory to the set of characters in the category.
    let byCategory =
        // OPTIMIZE : If this takes "too long" to compute on-the-fly, we could pre-compute
        // the category sets and implement code which recreates the CharSets from the intervals
        // in the CharSets (not the individual values, which would be much slower).
        let table = System.Collections.Generic.Dictionary<_,_> (30)
        for i = 0 to 65535 do
            /// The Unicode category of this character.
            let category = System.Char.GetUnicodeCategory (char i)

            // Add this character to the set for this category.
            table.[category] <-
                match table.TryGetValue category with
                | true, charSet ->
                    CharSet.add (char i) charSet
                | false, _ ->
                    CharSet.singleton (char i)

        // TODO : Assert that the table contains an entry for every UnicodeCategory value.
        // Otherwise, exceptions will be thrown at run-time if we try to retrive non-existent entries.

        // Convert the dictionary to a Map
        (Map.empty, table)
        ||> Seq.fold (fun categoryMap kvp ->
            Map.add kvp.Key kvp.Value categoryMap)

    //
    let ofCategory category =
        Map.tryFind category byCategory

    //
    let private categoryAbbreviations =
        Map.ofArray [|
            "Pe", UnicodeCategory.ClosePunctuation; // (Pe)
            "Pc", UnicodeCategory.ConnectorPunctuation; // (Pc)
            "Cc", UnicodeCategory.Control; // (Cc)
            "Sc", UnicodeCategory.CurrencySymbol; // (Sc)
            "Pd", UnicodeCategory.DashPunctuation; // (Pd)
            "Nd", UnicodeCategory.DecimalDigitNumber; // (Nd)
            "Me", UnicodeCategory.EnclosingMark; // (Me)
            "Pf", UnicodeCategory.FinalQuotePunctuation; // (Pf)
            "Cf", UnicodeCategory.Format; // (Cf)
            "Pi", UnicodeCategory.InitialQuotePunctuation; // (Pi)
            "Nl", UnicodeCategory.LetterNumber; // (Nl)
            "Zl", UnicodeCategory.LineSeparator; // (Zl)
            "Ll", UnicodeCategory.LowercaseLetter; // (Ll)
            "Sm", UnicodeCategory.MathSymbol; // (Sm)
            "Lm", UnicodeCategory.ModifierLetter; // (Lm)
            "Sk", UnicodeCategory.ModifierSymbol; // (Sk)
            "Mn", UnicodeCategory.NonSpacingMark; // (Mn)
            "Ps", UnicodeCategory.OpenPunctuation; // (Ps)
            "Lo", UnicodeCategory.OtherLetter; // (Lo)
            "Cn", UnicodeCategory.OtherNotAssigned; // (Cn)
            "No", UnicodeCategory.OtherNumber; // (No)
            "Po", UnicodeCategory.OtherPunctuation; // (Po)
            "So", UnicodeCategory.OtherSymbol; // (So)
            "Zp", UnicodeCategory.ParagraphSeparator; // (Zp)
            "Co", UnicodeCategory.PrivateUse; // (Co)
            "Zs", UnicodeCategory.SpaceSeparator; // (Zs)
            "Mc", UnicodeCategory.SpacingCombiningMark; // (Mc)
            "Cs", UnicodeCategory.Surrogate; // (Cs)
            "Lt", UnicodeCategory.TitlecaseLetter; // (Lt)
            "Lu", UnicodeCategory.UppercaseLetter; // (Lu)
            |]

    //
    let ofAbbreviation abbrev =
        Map.tryFind abbrev categoryAbbreviations
        |> Option.bind ofCategory