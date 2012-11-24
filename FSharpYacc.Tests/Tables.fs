(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpYacc.Tests.Tables

open Grammars

open NUnit.Framework
open FsUnit

open FSharpYacc
open Predictive
open Tables


        
// TEST
let ``LR(0) table for Grammar 3.20`` =
    Tables.Lr0.createTable grammar_3_20


let ``LR(0) table for Grammar 3.23`` =
    Tables.Lr0.createTable grammar_3_23

let ``SLR table for Grammar 3.23`` =
    Tables.Slr.createTable grammar_3_23

