(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpYacc.CodeGen

open System.CodeDom.Compiler
open System.ComponentModel.Composition
open System.IO
open System.Text
open LanguagePrimitives
//open SpecializedCollections
open Ast
//open Compile

(* TODO :   Move the code generator (and any other back-ends we want to create)
            into plugins using the Managed Extensibility Framework (MEF). *)

