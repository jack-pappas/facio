(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

//
module FSharpLex.GraphGen

open System.ComponentModel.Composition
open System.IO
//open System.Xml
open SpecializedCollections
open Ast
open Compile

// TODO : Implement back-ends which generate graph output, e.g., for debugging and presentation.
// DGML (for Visual Studio)
// dot (for graphviz)
