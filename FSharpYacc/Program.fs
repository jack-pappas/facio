(*
Copyright (c) 2012, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

namespace FSharpYacc

/// Assembly-level attributes specific to this assembly.
module private AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpYacc")>]
    [<assembly: AssemblyDescription("A 'yacc'-inspired parser-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("fc309105-ce95-46d1-8cb4-568fc6bea85c")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpYacc.Tests")>]
    #endif

    (* Dependency hints for Ngen *)
    [<assembly: DependencyAttribute("FSharp.Core", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System", LoadHint.Always)>]
    [<assembly: DependencyAttribute("System.ComponentModel.Composition", LoadHint.Always)>]

    // Appease the F# compiler
    do ()


//
[<RequireQualifiedAccess>]
module Program =
    (* TEMP : This code is taken from the F# Powerpack, and is licensed under the Apache 2.0 license *)
    open System.IO
    open Microsoft.FSharp.Text.Lexing
    //------------------------------------------------------------------
    // This code is duplicated from Microsoft.FSharp.Compiler.UnicodeLexing

    type private Lexbuf =  LexBuffer<char>

    /// Standard utility to create a Unicode LexBuffer
    ///
    /// One small annoyance is that LexBuffers and not IDisposable. This means
    /// we can't just return the LexBuffer object, since the file it wraps wouldn't
    /// get closed when we're finished with the LexBuffer. Hence we return the stream,
    /// the reader and the LexBuffer. The caller should dispose the first two when done.
    let private UnicodeFileAsLexbuf (filename, codePage : int option) : FileStream * StreamReader * Lexbuf =
        // Use the .NET functionality to auto-detect the unicode encoding
        // It also uses Lexing.from_text_reader to present the bytes read to the lexer in UTF8 decoded form
        let stream = new FileStream (filename, FileMode.Open, FileAccess.Read, FileShare.Read)
        let reader =
            match codePage with
            | None ->
                new StreamReader (stream, true)
            | Some n ->
                new StreamReader (stream, System.Text.Encoding.GetEncoding n)
        let lexbuf = LexBuffer.FromFunction reader.Read
        lexbuf.EndPos <- Position.FirstLine filename
        stream, reader, lexbuf
    (* End-TEMP *)

    /// Invokes FSharpYacc with the specified options.
    [<CompiledName("Invoke")>]
    let invoke (options : CompilationOptions) : int =
        (* TODO :   Validate the compilation options before proceeding further. *)
        //

        let parserSpec =
            try
                let stream, reader, lexbuf =
                    UnicodeFileAsLexbuf (options.InputFile, None)
                use stream = stream
                use reader = reader
                let parserSpec = Parser.spec Lexer.token lexbuf

                // TEMP : Need to do a little massaging of the Specification for now to put some lists in the correct order.
                { parserSpec with
                    TerminalDeclarations =
                        parserSpec.TerminalDeclarations
                        |> List.map (fun (declaredType, terminals) ->
                            declaredType, List.rev terminals);
                    Productions =
                        parserSpec.Productions
                        |> List.map (fun (nonterminal, rules) ->
                            nonterminal,
                            rules
                            |> List.map (fun rule ->
                                { rule with
                                    Symbols = List.rev rule.Symbols; })
                            |> List.rev)
                        |> List.rev; }

            with ex ->
                printfn "Error: %s" ex.Message
                exit 1

        // Compile the parsed specification.
        match Compiler.compile (parserSpec, options) with
        | Choice2Of2 errorMessages ->
            // Write the error messages to the console.
            // TODO : Write the error messages to NLog (or similar) instead, for flexibility.
            errorMessages
            |> List.iter (printfn "Error: %s")

            1   // Exit code: Error

        | Choice1Of2 (parserTable, warningMessages) ->
            // TODO : Pass the result to the selected backend.

            // BREAKPOINT
            let efowei = "weofkwokfwe".Length + 1

            0   // Exit code: Success

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main (options : string[]) =
        (* TODO :   Parse command-line options and use the values to
                    create an instance of the CompilationOptions record,
                    then call the 'invoke' function with it. *)
        
        // TEST : Just use an hard-coded CompilationOptions record for now.
        invoke {
            InputFile = @"C:\Users\Jack\Desktop\fsyacc-test\fslexpars.fsy"; }
        

        
