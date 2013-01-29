(*
Copyright (c) 2012-2013, Jack Pappas
All rights reserved.

This code is provided under the terms of the 2-clause ("Simplified") BSD license.
See LICENSE.TXT for licensing details.
*)

module FSharpLex.Program

//
module internal AssemblyInfo =
    open System.Reflection
    open System.Resources
    open System.Runtime.CompilerServices
    open System.Runtime.InteropServices
    open System.Security
    open System.Security.Permissions

    [<assembly: AssemblyTitle("FSharpLex")>]
    [<assembly: AssemblyDescription("A 'lex'-inspired lexical-analyzer-generator tool for F#.")>]
    [<assembly: NeutralResourcesLanguage("en-US")>]
    [<assembly: Guid("3e878e31-5c9a-456d-9ab8-a12e3fed1efe")>]

    (*  Makes internal modules, types, and functions visible
        to the test project so they can be unit-tested. *)
    #if DEBUG
    [<assembly: InternalsVisibleTo("FSharpLex.Tests")>]
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
    open System.ComponentModel.Composition
    open System.ComponentModel.Composition.Hosting
    open FSharp.CliArgs
    open FSharpLex.Plugin

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

    //
    let private loadBackends () =
        //
        use catalog = new AssemblyCatalog (typeof<Backends>.Assembly)

        //
        use container = new CompositionContainer (catalog)

        //
        let backends = Backends ()
        container.ComposeParts (backends)
        backends

    /// Invokes FSharpLex with the specified options.
    [<CompiledName("Invoke")>]
    let invoke (inputFile, options) : int =
        // Preconditions
        if inputFile = null then
            nullArg "inputFile"
        elif System.String.IsNullOrWhiteSpace inputFile then
            invalidArg "inputFile" "The path to the lexer specification is empty."
        elif not <| System.IO.File.Exists inputFile then
            invalidArg "inputFile" "No lexer specification exists at the specified path."

        // TEMP : This is hard-coded for now, but eventually we'll make it
        // so the user can specify which backend(s) to use.
        /// Compiler backends.
        let backends = loadBackends ()

        /// The parsed lexer specification.
        let lexerSpec =
            try
                let stream, reader, lexbuf =
                    UnicodeFileAsLexbuf (inputFile, None)
                use stream = stream
                use reader = reader
//                let tokens =
//                    let tokens = ResizeArray ()
//                    try
//                        while true do
//                            tokens.Add <| Lexer.token lexbuf
//                    with ex ->
//                        printfn "Error: %s" ex.Message
//                        ()
//                    tokens.ToArray ()
                let lexerSpec = Parser.spec Lexer.token lexbuf

                // TEMP : Some of the lists need to be reversed so they're in the order we expect.
                { lexerSpec with
                    Macros = List.rev lexerSpec.Macros;
                    Rules =
                        lexerSpec.Rules
                        |> List.map (fun (position, rule) ->
                            position,
                            { rule with
                                Clauses = List.rev rule.Clauses; })
                        |> List.rev; }

            with ex ->
                printfn "Error: %s" ex.Message
                exit 1

        // Compile the parsed specification.
        match Compile.lexerSpec lexerSpec options with
        | Choice2Of2 errorMessages ->
            // Write the error messages to the console.
            // TODO : Write the error messages to NLog (or similar) instead, for flexibility.
            errorMessages
            |> Array.iter (printfn "Error: %s")

            1   // Exit code: Error

        | Choice1Of2 compiledLexerSpec ->
            // TEMP : Invoke the various backends "manually".
            // Eventually we'll modify this so the user can specify the backend to use.
            backends.FslexBackend.EmitCompiledSpecification (
                compiledLexerSpec,
                options)

//            backends.GraphBackend.EmitCompiledSpecification (
//                compiledLexerSpec,
//                options)

            0   // Exit code: Success


    

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main (options : string[]) =
        (* TODO :   Parse command-line options and use the values to
                    create an instance of the CompilationOptions record,
                    then call the 'invoke' function with it. *)
        
        // TEST : Just use an hard-coded CompilationOptions record for now.
        invoke (@"C:\Users\Jack\Desktop\fslexlex.fsl", {
            Unicode = true;
            // TEMP
            FslexBackendOptions = Some {
                OutputPath = @"C:\Users\Jack\Desktop\fslex_lexer.fs";
                };
            GraphBackendOptions = Some {
                OutputPath = @"C:\Users\Jack\Desktop\CompiledLexerDfa.dgml";
                Format = GraphFileFormat.Dgml; };
            })

