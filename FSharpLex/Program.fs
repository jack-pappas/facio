(*
Copyright (c) 2012, Jack Pappas
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

    /// Invokes FSharpLex with the specified options.
    [<CompiledName("Invoke")>]
    let invoke (inputFile, options : Compile.CompilationOptions) : int =
        (* TODO :   Validate the compilation options before proceeding further. *)

        /// The parsed lexer specification.
        let lexerSpec =
            try
                let stream, reader, lexbuf =
                    UnicodeFileAsLexbuf (inputFile, None)
                use stream = stream
                use reader = reader
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
        let exitCode =
            let testSpec = FSharpLex.TestSpec.``fslex specification``
            match Compile.lexerSpec lexerSpec options with
            | Choice1Of2 compiledLexerSpec ->
                // TODO : Pass the result to the selected backend.

                let generatedCode = CodeGen.generateString compiledLexerSpec options
                //GraphGen.Dgml.emitSeparate compiledLexerSpec options

                // BREAKPOINT
                let efowei = "weofkwokfwe".Length + 1

                0   // Success
            | Choice2Of2 errorMessages ->
                // Write the error messages to the console.
                // TODO : Write the error messages to NLog (or similar) instead, for flexibility.
                errorMessages
                |> Array.iter (printfn "Error: %s")

                1   // Error

        // TEMP : Don't exit until pressing a key, so we can read any messages printed to the console.
        // This MUST be removed before FSharpYacc can be called from MSBuild, VS, etc.
        printfn ""
        printfn "Press any key to exit..."
        System.Console.ReadKey ()
        |> ignore

        // Return the exit code.
        exitCode

    /// The entry point for the application.
    [<EntryPoint; CompiledName("Main")>]
    let main (options : string[]) =
        (* TODO :   Parse command-line options and use the values to
                    create an instance of the CompilationOptions record,
                    then call the 'invoke' function with it. *)
        
        // TEST : Just use an hard-coded CompilationOptions record for now.
        invoke (@"C:\Users\Jack\Desktop\fsyacc-test\fslexlex.fsl", {
            Unicode = false; })

