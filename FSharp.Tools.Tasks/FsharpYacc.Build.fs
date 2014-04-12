// (c) Microsoft Corporation 2005-2009.

namespace FSharp.Tools.Tasks

open System
open Microsoft.Build.Framework
open Microsoft.Build.Utilities

(**************************************
MSBuild task for fsharpyacc

fsharpyacc <filename>
        -o <string>: The path where the output file will be written.
        -v: Produce a listing file.
        --module <string>: The name to use for the F# module containing the generated parser. The default is 'Parser'.
        --internal: Generate an internal module
        --open <string>: Add the given module to the list of those to open in both the generated signature and implementation.
        --lexlib <string>: Specify the namespace for the implementation of the lexer table interpreter. The default is 'Microsoft.FSharp.Text.Lexing'.
        --parslib <string>: Specify the namespace for the implementation of the parser table interpreter. The default is 'Microsoft.FSharp.Text.Parsing'.
        --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
        --help: display this list of options
        -help: display this list of options
**************************************)

type FSharpYacc() = 
    inherit Task()
    
    [<Required>]
    member val InputFile = null : string with get, set
    
    [<Output>]
    member val OutputFile = null : string with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = null : string with get, set

    member val LexLib = null : string with get, set

    member val ParsLib = null : string with get, set

    // --open
    member val Open = [| |] : string [] with get, set

    // --module
    member val Module = null : string with get, set

    member val Verbose = false with get, set

    member val Internal = false with get, set
        
    override this.Execute() =
        BuildLogger.logger <- this.Log
        BuildLogger.file <- this.InputFile

        FSharpYacc.Program.createListing := this.Verbose
        FSharpYacc.Program.internalModule := this.Internal
        FSharpYacc.Program.inputCodePage := 
            match Int32.TryParse this.CodePage with
            | true, codePage -> Some codePage 
            | _ -> None
        FSharpYacc.Program.openDeclarations.Clear()
        Array.iter FSharpYacc.Program.openDeclarations.Add this.Open
        let toOption x = if x = null then None else Some x
        FSharpYacc.Program.lexerInterpreterNamespace := toOption this.LexLib
        FSharpYacc.Program.parserInterpreterNamespace := toOption this.ParsLib
        FSharpYacc.Program.generatedModuleName := toOption this.Module
        FSharpYacc.Program.outputPath := toOption this.OutputFile
        FSharpYacc.Program.inputFile := toOption this.InputFile
        
        FSharpYacc.Program.main [| |] = 0