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

type FsharpYacc() as this = 
    inherit ToolTask()
    do this.StandardOutputImportance <- "Normal"

    static member val logger = null with get, set
    
    [<Required>]
    member val InputFile = null : string with get, set
    
    [<Output>]
    member val OutputFile = null : string with get, set
    
    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = null : string with get, set

    member val LexLib = null : string with get, set

    member val ParsLib = null : string with get, set

    // --open
    member val Open = null : string with get, set

    // --module
    member val Module = null : string with get, set

    member val Verbose = false with get, set

    member val Internal = false with get, set

    // ToolTask methods
    override this.ToolName = "fsharpyacc.exe"
    
    override this.GenerateFullPathToTool() = System.IO.Path.Combine(this.ToolPath, this.ToolExe)
        
    override this.Execute() =
        BuildLogger.logger <- this.Log
        base.Execute()

    override this.GenerateCommandLineCommands() =
        let builder = new CommandLineBuilder()

        // Verbose
        if this.Verbose then builder.AppendSwitch("-v")
        
        // Internal
        if this.Internal then builder.AppendSwitch("--internal")
        
        // CodePage
        builder.AppendSwitchIfNotNull("--codepage ", this.CodePage)
        
        // Open
        builder.AppendSwitchIfNotNull("--open ", this.Open)

        // LexLib
        builder.AppendSwitchIfNotNull("--lexlib ", this.LexLib)

        // LexLib
        builder.AppendSwitchIfNotNull("--parslib ", this.ParsLib)

        // Module
        builder.AppendSwitchIfNotNull("--module ", this.Module)

        // OutputFile
        builder.AppendSwitchIfNotNull("-o ", this.OutputFile)

        builder.AppendSwitchIfNotNull(" ", this.InputFile)
        
        let args = builder.ToString()

        this.BuildEngine.LogCustomEvent { new CustomBuildEventArgs(message=args,helpKeyword="",senderName="") with member x.Equals(y) = false }
                            
        args