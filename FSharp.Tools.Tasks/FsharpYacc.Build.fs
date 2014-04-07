// (c) Microsoft Corporation 2005-2009.

namespace Microsoft.FSharp.Build

open System
open Microsoft.Build.Framework
open Microsoft.Build.Utilities

(**************************************
MSBuild task for fsharpyacc
**************************************)

type FsharpYacc() = 
    inherit ToolTask()
    // [<Required>]
    member val InputFile = "" with get, set
    
    [<Microsoft.Build.Framework.Output>]
    member val OutputFile = "" with get, set
    
    member val OtherFlags = "" with get, set

    // --codepage <int>: Assume input lexer specification file is encoded with the given codepage.
    member val CodePage = "" with get, set

    // --ml-compatibility: Support the use of the global state from the 'Parsing' module in MLLib.
    member val MLCompatibility = false with get, set
        
    // --open
    member val Open = "" with get, set

   // --module
    member val Module = "" with get, set

    // ToolTask methods
    override this.ToolName = "fsyacc.exe"
    
    override this.GenerateFullPathToTool() = System.IO.Path.Combine(this.ToolPath, this.ToolExe)
        
    override this.GenerateCommandLineCommands() =
    
        let builder = new CommandLineBuilder()
        
        // CodePage
        builder.AppendSwitchIfNotNull("--codepage ", this.CodePage)
        
        // ML Compatibility
        if this.MLCompatibility then builder.AppendSwitch("--ml-compatibility")

        // Open
        builder.AppendSwitchIfNotNull("--open ", this.Open)

        // Module
        builder.AppendSwitchIfNotNull("--module ", this.Module)

        // OutputFile
        builder.AppendSwitchIfNotNull("-o ", this.OutputFile)

        // OtherFlags - must be second-to-last
        builder.AppendSwitchUnquotedIfNotNull("", this.OtherFlags)

        builder.AppendSwitchIfNotNull(" ", this.InputFile)
        
        let args = builder.ToString()

        // when doing simple unit tests using API, no BuildEnginer/Logger is attached
        if this.BuildEngine <> null then
            let eventArgs = { new CustomBuildEventArgs(message=args,helpKeyword="",senderName="") with member x.Equals(y) = false }
            this.BuildEngine.LogCustomEvent(eventArgs)
        
        args