module BuildLogger
open NLog.Targets
open NLog.Layouts
open NLog
open System.Reflection

let mutable logger = null : Microsoft.Build.Utilities.TaskLoggingHelper
let mutable file = null : string

type MsBuildLogLevel = Info | Warn | Error

type MsBuildLogTarget() =
    inherit Target()
    override this.Write (logEvent : LogEventInfo) =
        let exn =
            match logEvent.Exception with
            | null -> None
            | exn -> Some exn
        
        let level =
            match logEvent.Level with
            | lvl when lvl = LogLevel.Info -> Some Info
            | lvl when lvl = LogLevel.Warn -> Some Warn
            | lvl when lvl = LogLevel.Error -> Some Error
            | lvl when lvl = LogLevel.Fatal -> Some Error
            | _ -> None  

        match exn, level with
        | Some exn, Some Info -> logger.LogMessage exn.Message
        | None, Some Info -> logger.LogMessage logEvent.FormattedMessage
        | Some exn, Some Warn -> logger.LogWarningFromException(exn, true)
        | None, Some Warn -> logger.LogWarning logEvent.FormattedMessage
        | Some exn, Some Error -> logger.LogErrorFromException (exn, true, true, file)
        | None, Some Error -> logger.LogError logEvent.FormattedMessage
        | _, None -> ()
            
do  
    let fsharp =
        System.AppDomain.CurrentDomain.GetAssemblies()
        |> Seq.filter (fun assembly -> assembly.GetName().Name = "FSharp.Core")
        |> Seq.exactlyOne

    System.AppDomain.CurrentDomain.add_AssemblyResolve (fun sender args ->
        match args.Name.Split(',').[0] with
        | "FSharp.Core" -> fsharp            
        | _ -> null
    )

    Config.SimpleConfigurator.ConfigureForTargetLogging (new MsBuildLogTarget())