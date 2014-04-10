module BuildLogger
open NLog.Targets
open NLog.Layouts
open NLog
open System.Reflection

type Marker() = class end
    
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

    let methodCallTarget = new MethodCallTarget()
    methodCallTarget.ClassName <- typeof<Marker>.DeclaringType.AssemblyQualifiedName
    methodCallTarget.MethodName <- "log"
    methodCallTarget.Parameters.Add(MethodCallParameter(Layout.FromString "${level}"))
    methodCallTarget.Parameters.Add(MethodCallParameter(Layout.FromString "${message}"))
    Config.SimpleConfigurator.ConfigureForTargetLogging methodCallTarget

let mutable logger = null : Microsoft.Build.Utilities.TaskLoggingHelper

let log level message =
    match level with
    | "Error" -> logger.LogError message
    | "Info" -> logger.LogMessage message
    | "Warn" -> logger.LogWarning message
    | level -> logger.LogError (sprintf "unknown level: %s\nmessage: %s" level message)
