(*

Copyright 2014 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

namespace Facio.BuildTasks

open NLog
open NLog.Targets
open NLog.Layouts
open Microsoft.Build.Utilities


//
type MsBuildLogLevel = Info | Warn | Error

/// <summary>
/// NLog target which wraps a <see cref="T:Microsoft.Build.Utilities.TaskLoggingHelper"/> instance to emit MSBuild-style messages.
/// </summary>
[<Sealed>]
type internal MSBuildLogTarget (logger : TaskLoggingHelper, inputFile) =
    inherit Target ()

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
        | Some exn, Some Error -> logger.LogErrorFromException (exn, true, true, inputFile)
        | None, Some Error -> logger.LogError logEvent.FormattedMessage
        | _, None -> ()
