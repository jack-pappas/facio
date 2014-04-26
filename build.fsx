#I "packages/FAKE/tools/"
#r "FakeLib"

open Fake

let docDir = "./doc"
let resultsDir = "./results"
let docOutputDir = resultsDir @@ "Documentation"
let nugetTemp = "./nugetTemp/"

Target "Clean" (fun _ -> 
    CleanDirs [resultsDir; nugetTemp]
)

Target "Build" (fun _ ->
    !! "/**/*.sln"
    |> MSBuild resultsDir "Build" ["Configuration", "Testing"]
    |> Log "Build-Output (testing): "

    !! "/**/*.sln"
    |> MSBuildRelease "" "Build"
    |> Log "Build-Output (nuget): "
)

Target "Facio Nuget" (fun _ ->
    
    let grahamInfo = !! @"/**/Graham.nuspec" |> Seq.exactlyOne
    let grahamInfo = (ReadFileAsString >> getNuspecProperties) grahamInfo
    
    let fsharpToolsNuget = !! "/**/Facio.nuspec" |> Seq.exactlyOne
    
    let nugetVersion = grahamInfo.Version
    let workingDir = nugetTemp @@ (filenameWithouExt fsharpToolsNuget)
    
    ensureDirectory (workingDir @@ "build")
    ensureDirectory (workingDir @@ "lib" @@ "net40")
    
    !! "/**/Facio.BuildTasks/bin/Release/*.dll"
    ++ "/**/Facio.BuildTasks/bin/Release/*.exe"
    ++ "/**/Facio.BuildTasks/bin/Release/*.config"
    ++ "/**/fsharp*.exe.config"
    |> CopyFiles (workingDir @@ "build")

    !! "/**/bin/Release/Facio.targets"
    |> CopyFiles (workingDir @@ "build")
    
    !! "/**/LegacyInterpreters/bin/Release/*.*"
    -- "/**/FSharp.Core.*"
    |> CopyFiles (workingDir @@ "lib" @@ "net40")

    NuGet (fun p -> 
        { p with
            WorkingDir = workingDir
            OutputPath = resultsDir
            Version = grahamInfo.Version
            Files = ["**/*", None, Some "*.nuspec"] })
        fsharpToolsNuget
)

Target "Tests" (fun _ ->
    !! "/**/*.Tests.dll"
    |> SetBaseDir resultsDir
    |> NUnit id
)

Target "Default" DoNothing

"Clean"
    ==> "Build"
    =?> ("Tests", not <| hasBuildParam "NoTests")
    ==> "Facio Nuget"
    ==> "Default"

RunTargetOrDefault "Default"