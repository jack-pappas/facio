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

Target "FSharp.Tools Nuget" (fun _ ->
    
    let grahamInfo = !! @"C:\Users\Daniel\git\incube\credit-suisse\fsharp-tools/graham.nuspec" |> Seq.exactlyOne
    let grahamInfo = (ReadFileAsString >> getNuspecProperties) grahamInfo
    
    let fsharpToolsNuget = !! "/**/Fsharp.Tools.nuspec" |> Seq.exactlyOne
    
    let nugetVersion = grahamInfo.Version
    let workingDir = nugetTemp @@ (filenameWithouExt fsharpToolsNuget)
    
    ensureDirectory (workingDir @@ "lib" @@ "net40")
    ensureDirectory (workingDir @@ "build")
    
    !! "/**/FSharp.Tools.Tasks/bin/Release/*.dll"
    ++ "/**/FSharp.Tools.Tasks/bin/Release/*.exe"
    ++ "/**/FSharp.Tools.Tasks/bin/Release/*.config"
    |> CopyFiles (workingDir @@ "lib" @@ "net40")

    !! "/**/bin/Release/FSharp.Tools.targets"
    |> CopyFiles (workingDir @@ "build")
    

    NuGet (fun p -> 
        { p with
            WorkingDir = workingDir
            OutputPath = resultsDir
            Version = grahamInfo.Version })
        fsharpToolsNuget
)

Target "Tests" DoNothing // TODO: implement something meaningful

Target "Default" DoNothing

"Clean"
    ==> "Build"
    =?> ("Tests", not <| hasBuildParam "NoTests")
    ==> "FSharp.Tools Nuget"
    ==> "Default"

RunTargetOrDefault "Default"