#I "packages/FAKE/tools/"
#r "FakeLib"

open Fake
open Fake.Git
open Fake.AssemblyInfoHelper
open Fake.ReleaseNotesHelper
open System

let docDir = "./doc"
let resultsDir = "./_build/results"
let docOutputDir = resultsDir @@ "Documentation"
let nugetTemp = "./_build/nugetTemp/"
let authors = [ "Jack Pappas" ]

// Git configuration (used for publishing documentation in gh-pages branch)
// The profile where the project is posted
let gitHome = "https://github.com/jack-pappas"
// The name of the project on GitHub
let gitName = "facio"
// --------------------------------------------------------------------------------------

// Read additional information from the release notes document
Environment.CurrentDirectory <- __SOURCE_DIRECTORY__
let release = parseReleaseNotes (IO.File.ReadAllLines "RELEASE_NOTES.md")

// Generate assembly info files with the right version & up-to-date information
Target "AssemblyInfo" (fun _ ->
    ReplaceAssemblyInfoVersions (fun p ->
        {p with
            OutputFileName = "Common/CommonAssemblyInfo.fs"
            AssemblyVersion = release.AssemblyVersion
            AssemblyFileVersion = release.AssemblyVersion
            AssemblyInformationalVersion = release.AssemblyVersion })
)

// --------------------------------------------------------------------------------------
// Clean build results & restore NuGet packages

Target "RestorePackages" RestorePackages

Target "Clean" (fun _ ->
    CleanDirs [resultsDir; nugetTemp]
)

Target "CleanDocs" (fun _ ->
    CleanDirs ["docs/output"]
)

// --------------------------------------------------------------------------------------
// Build library & test project

Target "Build" (fun _ ->
    !! "/**/*.sln"
    -- "Examples/**/*.sln"
    |> MSBuild resultsDir "Build" ["Configuration", "Testing"]
    |> Log "Build-Output (testing): "

    !! "/**/*.sln"
    -- "Examples/**/*.sln"
    |> MSBuildRelease "" "Build"
    |> Log "Build-Output (nuget): "
)

// --------------------------------------------------------------------------------------
// Run the unit tests using test runner

Target "Tests" (fun _ ->
    !! "/**/*.Tests.dll"
    |> SetBaseDir resultsDir
    |> NUnit (fun p ->
        {p with
            TimeOut  = System.TimeSpan.FromMinutes 10.})
)

// --------------------------------------------------------------------------------------
// Build NuGet package(s)

Target "Facio Nuget" (fun _ ->

    //let grahamInfo = !! @"/**/Graham.nuspec" |> Seq.exactlyOne
    //let grahamInfo = (ReadFileAsString >> getNuspecProperties) grahamInfo

    let facioNuget = !! "/**/Facio.nuspec" |> Seq.exactlyOne

    //let nugetVersion = grahamInfo.Version
    let workingDir = nugetTemp @@ (filenameWithouExt facioNuget)

    ensureDirectory (workingDir @@ "build")
    ensureDirectory (workingDir @@ "lib" @@ "net40")

    !! "/**/Facio.BuildTasks/bin/Release/*.dll"
    ++ "/**/Facio.BuildTasks/bin/Release/*.exe"
    ++ "/**/Facio.BuildTasks/bin/Release/*.config"
    ++ "/**/fsharp*.exe.config"
    |> CopyFiles (workingDir @@ "build")

    !! "/**/bin/Release/Facio.targets"
    |> CopyFiles (workingDir @@ "build")

    facioNuget
    |> NuGet (fun p ->
        { p with
            Authors = authors
            WorkingDir = workingDir
            OutputPath = resultsDir
            Version = release.NugetVersion
            ReleaseNotes = String.Join(Environment.NewLine, release.Notes)
            Files = ["**/*", None, Some "*.nuspec"]
            Dependencies =
                [ "FsLexYacc.Runtime", "6.0.2" ]
            })
)

// --------------------------------------------------------------------------------------
// Generate the documentation

Target "GenerateDocs" (fun _ ->
    executeFSIWithArgs "docs/tools" "generate.fsx" ["--define:RELEASE"] [] |> ignore
)

// --------------------------------------------------------------------------------------
// Release Scripts

Target "ReleaseDocs" (fun _ ->
    let tempDocsDir = "temp/gh-pages"
    CleanDir tempDocsDir
    Repository.cloneSingleBranch "" (gitHome + "/" + gitName + ".git") "gh-pages" tempDocsDir

    fullclean tempDocsDir
    CopyRecursive "docs/output" tempDocsDir true |> tracefn "%A"
    StageAll tempDocsDir
    Commit tempDocsDir (sprintf "Update generated documentation for version %s" release.NugetVersion)
    Branches.push tempDocsDir
)

Target "Release" DoNothing

// --------------------------------------------------------------------------------------
// Run all targets by default. Invoke 'build <Target>' to override

Target "All" DoNothing

"Clean"
    ==> "RestorePackages"
    ==> "AssemblyInfo"
    ==> "Build"
    =?> ("Tests", not <| hasBuildParam "NoTests")
    ==> "All"

"All"
    ==> "CleanDocs"
    ==> "GenerateDocs"
    ==> "ReleaseDocs"
    ==> "Facio Nuget"
    ==> "Release"

RunTargetOrDefault "All"