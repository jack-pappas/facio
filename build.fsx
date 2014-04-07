#I "packages/FAKE/tools/"
#r "FakeLib"

open Fake

let docDir = "./doc"
let resultsDir = "./results"
let docOutputDir = resultsDir @@ "Documentation"

Target "Clean" (fun _ -> 
    CleanDir resultsDir
)

Target "Build" (fun _ ->
    !! "/**/*.sln"
    |> MSBuildRelease resultsDir "Build"
    |> Log "Build-Output: "
)

Target "Tests" DoNothing // TODO: implement something meaningful

Target "Default" DoNothing

"Clean"
    ==> "Build"
    =?> ("Tests", not <| hasBuildParam "NoTests")
    ==> "Default"

RunTargetOrDefault "Default"