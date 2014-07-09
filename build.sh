mono .nuget/NuGet.exe install .nuget/packages.config -OutputDirectory packages -ExcludeVersion

mono packages/FAKE/tools/FAKE.exe build.fsx All $1
