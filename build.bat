@echo off
cls
".nuget\nuget.exe" "install" ".nuget\packages.config" "-OutputDirectory" "packages" "-ExcludeVersion"
"packages\FAKE\tools\Fake.exe" build.fsx Default %1
pause