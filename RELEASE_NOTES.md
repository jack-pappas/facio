#### 0.8.6-alpha - April 18 2014
* Initial release

### 0.8.7-alpha - Unreleased
* Logo was added
* Site wes added
* Fixed an issue (#15) where fsharplex and fsharpyacc would crash when run via the build tasks (with MSBuild) when FSharp.Core 4.0.0.0 and/or 4.3.0.0 weren't available on the build machine.
* Removed the Facio.Support.LegacyInterpreters project. The new FsLexYacc.Runtime project is used instead because it includes the same functionality and makes it easy to transition from FsLexYacc to facio.
