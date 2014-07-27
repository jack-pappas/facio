#### 0.8.6-alpha - 2014-Apr-18
* Initial release.

### 0.8.7-alpha - 2014-Jul-19
* Logo was added. (Contribution by @sergey-tihon)
* Site wes added. (Contribution by @sergey-tihon)
* Fixed an issue (#15) where fsharplex and fsharpyacc would crash when run via the build tasks (with MSBuild) when FSharp.Core 4.0.0.0 and/or 4.3.0.0 weren't available on the build machine.
* Removed the Facio.Support.LegacyInterpreters project. The new FsLexYacc.Runtime project is used instead because it includes the same functionality and makes it easy to transition from FsLexYacc to facio.

### 0.8.8-alpha - 2014-Jul-27
* Implemented an optimization in fsharplex's fslex-compatible backend that reduces overall compilation times by up to 25%.

### 0.8.9-alpha - Unreleased
