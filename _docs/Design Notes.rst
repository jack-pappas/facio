Design Notes
############

Errors/Warnings
===============

- Warn if a token (``fsharplex``) or terminal (``fsharpyacc``) name begins with a lowercase letter.
- (``fsharpyacc``) Warn if a nonterminal name begins with an uppercase letter.


Implement new command-line options
==================================

- ``--nologo``
    Doesn't show the banner text when launching the compiler.

- ``--out:<output-filename>`` / ``-o:<output-filename>``
    Specifies the name of the compiled assembly or module.
    
- ``--times``
    Displays timing information for compilation.
    
- ``--warnon:<int-list>``
    Enable specific warnings that might be off by default or disabled by another command line option. In F# 3.0, only the 1182 (unused variables) warning is off by default.
    
- ``--warnaserror[+|-] [<int-list>]``
    Enables or disables the option to report warnings as errors. You can provide specific warning numbers to be disabled or enabled. Options later in the command line override options earlier in the command line. For example, to specify the warnings that you don't want reported as errors, specify ``--warnaserror+ --warnaserror-:<int-list>``.

