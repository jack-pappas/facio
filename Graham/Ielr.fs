(*

Copyright 2013 Jack Pappas

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

namespace Graham.Analysis

open Graham


/// Computed tables used in the IELR(1) algorithm.
type IelrTables<'Nonterminal, 'Terminal, 'Lookahead
    when 'Nonterminal : comparison
    and 'Terminal : comparison
    and 'Lookahead : comparison> = {
    /// Records dependencies of GOTO follow sets on kernel item lookahead sets.
    follow_kernel_items : Map<unit, unit>;
    /// Records GOTO follow tokens that do not depend on the kernel item lookahead
    /// sets of predecessor states. That is, this table records GOTO follows that
    /// will never change no matter how IELR(1) may split the LALR(1) parse states.
    always_follows : Map<unit, unit>;
    /// Records transition predecessor relations between LALR(1) states.
    predecessors : Map<unit, unit>;
}


