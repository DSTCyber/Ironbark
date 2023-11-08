(*Copyright (C) 2023 Commonwealth of Australia
  Micah Brown
  Brendan Mahony
  Jim McCarthy

This file is part of Ironbark.

This program is free software: you can redistribute it and/or modify it under the terms of 
the GNU General Public License as published by the Free Software Foundation, either 
version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; 
without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR 
PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program. If not, see <https://www.gnu.org/licenses/>.*)

subsection \<open>Properties of the Processor State Definition\<close>

theory state_auxiliary

imports
  state_implementations

begin

text \<open>We provide a trivial proof here that shows that two states can be shown to be 
equivalent if all of the components that make up the state are the same. This is used 
in future proofs to attack larger problems in a `piecemeal' fashion.\<close>

lemma sequential_state_equality:
  fixes 
    state1 state2 :: \<open>sequential_state\<close>
  assumes
    \<open>flag_state     state1 = flag_state     state2\<close>
    \<open>register_state state1 = register_state state2\<close>
    \<open>program_memory state1 = program_memory state2\<close>
    \<open>call_memory    state1 = call_memory    state2\<close>
    \<open>static_memory  state1 = static_memory  state2\<close>
    \<open>dynamic_memory state1 = dynamic_memory state2\<close>
    \<open>input_memory   state1 = input_memory   state2\<close>
    \<open>output_memory  state1 = output_memory  state2\<close>
  shows
    \<open>state1 = state2\<close>
  using assms
  by(simp)

end