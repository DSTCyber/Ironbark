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

subsection \<open>Properties of State Manipulation Definitions\<close>

theory state_manipulation_auxiliary

imports
  "Ironbark_state.state_top"
  state_manipulation_implementations

begin

text \<open>We provide a trivial proof here that the 8-bit opcode for any instruction will be less than or
equal to 255. This is obvious from the fact that it is the maximum value that can be stored in an
8-bit integer.\<close>

lemma opcode_bound:
  \<open>get_opcode instruction \<le> 255\<close>
  by (unat_arith, auto)

text \<open>We also provide a trivial proof here that if the underlying memory is the same, then a read
from that memory space will give the same result. This is not included in the simplification rules
as it tends to cause the simplifier to get stuck in an infinite loop.\<close>

lemma (in Ironbark_world) same_memory_same_addr:
  shows
    \<open>program_memory state1 = program_memory state2
      \<Longrightarrow> read_program_memory addr state1 = read_program_memory addr state2\<close>

    \<open>call_memory state1 = call_memory state2
      \<Longrightarrow> read_call_memory addr state1 = read_call_memory addr state2\<close>

    \<open>static_memory state1 = static_memory state2
      \<Longrightarrow> read_static_memory addr state1 = read_static_memory addr state2\<close>

    \<open>dynamic_memory state1 = dynamic_memory state2
      \<Longrightarrow> read_dynamic_memory addr state1 = read_dynamic_memory addr state2\<close>

    \<open>input_memory state1 = input_memory state2
      \<Longrightarrow> read_input_memory addr state1 = read_input_memory addr state2\<close>
  by (simp_all add: read_program_memory_def read_call_memory_def read_static_memory_def
      read_dynamic_memory_def read_input_memory_def)

end