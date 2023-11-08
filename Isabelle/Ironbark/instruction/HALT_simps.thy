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

subsubsection \<open>Simplification Rules Over HALT\<close>

theory HALT_simps

imports
  HALT_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for 
the \<open>HALT\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_HALT:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>flag_state (HALT state) = flag_state (set_halt state)\<close>
  using assms
  by(simp add: HALT_decomp_manipulation standard_error_def)

lemma (in Ironbark_world) register_HALT:
  \<open>register_state (HALT state) = register_state state\<close>
proof (cases \<open>typical_flags state\<close>)
  case True
  then show ?thesis 
    by(simp_all add: HALT_decomp_manipulation state_manipulation_simps)
next
  case False
  then show ?thesis 
    by(simp add: instruction_impl_defs state_manipulation_simps)
qed

lemma (in Ironbark_world) memory_HALT:
  \<open>program_memory (HALT state) = program_memory state\<close>
  \<open>call_memory    (HALT state) = call_memory    state\<close>
  \<open>static_memory  (HALT state) = static_memory  state\<close>
  \<open>dynamic_memory (HALT state) = dynamic_memory state\<close>
  \<open>input_memory   (HALT state) = input_memory   state\<close>
  \<open>output_memory  (HALT state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_HALT:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>get_end_jump   (HALT state) = 0\<close>
    \<open>get_end_call   (HALT state) = 0\<close>
    \<open>get_end_return (HALT state) = 0\<close>
    \<open>get_halt       (HALT state) = 1\<close>
    \<open>get_error      (HALT state) = 0\<close>
  using assms
  by(auto simp add: HALT_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_HALT:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>halt_flags (HALT state)\<close>
  using assms
  by(simp add: read_flag_HALT)

lemma (in Ironbark_world) read_register_HALT:
  \<open>read_register regID (HALT state) = read_register regID state\<close>
  by(simp_all add: read_register_def register_HALT)

lemma (in Ironbark_world) read_memory_HALT:
  \<open>read_program_memory  address (HALT state) = read_program_memory  address state\<close>
  \<open>read_call_memory     address (HALT state) = read_call_memory     address state\<close>
  \<open>read_static_memory   address (HALT state) = read_static_memory   address state\<close>
  \<open>read_dynamic_memory  address (HALT state) = read_dynamic_memory  address state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

text\<open>The following are lemmas of HALT on the initial state.\<close>

lemma (in Ironbark_world) read_flag_HALT_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (HALT start_state) = 0\<close>
    \<open>get_end_call   (HALT start_state) = 0\<close>
    \<open>get_end_return (HALT start_state) = 0\<close>
    \<open>get_halt       (HALT start_state) = 1\<close>
    \<open>get_error      (HALT start_state) = 0\<close>
  using assms
  by(auto simp add: read_flag_HALT initial_state_simps)

lemma (in Ironbark_world) common_flags_HALT_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>halt_flags (HALT start_state)\<close>
  using assms
  by(simp_all add: read_flag_HALT_initial_state)

lemma (in Ironbark_world) read_register_HALT_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register regID (HALT start_state) = read_register regID start_state\<close>
  using assms
  by(simp_all add: read_register_HALT)

lemma (in Ironbark_world) read_memory_HALT_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory    address (HALT start_state) 
      = read_program_memory address start_state\<close>

    \<open>read_call_memory       address (HALT start_state) 
      = read_call_memory    address start_state\<close>

    \<open>read_static_memory     address (HALT start_state) 
      = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory    address (HALT start_state) 
      = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_HALT)

end