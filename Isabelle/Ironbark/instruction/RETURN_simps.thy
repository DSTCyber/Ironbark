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

subsubsection \<open>Simplification Rules Over RETURN\<close>

theory RETURN_simps

imports
  RETURN_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for 
the \<open>RETURN\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) memory_RETURN:
  \<open>program_memory (RETURN state) = program_memory state\<close>
  \<open>call_memory    (RETURN state) = call_memory    state\<close>
  \<open>static_memory  (RETURN state) = static_memory  state\<close>
  \<open>dynamic_memory (RETURN state) = dynamic_memory state\<close>
  \<open>input_memory   (RETURN state) = input_memory   state\<close>
  \<open>output_memory  (RETURN state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps Let_def)

lemma (in Ironbark_world) read_flag_RETURN:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>get_end_jump   (RETURN state) = 0\<close>
    \<open>get_end_call   (RETURN state) = 0\<close>
    \<open>get_end_return (RETURN state) = 1\<close>
    \<open>get_halt       (RETURN state) = 0\<close>
    \<open>get_error      (RETURN state) = 0\<close>
  using assms
  by(auto simp add: RETURN_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_RETURN:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>end_return_flags (RETURN state)\<close>
  using assms
  by(simp_all add: read_flag_RETURN)

lemma (in Ironbark_world) read_ip_RETURN:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register instruction_pointer_ref (RETURN state) 
    = read_call_memory ((read_register call_frame_pointer_ref state) - 67) state + 1\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps Let_def)

lemma (in Ironbark_world) read_cycles_RETURN:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register cycles_register_ref (RETURN state) 
    = (read_register cycles_register_ref state) + call_duration\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_RETURN:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (RETURN state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_memory_RETURN:
  shows
    \<open>read_program_memory  address (RETURN state) = read_program_memory  address state\<close>
    \<open>read_static_memory   address (RETURN state) = read_static_memory   address state\<close>
    \<open>read_dynamic_memory  address (RETURN state) = read_dynamic_memory  address state\<close>
  using memory_RETURN
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) read_call_memory_RETURN:
  assumes
    \<open>typical_flags state\<close>
    \<open>\<forall>n \<in> {0 .. 50} . address \<noteq> read_register call_frame_pointer_ref state + 51 + n\<close>
    \<open>address < (read_register call_frame_pointer_ref state)\<close>
  shows
    \<open>read_call_memory address (RETURN state) = read_call_memory address state\<close>
  using assms
  by(simp add: 
      instruction_impl_defs 
      state_manipulation_reorder
      state_manipulation_simps)

text\<open>The following are cases of RETURN over the initial state\<close>

lemma (in Ironbark_world) read_flag_RETURN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (RETURN start_state) = 0\<close>
    \<open>get_end_call   (RETURN start_state) = 0\<close>
    \<open>get_end_return (RETURN start_state) = 1\<close>
    \<open>get_halt       (RETURN start_state) = 0\<close>
    \<open>get_error      (RETURN start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_RETURN initial_state_simps)

lemma (in Ironbark_world) common_flags_RETURN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>end_return_flags (RETURN start_state)\<close>
  using assms
  by(simp add: read_flag_RETURN_initial_state)

lemma (in Ironbark_world) read_memory_RETURN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (RETURN start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_static_memory   address (RETURN start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (RETURN start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_RETURN)

lemma (in Ironbark_world) read_last_ip_RETURN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (RETURN start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_RETURN initial_state_simps)

lemma (in Ironbark_world) read_ip_RETURN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (RETURN start_state) = the None + 1\<close>
  using assms
  by(simp add: read_ip_RETURN initial_state_simps read_call_memory_def)

end