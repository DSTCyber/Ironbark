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

subsubsection \<open>Simplification Rules Over CALL\<close>

theory CALL_simps

imports
  CALL_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the 
\<open>CALL\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) memory_CALL:
  \<open>program_memory (CALL immediate state) = program_memory state\<close>
  \<open>static_memory  (CALL immediate state) = static_memory  state\<close>
  \<open>dynamic_memory (CALL immediate state) = dynamic_memory state\<close>
  \<open>input_memory   (CALL immediate state) = input_memory   state\<close>
  \<open>output_memory  (CALL immediate state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_CALL:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>get_end_jump   (CALL immediate state) = 0\<close>
    \<open>get_end_call   (CALL immediate state) = 1\<close>
    \<open>get_end_return (CALL immediate state) = 0\<close>
    \<open>get_halt       (CALL immediate state) = 0\<close>
    \<open>get_error      (CALL immediate state) = 0\<close>
  using assms
  by(auto simp add: CALL_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_CALL:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>end_call_flags (CALL immediate state)\<close>
  using assms
  by(simp_all add: read_flag_CALL)

lemma (in Ironbark_world) read_register_CALL:
  assumes
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref,
                call_frame_pointer_ref
              }\<close>
  shows
    \<open>read_register regID (CALL immediate state) = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_CALL:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register instruction_pointer_ref (CALL immediate state) = immediate\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_CALL:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register cycles_register_ref (CALL immediate state) 
    = (read_register cycles_register_ref state) + call_duration\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_CALL:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (CALL immediate state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_call_pointer_CALL:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register call_frame_pointer_ref (CALL immediate state) 
    = (read_register call_frame_pointer_ref state) + 67\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_memory_CALL:
  \<open>read_program_memory  address (CALL immediate state) 
  = read_program_memory address state\<close>
  \<open>read_static_memory   address (CALL immediate state) 
  = read_static_memory  address state\<close>
  \<open>read_dynamic_memory  address (CALL immediate state) 
  = read_dynamic_memory address state\<close>
  using memory_CALL
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) read_call_memory_CALL:
  assumes
    \<open>typical_flags state\<close>
    \<open>\<forall>n \<in> {0 .. 66} . address \<noteq> read_register call_frame_pointer_ref state + n\<close>
    \<open>address < (read_register call_frame_pointer_ref state)\<close>
  shows
    \<open>read_call_memory address (CALL immediate state) = read_call_memory address state\<close>
  using assms
  by(simp add: 
      instruction_impl_defs
      state_manipulation_reorder
      state_manipulation_simps)

text\<open>The following are cases of CALL over the initial state\<close>

lemma (in Ironbark_world) read_flag_CALL_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (CALL immediate start_state) = 0\<close>
    \<open>get_end_call   (CALL immediate start_state) = 1\<close>
    \<open>get_end_return (CALL immediate start_state) = 0\<close>
    \<open>get_halt       (CALL immediate start_state) = 0\<close>
    \<open>get_error      (CALL immediate start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_CALL initial_state_simps)

lemma (in Ironbark_world) common_flags_CALL_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>end_call_flags (CALL immediate start_state)\<close>
  using assms
  by(simp add: read_flag_CALL_initial_state)

lemma (in Ironbark_world) read_memory_CALL_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (CALL immediate start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_static_memory   address (CALL immediate start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (CALL immediate start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_CALL)

lemma (in Ironbark_world) read_last_ip_CALL_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (CALL immediate start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_CALL initial_state_simps)

lemma (in Ironbark_world) read_ip_CALL_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (CALL immediate start_state) = immediate\<close>
  using assms
  by(simp add: read_ip_CALL initial_state_simps)

end