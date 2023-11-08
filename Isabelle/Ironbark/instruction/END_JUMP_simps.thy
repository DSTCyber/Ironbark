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

subsubsection \<open>Simplification Rules Over END\_JUMP\<close>

theory END_JUMP_simps

imports
  END_JUMP_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the 
\<open>END_JUMP\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_END_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>flag_state (END_JUMP immediate state) = flag_state state\<close>
  using assms
  by(simp add: END_JUMP_decomp_mixed_fall)

lemma (in Ironbark_world) memory_END_JUMP:
  \<open>program_memory (END_JUMP immediate state) = program_memory state\<close>
  \<open>call_memory    (END_JUMP immediate state) = call_memory    state\<close>
  \<open>static_memory  (END_JUMP immediate state) = static_memory  state\<close>
  \<open>dynamic_memory (END_JUMP immediate state) = dynamic_memory state\<close>
  \<open>input_memory   (END_JUMP immediate state) = input_memory   state\<close>
  \<open>output_memory  (END_JUMP immediate state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_END_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>get_end_jump   (END_JUMP immediate state) = 0\<close>
    \<open>get_end_call   (END_JUMP immediate state) = 0\<close>
    \<open>get_end_return (END_JUMP immediate state) = 0\<close>
    \<open>get_halt       (END_JUMP immediate state) = 0\<close>
    \<open>get_error      (END_JUMP immediate state) = 0\<close>
  using assms
  by(simp_all add: read_flag_decomp flag_END_JUMP_fall)

lemma (in Ironbark_world) read_flag_END_JUMP_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>get_end_jump   (END_JUMP immediate state) = 0\<close>
    \<open>get_end_call   (END_JUMP immediate state) = 0\<close>
    \<open>get_end_return (END_JUMP immediate state) = 0\<close>
    \<open>get_halt       (END_JUMP immediate state) = 0\<close>
    \<open>get_error      (END_JUMP immediate state) = 0\<close>
  using assms
  by(simp_all add: END_JUMP_decomp_manipulation_jump state_manipulation_simps)

lemma (in Ironbark_world) common_flags_END_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>typical_flags (END_JUMP immediate state)\<close>
  using assms
  by(simp_all add: read_flag_END_JUMP_fall)

lemma (in Ironbark_world) common_flags_END_JUMP_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>typical_flags (END_JUMP immediate state)\<close>
  using assms
  by(simp_all add: read_flag_END_JUMP_jump)

lemma (in Ironbark_world) read_register_END_JUMP:
  assumes
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref
              }\<close>
  shows
    \<open>read_register regID (END_JUMP immediate state) = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_END_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register instruction_pointer_ref (END_JUMP immediate state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: END_JUMP_decomp_manipulation_fall state_manipulation_simps)

lemma (in Ironbark_world) read_ip_END_JUMP_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>read_register instruction_pointer_ref (END_JUMP immediate state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: END_JUMP_decomp_manipulation_jump state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_END_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register cycles_register_ref (END_JUMP immediate state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: END_JUMP_decomp_manipulation_fall state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_END_JUMP_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>read_register cycles_register_ref (END_JUMP immediate state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: END_JUMP_decomp_manipulation_jump state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_END_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (END_JUMP immediate state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: END_JUMP_decomp_manipulation_fall state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_END_JUMP_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (END_JUMP immediate state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: END_JUMP_decomp_manipulation_jump state_manipulation_simps)

lemma (in Ironbark_world) read_memory_END_JUMP:
  \<open>read_program_memory  address (END_JUMP immediate state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (END_JUMP immediate state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (END_JUMP immediate state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (END_JUMP immediate state) 
  = read_dynamic_memory address state\<close>
  using memory_END_JUMP
  by(simp_all add: state_manipulation_decomp)

text\<open>The following are lemmas of END\_JUMP on the initial state.\<close>

lemma (in Ironbark_world) read_flag_END_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (END_JUMP immediate start_state) = 0\<close>
    \<open>get_end_call   (END_JUMP immediate start_state) = 0\<close>
    \<open>get_end_return (END_JUMP immediate start_state) = 0\<close>
    \<open>get_halt       (END_JUMP immediate start_state) = 0\<close>
    \<open>get_error      (END_JUMP immediate start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_END_JUMP_fall initial_state_simps)

lemma (in Ironbark_world) common_flags_END_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>typical_flags (END_JUMP immediate start_state)\<close>
  using assms
  by(simp add: read_flag_END_JUMP_initial_state)

lemma (in Ironbark_world) read_memory_END_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (END_JUMP immediate start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (END_JUMP immediate start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (END_JUMP immediate start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (END_JUMP immediate start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_END_JUMP initial_state_simps)

lemma (in Ironbark_world) read_last_ip_END_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (END_JUMP immediate start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_END_JUMP_fall initial_state_simps)

lemma (in Ironbark_world) read_ip_END_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (END_JUMP immediate start_state) 
    = (read_register instruction_pointer_ref start_state) + 1\<close>
  using assms
  by(simp add: read_ip_END_JUMP_fall initial_state_simps)

end