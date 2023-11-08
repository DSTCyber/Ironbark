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

subsubsection \<open>Simplification Rules Over JUMP\<close>

theory JUMP_simps

imports
  JUMP_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for 
the \<open>JUMP\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_JUMP:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>flag_state (JUMP immediate state) = flag_state (set_end_jump state)\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) memory_JUMP:
  \<open>program_memory (JUMP immediate state) = program_memory state\<close>
  \<open>call_memory    (JUMP immediate state) = call_memory    state\<close>
  \<open>static_memory  (JUMP immediate state) = static_memory  state\<close>
  \<open>dynamic_memory (JUMP immediate state) = dynamic_memory state\<close>
  \<open>input_memory   (JUMP immediate state) = input_memory   state\<close>
  \<open>output_memory  (JUMP immediate state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_JUMP:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>get_end_jump   (JUMP immediate state) = 1\<close>
    \<open>get_end_call   (JUMP immediate state) = 0\<close>
    \<open>get_end_return (JUMP immediate state) = 0\<close>
    \<open>get_halt       (JUMP immediate state) = 0\<close>
    \<open>get_error      (JUMP immediate state) = 0\<close>
  using assms
  by(simp_all add: JUMP_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_JUMP:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>end_jump_flags (JUMP immediate state)\<close>
  using assms
  by(simp_all add: read_flag_JUMP)

lemma (in Ironbark_world) read_register_JUMP:
  assumes
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref
              }\<close>
  shows
    \<open>read_register regID (JUMP immediate state) = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_JUMP:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register instruction_pointer_ref (JUMP immediate state) = immediate\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_JUMP:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register cycles_register_ref (JUMP immediate state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_JUMP:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (JUMP immediate state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: instruction_impl_defs  state_manipulation_simps)

lemma (in Ironbark_world) read_memory_JUMP:
  \<open>read_program_memory  address (JUMP immediate state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (JUMP immediate state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (JUMP immediate state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (JUMP immediate state) 
  = read_dynamic_memory address state\<close>
  using memory_JUMP
  by(simp_all add: state_manipulation_decomp)

text\<open>The following are cases of JUMP over the initial state.\<close>

lemma (in Ironbark_world) read_flag_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (JUMP immediate start_state) = 1\<close>
    \<open>get_end_call   (JUMP immediate start_state) = 0\<close>
    \<open>get_end_return (JUMP immediate start_state) = 0\<close>
    \<open>get_halt       (JUMP immediate start_state) = 0\<close>
    \<open>get_error      (JUMP immediate start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_JUMP initial_state_simps)

lemma (in Ironbark_world) common_flags_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>end_jump_flags (JUMP immediate start_state)\<close>
  using assms
  by(simp add: read_flag_JUMP_initial_state)

lemma (in Ironbark_world) read_memory_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (JUMP immediate start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (JUMP immediate start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (JUMP immediate start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (JUMP immediate start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_JUMP)

lemma (in Ironbark_world) read_last_ip_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (JUMP immediate start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_JUMP initial_state_simps)

lemma (in Ironbark_world) read_ip_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (JUMP immediate start_state) = immediate\<close>
proof -
  have 
    \<open>(read_register reg1 start_state) = 0x00\<close>
    using assms
    by(simp_all add: state_manipulation_simps)
  then show ?thesis
    using assms
    by(simp_all add: read_ip_JUMP state_manipulation_simps)
qed

end