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

subsubsection \<open>Simplification Rules Over END\_JUMP\_STRICT\<close>

theory END_JUMP_STRICT_simps

imports
  END_JUMP_STRICT_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the end 
jump strict instruction. The various rules are primarily 
showing non-interference, or the specific changes to a specific value from the 
instruction. Where needed, we use the `special' case where we assume the guards of the 
instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_END_JUMP_STRICT:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>flag_state (END_JUMP_STRICT immediate state) = flag_state (clear_end_jump state)\<close>
  using assms
  by(simp add: END_JUMP_STRICT_decomp_mixed)

lemma (in Ironbark_world) memory_END_JUMP_STRICT:
  \<open>program_memory (END_JUMP_STRICT immediate state) = program_memory state\<close>
  \<open>call_memory    (END_JUMP_STRICT immediate state) = call_memory    state\<close>
  \<open>static_memory  (END_JUMP_STRICT immediate state) = static_memory  state\<close>
  \<open>dynamic_memory (END_JUMP_STRICT immediate state) = dynamic_memory state\<close>
  \<open>input_memory   (END_JUMP_STRICT immediate state) = input_memory   state\<close>
  \<open>output_memory  (END_JUMP_STRICT immediate state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_END_JUMP_STRICT:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>get_end_jump   (END_JUMP_STRICT immediate state) = 0\<close>
    \<open>get_end_call   (END_JUMP_STRICT immediate state) = 0\<close>
    \<open>get_end_return (END_JUMP_STRICT immediate state) = 0\<close>
    \<open>get_halt       (END_JUMP_STRICT immediate state) = 0\<close>
    \<open>get_error      (END_JUMP_STRICT immediate state) = 0\<close>
  using assms
  by(simp_all add: END_JUMP_STRICT_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_END_JUMP_STRICT:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>typical_flags (END_JUMP_STRICT immediate state)\<close>
  using assms
  by(simp_all add: read_flag_END_JUMP_STRICT)

lemma (in Ironbark_world) read_register_END_JUMP_STRICT:
  assumes
    \<open>regID \<notin> {
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      cycles_register_ref
    }\<close>
  shows
    \<open>read_register regID (END_JUMP_STRICT immediate state) = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_END_JUMP_STRICT:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>read_register instruction_pointer_ref (END_JUMP_STRICT immediate state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: END_JUMP_STRICT_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_END_JUMP_STRICT:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>read_register cycles_register_ref (END_JUMP_STRICT immediate state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: END_JUMP_STRICT_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_END_JUMP_STRICT:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (END_JUMP_STRICT immediate state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: END_JUMP_STRICT_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_memory_END_JUMP_STRICT:
  shows
    \<open>read_program_memory  address (END_JUMP_STRICT immediate state) 
    = read_program_memory address state\<close>

    \<open>read_call_memory     address (END_JUMP_STRICT immediate state) 
    = read_call_memory    address state\<close>

    \<open>read_static_memory   address (END_JUMP_STRICT immediate state) 
    = read_static_memory  address state\<close>

    \<open>read_dynamic_memory  address (END_JUMP_STRICT immediate state) 
    = read_dynamic_memory address state\<close>
  using memory_END_JUMP_STRICT
  by(simp_all add: state_manipulation_decomp)

text\<open>The following are lemmas of END\_JUMP\_STRICT on the initial state. 
Since the initial state is not after a jump, we get error. The simps for ERROR0 can 
be used in this instance.\<close>

lemma (in Ironbark_world) END_JUMP_STRICT_initial_state_errors:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>(END_JUMP_STRICT immediate start_state) = (ERROR0 start_state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

end