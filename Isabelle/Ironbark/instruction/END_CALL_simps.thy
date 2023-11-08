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

subsubsection \<open>Simplification Rules Over END\_CALL\<close>

theory END_CALL_simps

imports
  END_CALL_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the 
\<open>END_CALL\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>flag_state (END_CALL state) = flag_state (clear_end_call state)\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) register_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>register_state (END_CALL state) 
    = register_state (standard_post_instruction common_instruction_duration state)\<close>
  using assms
  apply(simp_all add: instruction_impl_defs)
  apply(intro register_state_passover)
  apply(simp_all add: state_manipulation_simps)
  done

lemma (in Ironbark_world) memory_END_CALL:
  shows
    \<open>program_memory (END_CALL state) = program_memory state\<close>
    \<open>call_memory    (END_CALL state) = call_memory    state\<close>
    \<open>static_memory  (END_CALL state) = static_memory  state\<close>
    \<open>dynamic_memory (END_CALL state) = dynamic_memory state\<close>
    \<open>input_memory   (END_CALL state) = input_memory   state\<close>
    \<open>output_memory  (END_CALL state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>get_end_jump   (END_CALL state) = 0\<close>
    \<open>get_end_call   (END_CALL state) = 0\<close>
    \<open>get_end_return (END_CALL state) = 0\<close>
    \<open>get_halt       (END_CALL state) = 0\<close>
    \<open>get_error      (END_CALL state) = 0\<close>
  using assms 
  by(simp_all add: state_manipulation_decomp flag_END_CALL)

lemma (in Ironbark_world) common_flags_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>typical_flags (END_CALL state)\<close>
  using assms
  by(simp_all add: read_flag_END_CALL)

lemma (in Ironbark_world) read_register_END_CALL:
  assumes
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref
              }\<close>
  shows
    \<open>read_register regID (END_CALL state) = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>read_register instruction_pointer_ref (END_CALL state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>read_register cycles_register_ref (END_CALL state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_END_CALL:
  assumes
    \<open>end_call_flags state\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (END_CALL state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_memory_END_CALL:
  shows
    \<open>read_program_memory  address (END_CALL state) 
    = read_program_memory address state\<close>

    \<open>read_call_memory     address (END_CALL state) 
    = read_call_memory    address state\<close>

    \<open>read_static_memory   address (END_CALL state) 
    = read_static_memory  address state\<close>

    \<open>read_dynamic_memory  address (END_CALL state) 
    = read_dynamic_memory address state\<close>
  using memory_END_CALL
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

text\<open>The following are lemmas of END\_CALL on the initial state. Since there is no 
call, we just get error, and we can use the ERROR0 lemmas for reasoning beyond this 
point.\<close>

lemma (in Ironbark_world) END_CALL_initial_state_errors:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>(END_CALL start_state) = (ERROR0 start_state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

end