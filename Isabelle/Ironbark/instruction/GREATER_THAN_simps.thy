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

subsubsection \<open>Simplification Rules Over GREATER\_THAN\<close>

theory GREATER_THAN_simps

imports
  GREATER_THAN_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for 
the \<open>GREATER_THAN\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_GREATER_THAN:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>flag_state (GREATER_THAN reg1 reg2 reg3 state) = flag_state state\<close>
  using assms
  by(simp add: GREATER_THAN_decomp_mixed)

lemma (in Ironbark_world) memory_GREATER_THAN:
  \<open>program_memory (GREATER_THAN reg1 reg2 reg3 state) = program_memory  state\<close>
  \<open>call_memory    (GREATER_THAN reg1 reg2 reg3 state) = call_memory     state\<close>
  \<open>static_memory  (GREATER_THAN reg1 reg2 reg3 state) = static_memory   state\<close>
  \<open>dynamic_memory (GREATER_THAN reg1 reg2 reg3 state) = dynamic_memory  state\<close>
  \<open>input_memory   (GREATER_THAN reg1 reg2 reg3 state) = input_memory    state\<close>
  \<open>output_memory  (GREATER_THAN reg1 reg2 reg3 state) = output_memory   state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_GREATER_THAN:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>get_end_jump   (GREATER_THAN reg1 reg2 reg3 state) = 0\<close>
    \<open>get_end_call   (GREATER_THAN reg1 reg2 reg3 state) = 0\<close>
    \<open>get_end_return (GREATER_THAN reg1 reg2 reg3 state) = 0\<close>
    \<open>get_halt       (GREATER_THAN reg1 reg2 reg3 state) = 0\<close>
    \<open>get_error      (GREATER_THAN reg1 reg2 reg3 state) = 0\<close>
  using assms
  by(simp_all add: read_flag_decomp flag_GREATER_THAN)

lemma (in Ironbark_world) common_flags_GREATER_THAN:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>typical_flags (GREATER_THAN reg1 reg2 reg3 state)\<close>
  using assms
  by(simp_all add: read_flag_GREATER_THAN)

lemma (in Ironbark_world) read_register_GREATER_THAN_diff:
  assumes
    \<open>regID \<noteq> reg1\<close>
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref
              }\<close>
  shows
    \<open>read_register  regID (GREATER_THAN reg1 reg2 reg3 state) 
    = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_register_GREATER_THAN_same:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register reg1 (GREATER_THAN reg1 reg2 reg3 state) = 
    (
      if ((read_register reg2 state > read_register reg3 state)) then 
        0x1 
      else 
        0x0
    )\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_GREATER_THAN:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register instruction_pointer_ref (GREATER_THAN reg1 reg2 reg3 state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_GREATER_THAN:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register cycles_register_ref (GREATER_THAN reg1 reg2 reg3 state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_GREATER_THAN:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (GREATER_THAN reg1 reg2 reg3 state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_memory_GREATER_THAN:
  shows
    \<open>read_program_memory  address (GREATER_THAN reg1 reg2 reg3 state) 
    = read_program_memory address state\<close>

    \<open>read_call_memory     address (GREATER_THAN reg1 reg2 reg3 state) 
    = read_call_memory    address state\<close>

    \<open>read_static_memory   address (GREATER_THAN reg1 reg2 reg3 state) 
    = read_static_memory  address state\<close>

    \<open>read_dynamic_memory  address (GREATER_THAN reg1 reg2 reg3 state) 
    = read_dynamic_memory address state\<close>
  using memory_GREATER_THAN
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) write_register_GREATER_THAN_same:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>write_register reg1 value (GREATER_THAN reg1 reg2 reg3 state) 
    = write_register reg1 value 
      (standard_post_instruction common_instruction_duration state)\<close>
  using assms
  by(simp add: 
      instruction_impl_defs 
      state_manipulation_reorder 
      state_manipulation_simps)

text\<open>The following are cases of GREATER\_THAN over the initial state.\<close>

lemma (in Ironbark_world) read_flag_GREATER_THAN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (GREATER_THAN reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_end_call   (GREATER_THAN reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_end_return (GREATER_THAN reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_halt       (GREATER_THAN reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_error      (GREATER_THAN reg1 reg2 reg3 start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_GREATER_THAN initial_state_simps)

lemma (in Ironbark_world) common_flags_GREATER_THAN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>typical_flags (GREATER_THAN reg1 reg2 reg3 start_state)\<close>
  using assms
  by(simp add: read_flag_GREATER_THAN_initial_state)

lemma (in Ironbark_world) read_memory_GREATER_THAN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (GREATER_THAN reg1 reg2 reg3 start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (GREATER_THAN reg1 reg2 reg3 start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (GREATER_THAN reg1 reg2 reg3 start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (GREATER_THAN reg1 reg2 reg3 start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_GREATER_THAN)

lemma (in Ironbark_world) read_last_ip_GREATER_THAN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref 
      (GREATER_THAN reg1 reg2 reg3 start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_GREATER_THAN initial_state_simps)

lemma (in Ironbark_world) read_ip_GREATER_THAN_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (GREATER_THAN reg1 reg2 reg3 start_state) 
    = (read_register instruction_pointer_ref start_state) + 1\<close>
  using assms
  by(simp add: read_ip_GREATER_THAN initial_state_simps)

end