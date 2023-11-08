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

subsubsection \<open>Simplification Rules Over BITWISE\_AND\<close>

theory BITWISE_AND_simps

imports
  BITWISE_AND_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the 
\<open>BITWISE_AND\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_BITWISE_AND:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>flag_state (BITWISE_AND reg1 reg2 reg3 state) = flag_state state\<close>
  using assms
  by(simp_all add: BITWISE_AND_decomp_mixed)

lemma (in Ironbark_world) memory_BITWISE_AND:
  shows
    \<open>program_memory (BITWISE_AND reg1 reg2 reg3 state) = program_memory state\<close>
    \<open>call_memory    (BITWISE_AND reg1 reg2 reg3 state) = call_memory    state\<close>
    \<open>static_memory  (BITWISE_AND reg1 reg2 reg3 state) = static_memory  state\<close>
    \<open>dynamic_memory (BITWISE_AND reg1 reg2 reg3 state) = dynamic_memory state\<close>
    \<open>input_memory   (BITWISE_AND reg1 reg2 reg3 state) = input_memory   state\<close>
    \<open>output_memory  (BITWISE_AND reg1 reg2 reg3 state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_BITWISE_AND:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>get_end_jump   (BITWISE_AND reg1 reg2 reg3 state) = 0\<close>
    \<open>get_end_call   (BITWISE_AND reg1 reg2 reg3 state) = 0\<close>
    \<open>get_end_return (BITWISE_AND reg1 reg2 reg3 state) = 0\<close>
    \<open>get_halt       (BITWISE_AND reg1 reg2 reg3 state) = 0\<close>
    \<open>get_error      (BITWISE_AND reg1 reg2 reg3 state) = 0\<close>
  using assms
  by(simp_all add: read_flag_decomp flag_BITWISE_AND)

lemma (in Ironbark_world) common_flags_BITWISE_AND:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>typical_flags (BITWISE_AND reg1 reg2 reg3 state)\<close>
  using assms
  by(simp_all add: read_flag_BITWISE_AND)

lemma (in Ironbark_world) read_register_BITWISE_AND_diff:
  assumes
    \<open>regID \<noteq> reg1\<close>
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref
              }\<close>
  shows
    \<open>read_register regID (BITWISE_AND reg1 reg2 reg3 state) 
      = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_register_BITWISE_AND_same:
  includes 
    bit_operations_syntax
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register reg1 (BITWISE_AND reg1 reg2 reg3 state) 
    = (read_register reg2 state) AND (read_register reg3 state)\<close>
  using assms
  by(simp add: BITWISE_AND_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_ip_BITWISE_AND:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register instruction_pointer_ref (BITWISE_AND reg1 reg2 reg3 state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_BITWISE_AND:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register cycles_register_ref (BITWISE_AND reg1 reg2 reg3 state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_BITWISE_AND:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (BITWISE_AND reg1 reg2 reg3 state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_memory_BITWISE_AND:
  shows
    \<open>read_program_memory  address (BITWISE_AND reg1 reg2 reg3 state) 
    = read_program_memory address state\<close>

    \<open>read_call_memory     address (BITWISE_AND reg1 reg2 reg3 state) 
    = read_call_memory    address state\<close>

    \<open>read_static_memory   address (BITWISE_AND reg1 reg2 reg3 state) 
    = read_static_memory  address state\<close>

    \<open>read_dynamic_memory  address (BITWISE_AND reg1 reg2 reg3 state) 
    = read_dynamic_memory address state\<close>
  using memory_BITWISE_AND
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) write_register_BITWISE_AND_same:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  shows
    \<open>write_register reg1 value (BITWISE_AND reg1 reg2 reg3 state) = 
      write_register 
        reg1 
        value 
        (standard_post_instruction common_instruction_duration state)\<close>
  using assms
  by(simp add: 
      instruction_impl_defs
      state_manipulation_reorder
      state_manipulation_simps)

text \<open>The following are cases of BITWISE\_AND over the initial state.\<close>

lemma (in Ironbark_world) read_flag_BITWISE_AND_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (BITWISE_AND reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_end_call   (BITWISE_AND reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_end_return (BITWISE_AND reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_halt       (BITWISE_AND reg1 reg2 reg3 start_state) = 0\<close>
    \<open>get_error      (BITWISE_AND reg1 reg2 reg3 start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_BITWISE_AND initial_state_simps)

lemma (in Ironbark_world) common_flags_BITWISE_AND_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>typical_flags (BITWISE_AND reg1 reg2 reg3 start_state)\<close>
  using assms
  by(simp add: read_flag_BITWISE_AND_initial_state)

lemma (in Ironbark_world) read_memory_BITWISE_AND_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (BITWISE_AND reg1 reg2 reg3 start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (BITWISE_AND reg1 reg2 reg3 start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (BITWISE_AND reg1 reg2 reg3 start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (BITWISE_AND reg1 reg2 reg3 start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_BITWISE_AND)

lemma (in Ironbark_world) read_last_ip_BITWISE_AND_initial_state:
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
      (BITWISE_AND reg1 reg2 reg3 start_state) 
    = read_register instruction_pointer_ref start_state\<close>
  using assms
  by(simp add: read_last_ip_BITWISE_AND initial_state_simps)

lemma (in Ironbark_world) read_ip_BITWISE_AND_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
    \<open>check_read_permission reg3\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (BITWISE_AND reg1 reg2 reg3 start_state) 
    = (read_register instruction_pointer_ref start_state) + 1\<close>
  using assms
  by(simp add: read_ip_BITWISE_AND initial_state_simps)

end