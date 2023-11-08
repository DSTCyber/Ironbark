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

subsubsection \<open>Simplification Rules Over LOAD\_IMMEDIATE\<close>

theory LOAD_IMMEDIATE_simps

imports
  instruction_auxiliary
  LOAD_IMMEDIATE_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for 
the \<open>LOAD_IMMEDIATE\<close> instruction. The various rules are 
primarily showing non-interference, or the specific changes to a specific value from 
the instruction. Where needed, we use the `special' case where we assume the guards of 
the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_LOAD_IMMEDIATE:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>flag_state (LOAD_IMMEDIATE regID immediate state) = flag_state state\<close>
  using assms
  by(simp add: LOAD_IMMEDIATE_decomp_mixed)

lemma (in Ironbark_world) memory_LOAD_IMMEDIATE:
  shows
    \<open>program_memory (LOAD_IMMEDIATE regID immediate state) = program_memory state\<close>
    \<open>call_memory    (LOAD_IMMEDIATE regID immediate state) = call_memory    state\<close>
    \<open>static_memory  (LOAD_IMMEDIATE regID immediate state) = static_memory  state\<close>
    \<open>dynamic_memory (LOAD_IMMEDIATE regID immediate state) = dynamic_memory state\<close>
    \<open>input_memory   (LOAD_IMMEDIATE regID immediate state) = input_memory   state\<close>
    \<open>output_memory  (LOAD_IMMEDIATE regID immediate state) = output_memory  state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_LOAD_IMMEDIATE:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>get_end_jump   (LOAD_IMMEDIATE regID immediate state) = 0\<close>
    \<open>get_end_call   (LOAD_IMMEDIATE regID immediate state) = 0\<close>
    \<open>get_end_return (LOAD_IMMEDIATE regID immediate state) = 0\<close>
    \<open>get_halt       (LOAD_IMMEDIATE regID immediate state) = 0\<close>
    \<open>get_error      (LOAD_IMMEDIATE regID immediate state) = 0\<close>
  using assms
  by(simp_all add: read_flag_decomp flag_LOAD_IMMEDIATE)

lemma (in Ironbark_world) common_flags_LOAD_IMMEDIATE:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>typical_flags (LOAD_IMMEDIATE regID immediate state)\<close>
  using assms
  by(simp_all add: read_flag_LOAD_IMMEDIATE)

lemma (in Ironbark_world) read_register_LOAD_IMMEDIATE_diff:
  assumes
    \<open>regID1 \<noteq> regID2\<close>
    \<open>regID1 \<notin> {
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      cycles_register_ref
    }\<close>
  shows
    \<open>read_register  regID1 (LOAD_IMMEDIATE regID2 immediate state) 
    = read_register regID1 state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_register_LOAD_IMMEDIATE_same:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>read_register regID (LOAD_IMMEDIATE regID immediate state) = immediate\<close>
  using assms
  by(simp add: LOAD_IMMEDIATE_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_ip_LOAD_IMMEDIATE:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>read_register instruction_pointer_ref (LOAD_IMMEDIATE regID immediate state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: LOAD_IMMEDIATE_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_LOAD_IMMEDIATE:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>read_register cycles_register_ref (LOAD_IMMEDIATE regID immediate state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: LOAD_IMMEDIATE_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_LOAD_IMMEDIATE:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (LOAD_IMMEDIATE regID immediate state) 
      = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: LOAD_IMMEDIATE_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_memory_LOAD_IMMEDIATE:
  shows
    \<open>read_program_memory  address (LOAD_IMMEDIATE regID immediate state) 
    = read_program_memory address state\<close>

    \<open>read_call_memory     address (LOAD_IMMEDIATE regID immediate state) 
    = read_call_memory    address state\<close>

    \<open>read_static_memory   address (LOAD_IMMEDIATE regID immediate state) 
    = read_static_memory  address state\<close>

    \<open>read_dynamic_memory  address (LOAD_IMMEDIATE regID immediate state) 
    = read_dynamic_memory address state\<close>
  using memory_LOAD_IMMEDIATE
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) write_register_LOAD_IMMEDIATE_same:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_write_permission regID\<close>
  shows
    \<open>write_register regID value (LOAD_IMMEDIATE regID immediate state) = 
      write_register 
        regID 
        value 
        (standard_post_instruction common_instruction_duration state)\<close>
  using assms
  by(simp add: 
      instruction_impl_defs 
      state_manipulation_reorder 
      state_manipulation_simps)

text\<open>The following are lemmas of LOAD\_IMMEDIATE on the initial state.\<close>

lemma (in Ironbark_world) read_flag_LOAD_IMMEDIATE_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission regID\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (LOAD_IMMEDIATE regID immediate start_state) = 0\<close>
    \<open>get_end_call   (LOAD_IMMEDIATE regID immediate start_state) = 0\<close>
    \<open>get_end_return (LOAD_IMMEDIATE regID immediate start_state) = 0\<close>
    \<open>get_halt       (LOAD_IMMEDIATE regID immediate start_state) = 0\<close>
    \<open>get_error      (LOAD_IMMEDIATE regID immediate start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_LOAD_IMMEDIATE initial_state_simps)

lemma (in Ironbark_world) common_flags_LOAD_IMMEDIATE_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission regID\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>typical_flags (LOAD_IMMEDIATE regID immediate start_state)\<close>
  using assms
  by(simp add: read_flag_LOAD_IMMEDIATE_initial_state)

lemma (in Ironbark_world) read_memory_LOAD_IMMEDIATE_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission regID\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (LOAD_IMMEDIATE regID immediate start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (LOAD_IMMEDIATE regID immediate start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (LOAD_IMMEDIATE regID immediate start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (LOAD_IMMEDIATE regID immediate start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_LOAD_IMMEDIATE initial_state_simps)

lemma (in Ironbark_world) read_last_ip_LOAD_IMMEDIATE_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission regID\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref 
      (LOAD_IMMEDIATE regID immediate start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_LOAD_IMMEDIATE initial_state_simps)

lemma (in Ironbark_world) read_ip_LOAD_IMMEDIATE_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_write_permission regID\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (LOAD_IMMEDIATE regID immediate start_state) 
    = (read_register instruction_pointer_ref start_state) + 1\<close>
  using assms
  by(simp add: read_ip_LOAD_IMMEDIATE initial_state_simps)

end