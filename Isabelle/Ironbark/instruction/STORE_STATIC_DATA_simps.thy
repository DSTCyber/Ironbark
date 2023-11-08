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

subsubsection \<open>Simplification Rules Over STORE\_STATIC\_DATA\<close>

theory STORE_STATIC_DATA_simps

imports
  STORE_STATIC_DATA_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the store 
static data instruction. The various rules are primarily 
showing non-interference, or the specific changes to a specific value from the 
instruction. Where needed, we use the `special' case where we assume the guards of the 
instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_STORE_STATIC_DATA:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>flag_state (STORE_STATIC_DATA reg1 reg2 state) = flag_state state\<close>
  using assms
  by(simp add: STORE_STATIC_DATA_decomp_mixed)

lemma (in Ironbark_world) memory_STORE_STATIC_DATA_same:
  \<open>program_memory (STORE_STATIC_DATA reg1 reg2 state) = program_memory  state\<close>
  \<open>call_memory    (STORE_STATIC_DATA reg1 reg2 state) = call_memory     state\<close>
  \<open>dynamic_memory (STORE_STATIC_DATA reg1 reg2 state) = dynamic_memory  state\<close>
  \<open>input_memory   (STORE_STATIC_DATA reg1 reg2 state) = input_memory    state\<close>
  \<open>output_memory  (STORE_STATIC_DATA reg1 reg2 state) = output_memory   state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) memory_STORE_STATIC_DATA_diff:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>static_memory (STORE_STATIC_DATA reg1 reg2 state) = 
      static_memory 
        (write_static_memory
          (read_register reg1 state)
          (read_register reg2 state)
          state
        )\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_STORE_STATIC_DATA:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>get_end_jump   (STORE_STATIC_DATA reg1 reg2 state) = 0\<close>
    \<open>get_end_call   (STORE_STATIC_DATA reg1 reg2 state) = 0\<close>
    \<open>get_end_return (STORE_STATIC_DATA reg1 reg2 state) = 0\<close>
    \<open>get_halt       (STORE_STATIC_DATA reg1 reg2 state) = 0\<close>
    \<open>get_error      (STORE_STATIC_DATA reg1 reg2 state) = 0\<close>
  using assms
  by(simp_all add: read_flag_decomp flag_STORE_STATIC_DATA)

lemma (in Ironbark_world) common_flags_STORE_STATIC_DATA:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>typical_flags (STORE_STATIC_DATA reg1 reg2 state)\<close>
  using assms
  by(simp_all add: read_flag_STORE_STATIC_DATA)

lemma (in Ironbark_world) read_register_STORE_STATIC_DATA:
  assumes
    \<open>regID \<notin> {
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      cycles_register_ref
    }\<close>
  shows
    \<open>read_register    regID (STORE_STATIC_DATA reg1 reg2 state) 
    = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_STORE_STATIC_DATA:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>read_register instruction_pointer_ref (STORE_STATIC_DATA reg1 reg2 state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: STORE_STATIC_DATA_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_STORE_STATIC_DATA:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>read_register cycles_register_ref (STORE_STATIC_DATA reg1 reg2 state) 
    = (read_register cycles_register_ref state) + memory_instruction_duration\<close>
  using assms
  by(simp add: STORE_STATIC_DATA_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_STORE_STATIC_DATA:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (STORE_STATIC_DATA reg1 reg2 state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: STORE_STATIC_DATA_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) read_memory_STORE_STATIC_DATA_same:
  \<open>read_program_memory  address (STORE_STATIC_DATA reg1 reg2 state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (STORE_STATIC_DATA reg1 reg2 state) 
  = read_call_memory    address state\<close>

  \<open>read_dynamic_memory  address (STORE_STATIC_DATA reg1 reg2 state) 
  = read_dynamic_memory address state\<close>
  using memory_STORE_STATIC_DATA_same
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) read_memory_STORE_STATIC_DATA_diff:
  assumes
    \<open>address \<noteq> read_register reg1 state\<close>
  shows
    \<open>read_dynamic_memory  address (STORE_STATIC_DATA reg1 reg2 state) 
    = read_dynamic_memory address state\<close>
proof (cases 
    \<open>(check_read_permission reg1) 
    \<and> (check_read_permission reg2) 
    \<and> (typical_flags state)\<close>)
  case True
  then show ?thesis 
    using assms
    by(simp add: STORE_STATIC_DATA_decomp_manipulation state_manipulation_simps)
next
  case False
  then have
    \<open>STORE_STATIC_DATA reg1 reg2 state = standard_error state\<close>
    by(simp add: instruction_impl_defs state_manipulation_simps, linarith)
  then show ?thesis 
    by(simp add: state_manipulation_simps)
qed

text\<open>The following are lemmas of STORE\_STATIC\_DATA on the initial state.\<close>

lemma (in Ironbark_world) read_flag_STORE_STATIC_DATA_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (STORE_STATIC_DATA reg1 reg2 start_state) = 0\<close>
    \<open>get_end_call   (STORE_STATIC_DATA reg1 reg2 start_state) = 0\<close>
    \<open>get_end_return (STORE_STATIC_DATA reg1 reg2 start_state) = 0\<close>
    \<open>get_halt       (STORE_STATIC_DATA reg1 reg2 start_state) = 0\<close>
    \<open>get_error      (STORE_STATIC_DATA reg1 reg2 start_state) = 0\<close>
  using assms
  by(simp_all add: read_flag_STORE_STATIC_DATA initial_state_simps)

lemma (in Ironbark_world) common_flags_STORE_STATIC_DATA_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>typical_flags (STORE_STATIC_DATA reg1 reg2 start_state)\<close>
  using assms
  by(simp add: read_flag_STORE_STATIC_DATA_initial_state)

lemma (in Ironbark_world) read_memory_STORE_STATIC_DATA_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (STORE_STATIC_DATA reg1 reg2 start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (STORE_STATIC_DATA reg1 reg2 start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_dynamic_memory  address (STORE_STATIC_DATA reg1 reg2 start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_STORE_STATIC_DATA_same)

lemma (in Ironbark_world) read_last_ip_STORE_STATIC_DATA_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref 
      (STORE_STATIC_DATA reg1 reg2 start_state) 
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_STORE_STATIC_DATA initial_state_simps)

lemma (in Ironbark_world) read_ip_STORE_STATIC_DATA_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (STORE_STATIC_DATA reg1 reg2 start_state) 
    = (read_register instruction_pointer_ref start_state) + 1\<close>
  using assms
  by(simp add: read_ip_STORE_STATIC_DATA initial_state_simps)

end