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

subsubsection \<open>Simplification Rules Over CONDITIONAL\_JUMP\<close>

theory CONDITIONAL_JUMP_simps

imports
  CONDITIONAL_JUMP_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the 
\<open>CONDITIONAL_JUMP\<close> instruction. 
The various rules are primarily showing non-interference, or 
the specific changes to a specific value from the instruction. 
Where needed, we use the `special' 
case where we assume the guards of the instruction will pass.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_CONDITIONAL_JUMP:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
  shows
    \<open>(read_register reg1 state) = 0x00 
    \<Longrightarrow> flag_state (CONDITIONAL_JUMP reg1 immediate state) = flag_state state\<close>

    \<open>(read_register reg1 state) \<noteq> 0x00 
    \<Longrightarrow> flag_state (CONDITIONAL_JUMP reg1 immediate state) 
      = flag_state (set_end_jump state)\<close>
  using assms
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) memory_CONDITIONAL_JUMP:
  \<open>program_memory (CONDITIONAL_JUMP reg1 immediate state) = program_memory  state\<close>
  \<open>call_memory    (CONDITIONAL_JUMP reg1 immediate state) = call_memory     state\<close>
  \<open>static_memory  (CONDITIONAL_JUMP reg1 immediate state) = static_memory   state\<close>
  \<open>dynamic_memory (CONDITIONAL_JUMP reg1 immediate state) = dynamic_memory  state\<close>
  \<open>input_memory   (CONDITIONAL_JUMP reg1 immediate state) = input_memory    state\<close>
  \<open>output_memory  (CONDITIONAL_JUMP reg1 immediate state) = output_memory   state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_flag_CONDITIONAL_JUMP:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
  shows
    \<open>get_end_call   (CONDITIONAL_JUMP reg1 immediate state) = 0\<close>
    \<open>get_end_return (CONDITIONAL_JUMP reg1 immediate state) = 0\<close>
    \<open>get_halt       (CONDITIONAL_JUMP reg1 immediate state) = 0\<close>
    \<open>get_error      (CONDITIONAL_JUMP reg1 immediate state) = 0\<close>

    \<open>read_register reg1 state = 0x00 
    \<Longrightarrow> get_end_jump (CONDITIONAL_JUMP reg1 immediate state) = 0\<close>

    \<open>read_register reg1 state \<noteq> 0x00 
    \<Longrightarrow> get_end_jump (CONDITIONAL_JUMP reg1 immediate state) = 1\<close>
  using assms
  by(simp_all add: CONDITIONAL_JUMP_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_CONDITIONAL_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>(read_register reg1 state) = 0x00\<close>
  shows
    \<open>typical_flags (CONDITIONAL_JUMP reg1 immediate state)\<close>
  using assms
  by(simp_all add: read_flag_CONDITIONAL_JUMP)

lemma (in Ironbark_world) common_flags_CONDITIONAL_JUMP_jump:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>(read_register reg1 state) \<noteq> 0x00\<close>
  shows
    \<open>end_jump_flags (CONDITIONAL_JUMP reg1 immediate state)\<close>
  using assms
  by(simp_all add: read_flag_CONDITIONAL_JUMP)

lemma (in Ironbark_world) read_register_CONDITIONAL_JUMP:
  assumes
    \<open>regID \<notin> {
                instruction_pointer_ref,
                last_instruction_pointer_ref,
                cycles_register_ref
              }\<close>
  shows
    \<open>read_register  regID (CONDITIONAL_JUMP reg1 immediate state) 
    = read_register regID state\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_CONDITIONAL_JUMP_jump:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>(read_register reg1 state) \<noteq> 0x00\<close>
  shows
    \<open>read_register instruction_pointer_ref (CONDITIONAL_JUMP reg1 immediate state) 
    = immediate\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_ip_CONDITIONAL_JUMP_fall:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>(read_register reg1 state) = 0x00\<close>
  shows
    \<open>read_register instruction_pointer_ref (CONDITIONAL_JUMP reg1 immediate state) 
    = (read_register instruction_pointer_ref state) + 1\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_cycles_CONDITIONAL_JUMP:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
  shows
    \<open>read_register cycles_register_ref (CONDITIONAL_JUMP reg1 immediate state) 
    = (read_register cycles_register_ref state) + common_instruction_duration\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_last_ip_CONDITIONAL_JUMP:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
  shows
    \<open>read_register last_instruction_pointer_ref (CONDITIONAL_JUMP reg1 immediate state) 
    = (read_register instruction_pointer_ref state)\<close>
  using assms
  by(simp add: instruction_impl_defs state_manipulation_simps)

lemma (in Ironbark_world) read_memory_CONDITIONAL_JUMP:
  \<open>read_program_memory  address (CONDITIONAL_JUMP reg1 immediate state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (CONDITIONAL_JUMP reg1 immediate state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (CONDITIONAL_JUMP reg1 immediate state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (CONDITIONAL_JUMP reg1 immediate state) 
  = read_dynamic_memory address state\<close>
  using memory_CONDITIONAL_JUMP
  by(simp_all add: state_manipulation_decomp)

text\<open>The following are cases of CONDITIONAL\_JUMP over the initial state.\<close>

lemma (in Ironbark_world) read_flag_CONDITIONAL_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_end_call   (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_end_return (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_halt       (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_error      (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
  using assms
proof -
  have 
    \<open>typical_flags start_state\<close>
    \<open>(read_register reg1 start_state) = 0x00\<close>
    using assms
    by(simp_all add: state_manipulation_simps)
  then show
    \<open>get_end_jump   (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_end_call   (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_end_return (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_halt       (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    \<open>get_error      (CONDITIONAL_JUMP reg1 immediate start_state) = 0\<close>
    using assms
    by(simp_all add: CONDITIONAL_JUMP_decomp_manipulation state_manipulation_simps)
qed

lemma (in Ironbark_world) common_flags_CONDITIONAL_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>typical_flags (CONDITIONAL_JUMP reg1 immediate start_state)\<close>
  using assms
  by(simp add: read_flag_CONDITIONAL_JUMP_initial_state)

lemma (in Ironbark_world) read_memory_CONDITIONAL_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_program_memory  address (CONDITIONAL_JUMP reg1 immediate start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (CONDITIONAL_JUMP reg1 immediate start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (CONDITIONAL_JUMP reg1 immediate start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (CONDITIONAL_JUMP reg1 immediate start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_CONDITIONAL_JUMP)

lemma (in Ironbark_world) read_last_ip_CONDITIONAL_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register last_instruction_pointer_ref 
      (CONDITIONAL_JUMP reg1 immediate start_state)
    = (read_register instruction_pointer_ref start_state)\<close>
  using assms
  by(simp add: read_last_ip_CONDITIONAL_JUMP initial_state_simps)

lemma (in Ironbark_world) read_ip_CONDITIONAL_JUMP_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  assumes
    \<open>check_read_permission reg1\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register instruction_pointer_ref (CONDITIONAL_JUMP reg1 immediate start_state) 
    = (read_register instruction_pointer_ref start_state) + 1\<close>
proof -
  have 
    \<open>(read_register reg1 start_state) = 0x00\<close>
    using assms
    by(simp_all add: state_manipulation_simps)
  then show ?thesis
    using assms
    by(simp_all add: read_ip_CONDITIONAL_JUMP_fall state_manipulation_simps)
qed

end