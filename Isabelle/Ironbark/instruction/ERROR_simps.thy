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

subsubsection \<open>Simplification Rules Over ERROR0 and ERROR1\<close>

theory ERROR_simps

imports
  ERROR_decomposition

begin

text \<open>As with most instructions, we provide various simplification rules for the 
error0 and error1 instructions. The various rules are 
primarily showing non-interference, or the specific changes to a specific value from 
the instructions.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_ERROR:
  \<open>flag_state (ERROR0 state) = flag_state (set_halt (set_error state))\<close>

  \<open>flag_state (ERROR1 state) = flag_state (set_halt (set_error state))\<close>
  by(simp_all add: ERROR_decomp_manipulation standard_error_def)

lemma (in Ironbark_world) register_ERROR:
  \<open>register_state (ERROR0 state) = register_state state\<close>

  \<open>register_state (ERROR1 state) = register_state state\<close>
  by(simp_all add: ERROR_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) memory_ERROR:
  \<open>program_memory (ERROR0 state) = program_memory state\<close>
  \<open>call_memory    (ERROR0 state) = call_memory    state\<close>
  \<open>static_memory  (ERROR0 state) = static_memory  state\<close>
  \<open>dynamic_memory (ERROR0 state) = dynamic_memory state\<close>
  \<open>input_memory   (ERROR0 state) = input_memory   state\<close>
  \<open>output_memory  (ERROR0 state) = output_memory  state\<close>

  \<open>program_memory (ERROR1 state) = program_memory state\<close>
  \<open>call_memory    (ERROR1 state) = call_memory    state\<close>
  \<open>static_memory  (ERROR1 state) = static_memory  state\<close>
  \<open>dynamic_memory (ERROR1 state) = dynamic_memory state\<close>
  \<open>input_memory   (ERROR1 state) = input_memory   state\<close>
  \<open>output_memory  (ERROR1 state) = output_memory  state\<close>
  by(simp_all add: ERROR_decomp_state)

lemma (in Ironbark_world) read_flag_ERROR:
  \<open>get_end_jump   (ERROR0 state) = get_end_jump state\<close>
  \<open>get_end_call   (ERROR0 state) = get_end_call state\<close>
  \<open>get_end_return (ERROR0 state) = get_end_return state\<close>
  \<open>get_halt       (ERROR0 state) = 1\<close>
  \<open>get_error      (ERROR0 state) = 1\<close>

  \<open>get_end_jump   (ERROR1 state) = get_end_jump state\<close>
  \<open>get_end_call   (ERROR1 state) = get_end_call state\<close>
  \<open>get_end_return (ERROR1 state) = get_end_return state\<close>
  \<open>get_halt       (ERROR1 state) = 1\<close>
  \<open>get_error      (ERROR1 state) = 1\<close>
  by(auto simp add: ERROR_decomp_manipulation state_manipulation_simps)

lemma (in Ironbark_world) common_flags_ERROR:
  \<open>\<not> typical_flags    (ERROR0 state)\<close>
  \<open>\<not> end_jump_flags   (ERROR0 state)\<close>
  \<open>\<not> end_call_flags   (ERROR0 state)\<close>
  \<open>\<not> end_return_flags (ERROR0 state)\<close>
  \<open>\<not> halt_flags       (ERROR0 state)\<close>

  \<open>\<not> typical_flags    (ERROR1 state)\<close>
  \<open>\<not> end_jump_flags   (ERROR1 state)\<close>
  \<open>\<not> end_call_flags   (ERROR1 state)\<close>
  \<open>\<not> end_return_flags (ERROR1 state)\<close>
  \<open>\<not> halt_flags       (ERROR1 state)\<close>
  by(simp_all add: read_flag_ERROR)

lemma (in Ironbark_world) read_register_ERROR:
  \<open>read_register regID (ERROR0 state) = read_register regID state\<close>

  \<open>read_register regID (ERROR1 state) = read_register regID state\<close>
  by(simp_all add: read_register_def register_ERROR)

lemma (in Ironbark_world) read_memory_ERROR:
  \<open>read_program_memory  address (ERROR0 state) = read_program_memory  address state\<close>
  \<open>read_call_memory     address (ERROR0 state) = read_call_memory     address state\<close>
  \<open>read_static_memory   address (ERROR0 state) = read_static_memory   address state\<close>
  \<open>read_dynamic_memory  address (ERROR0 state) = read_dynamic_memory  address state\<close>

  \<open>read_program_memory  address (ERROR1 state) = read_program_memory  address state\<close>
  \<open>read_call_memory     address (ERROR1 state) = read_call_memory     address state\<close>
  \<open>read_static_memory   address (ERROR1 state) = read_static_memory   address state\<close>
  \<open>read_dynamic_memory  address (ERROR1 state) = read_dynamic_memory  address state\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_simps)

text\<open>The following are lemmas of ERROR on the initial state.\<close>

lemma (in Ironbark_world) read_flag_ERROR_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>get_end_jump   (ERROR0 start_state) = 0\<close>
    \<open>get_end_call   (ERROR0 start_state) = 0\<close>
    \<open>get_end_return (ERROR0 start_state) = 0\<close>
    \<open>get_halt       (ERROR0 start_state) = 1\<close>
    \<open>get_error      (ERROR0 start_state) = 1\<close>

    \<open>get_end_jump   (ERROR1 start_state) = 0\<close>
    \<open>get_end_call   (ERROR1 start_state) = 0\<close>
    \<open>get_end_return (ERROR1 start_state) = 0\<close>
    \<open>get_halt       (ERROR1 start_state) = 1\<close>
    \<open>get_error      (ERROR1 start_state) = 1\<close>
  using assms
  by(auto simp add: read_flag_ERROR initial_state_simps)

lemma (in Ironbark_world) common_flags_ERROR_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>error_flags (ERROR0 start_state)\<close>

    \<open>error_flags (ERROR1 start_state)\<close>
  using assms
  by(simp_all add: read_flag_ERROR_initial_state)

lemma (in Ironbark_world) read_register_ERROR_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<open>read_register regID (ERROR0 start_state) = read_register regID start_state\<close>

    \<open>read_register regID (ERROR1 start_state) = read_register regID start_state\<close>
  using assms
  by(simp_all add: read_register_ERROR)

lemma (in Ironbark_world) read_memory_ERROR_initial_state:
  fixes
    program :: \<open>(64 word, 96 word) map\<close>
  defines
    \<open>start_state \<equiv> initial_state\<lparr>program_memory := program\<rparr>\<close>
  shows
    \<comment>\<open>error0\<close>
    \<open>read_program_memory  address (ERROR0 start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (ERROR0 start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (ERROR0 start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (ERROR0 start_state) 
    = read_dynamic_memory address start_state\<close>

    \<comment>\<open>error1\<close>
    \<open>read_program_memory  address (ERROR1 start_state) 
    = read_program_memory address start_state\<close>

    \<open>read_call_memory     address (ERROR1 start_state) 
    = read_call_memory    address start_state\<close>

    \<open>read_static_memory   address (ERROR1 start_state) 
    = read_static_memory  address start_state\<close>

    \<open>read_dynamic_memory  address (ERROR1 start_state) 
    = read_dynamic_memory address start_state\<close>
  using assms
  by(simp_all add: read_memory_ERROR)

end