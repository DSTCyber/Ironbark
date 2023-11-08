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

subsubsection \<open>Simplification Rules Over Register\<close>

theory register_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules that apply register read and write
 operations to a state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma flag_state_write_register:
  assumes
    \<open>regID \<in> registers\<close>
  shows
    \<open>flag_state (write_register regID value state) = flag_state state\<close>
  using assms by(simp add: write_register_def)

lemma memory_write_register:
  \<open>program_memory (write_register regID value state) = program_memory state\<close>
  \<open>call_memory    (write_register regID value state) = call_memory    state\<close>
  \<open>static_memory  (write_register rgeID value state) = static_memory  state\<close>
  \<open>dynamic_memory (write_register regID value state) = dynamic_memory state\<close>
  \<open>input_memory   (write_register regID value state) = input_memory   state\<close>
  \<open>output_memory  (write_register regID value state) = output_memory  state\<close>
  by(simp_all add: write_register_def)

lemma (in Ironbark_world) read_flag_write_register:
  assumes
    \<open>regID \<in> registers\<close>
  shows
    \<open>get_end_jump   (write_register regID value state) = get_end_jump   state\<close>
    \<open>get_end_call   (write_register regID value state) = get_end_call   state\<close>
    \<open>get_end_return (write_register regID value state) = get_end_return state\<close>
    \<open>get_halt       (write_register regID value state) = get_halt       state\<close>
    \<open>get_error      (write_register regID value state) = get_error      state\<close>
  using assms by (simp_all add: flag_state_write_register state_manipulation_decomp)

lemma (in Ironbark_world) common_flags_write_register:
  assumes
    \<open>regID \<in> registers\<close>
  shows
    \<open>typical_flags    (write_register regID value state) = typical_flags    state\<close>
    \<open>end_call_flags   (write_register regID value state) = end_call_flags   state\<close>
    \<open>end_return_flags (write_register regID value state) = end_return_flags state\<close>
    \<open>end_jump_flags   (write_register regID value state) = end_jump_flags   state\<close>
    \<open>halt_flags       (write_register regID value state) = halt_flags       state\<close>
    \<open>error_flags      (write_register regID value state) = error_flags      state\<close>
  using assms
  by(simp_all add: read_flag_write_register)

lemma same_registers_read_write:
  assumes
    \<open>regID \<in> registers\<close>
  shows
    \<open>read_register regID (write_register regID value state) = value\<close>
  using assms by(simp add: read_register_def write_register_def)

lemma diff_registers_read_write:
  assumes
    \<open>regID1 \<noteq> regID2\<close>
  shows
    \<open>read_register  regID1 (write_register regID2 value state) 
    = read_register regID1 state\<close>
  using assms by(simp add: write_register_def read_register_def)

lemma (in Ironbark_world) read_memory_write_register:
  \<open>read_program_memory  address (write_register regID value state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (write_register regID value state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (write_register regID value state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (write_register regID value state) 
  = read_dynamic_memory address state\<close>

  \<open>read_input_memory    address (write_register regID value state) 
  = read_input_memory   address state\<close>
  by (simp_all add: memory_write_register
      read_program_memory_def read_call_memory_def
      read_static_memory_def read_dynamic_memory_def
      read_input_memory_def)

lemma same_registers_write_read:
  assumes
    \<open>regID \<in> registers\<close>
    \<open>register_state state regID = Some value\<close>
  shows
    \<open>write_register regID (read_register regID state) state = state\<close>
  using assms by(simp add: read_register_def write_register_def map_upd_triv)

lemma same_registers_write_write:
  shows
    \<open>write_register   regID value1 (write_register regID value2 state) 
    = write_register  regID value1 state\<close>
  by(simp add: write_register_def)

lemma register_state_write_backup:
  shows
    \<open>register_state   (write_register regID value1 (backup_registers_before_call state)) 
    = register_state  (write_register regID value1 state)\<close>
  by(simp add: backup_registers_before_call_def write_register_def)

end