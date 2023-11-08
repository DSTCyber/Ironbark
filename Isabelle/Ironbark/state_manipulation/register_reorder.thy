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

subsubsection \<open>Reordering Rules for Registers\<close>

theory register_reorder

imports
  state_manipulation_simps

begin

text \<open>This file contains reordering rules that apply write register to a state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) write_register_write_memory:
  fixes
    value1 :: \<open>96 word\<close> 
    and value2 :: \<open>64 word\<close>
  assumes
    \<open>regID \<in> registers\<close>
  shows
    \<open>write_register regID value (write_program_memory  address value1 state) 
    = write_program_memory address value1 (write_register regID value state)\<close>
  
    \<open>write_register regID value (write_call_memory     address value2 state) 
    = write_call_memory    address value2 (write_register regID value state)\<close>
  
    \<open>write_register regID value (write_static_memory   address value2 state) 
    = write_static_memory  address value2 (write_register regID value state)\<close>
  
    \<open>write_register regID value (write_dynamic_memory  address value2 state) 
    = write_dynamic_memory address value2 (write_register regID value state)\<close>
  
    \<open>write_register regID value (write_output_memory   address value2 state) 
    = write_output_memory  address value2 (write_register regID value state)\<close>
  using assms
  by(simp_all add: state_manipulation_decomp)

lemma diff_registers_write_write:
  assumes
    \<open>regID1 \<in> registers\<close>
    \<open>regID2 \<in> registers\<close>
    \<open>regID1 \<noteq> regID2\<close>
  shows
    \<open>write_register   regID1 value1 (write_register regID2 value2 state)
    = write_register  regID2 value2 (write_register regID1 value1 state)\<close>
  using assms by(simp add: write_register_def fun_upd_twist)

lemma (in Ironbark_world) register_post_reorder:
  assumes
    \<open>regID \<notin> {
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      cycles_register_ref
    }\<close>
  shows
    \<open>standard_post_instruction instruction_duration 
      (write_register regID value state) 
    = write_register regID value 
      (standard_post_instruction instruction_duration state)\<close>
  using assms
  apply(simp add: state_manipulation_decomp)
  apply(simp add: write_register_def)
  apply(simp add: fun_upd_twist)
  done

end