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

subsubsection \<open>Reorder Rules For Memory\<close>

theory memory_reorder

imports
  state_manipulation_simps

begin

text \<open>This file contains reordering rules that apply write memory operations to a 
state.\<close>

text \<open>In this instance, we show that writes to the same memory space at different 
addresses can be freely reordered.\<close>

lemma (in Ironbark_world) diff_addr_write_write:
  fixes
    value1 value2 :: \<open>96 word\<close>
    and value3 value4 :: \<open>64 word\<close>
  assumes
    \<open>address1 \<noteq> address2\<close>
  shows
    \<open>write_program_memory   address1 value1 
      (write_program_memory address2 value2 state) 
    = write_program_memory  address2 value2 
      (write_program_memory address1 value1 state)\<close>

    \<open>write_call_memory      address1 value3 
      (write_call_memory    address2 value4 state) 
    = write_call_memory     address2 value4 
      (write_call_memory    address1 value3 state)\<close>

    \<open>write_static_memory    address1 value3 
      (write_static_memory  address2 value4 state) 
    = write_static_memory   address2 value4 
      (write_static_memory  address1 value3 state)\<close>

    \<open>write_dynamic_memory   address1 value3 
      (write_dynamic_memory address2 value4 state) 
    = write_dynamic_memory  address2 value4 
      (write_dynamic_memory address1 value3 state)\<close>

    \<open>write_output_memory    address1 value3 
      (write_output_memory  address2 value4 state) 
    = write_output_memory   address2 value4 
      (write_output_memory  address1 value3 state)\<close>
  using assms by (simp_all add: state_manipulation_decomp fun_upd_twist)

end