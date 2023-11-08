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

subsubsection \<open>ADD Instruction Interface\<close>

theory ADD_top

imports
  ADD_decomposition
  ADD_simps

begin

text \<open>This file provides a single point for importing all the content for the ADD 
instruction.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) ADD_decomp_all =
  ADD_decomp_state
  ADD_decomp_mixed
  ADD_decomp_manipulation

lemmas (in Ironbark_world) ADD_simps = 
  flag_ADD
  memory_ADD
  read_flag_ADD
  common_flags_ADD
  read_register_ADD_diff
  read_register_ADD_same
  read_ip_ADD
  read_cycles_ADD
  read_last_ip_ADD
  read_memory_ADD
  write_register_ADD_same
  read_flag_ADD_initial_state
  common_flags_ADD_initial_state
  read_memory_ADD_initial_state
  read_last_ip_ADD_initial_state
  read_ip_ADD_initial_state
  
end