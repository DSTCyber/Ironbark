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

subsubsection \<open>LESS\_THAN Instruction Interface\<close>

theory LESS_THAN_top

imports
  LESS_THAN_decomposition
  LESS_THAN_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) LESS_THAN_decomp_all =
  LESS_THAN_decomp_state
  LESS_THAN_decomp_mixed
  LESS_THAN_decomp_manipulation

lemmas (in Ironbark_world) LESS_THAN_simps = 
  flag_LESS_THAN
  memory_LESS_THAN
  read_flag_LESS_THAN
  common_flags_LESS_THAN
  read_register_LESS_THAN_diff
  read_register_LESS_THAN_same
  read_ip_LESS_THAN
  read_cycles_LESS_THAN
  read_last_ip_LESS_THAN
  read_memory_LESS_THAN
  write_register_LESS_THAN_same
  read_flag_LESS_THAN_initial_state
  common_flags_LESS_THAN_initial_state
  read_memory_LESS_THAN_initial_state
  read_last_ip_LESS_THAN_initial_state
  read_ip_LESS_THAN_initial_state
  
end