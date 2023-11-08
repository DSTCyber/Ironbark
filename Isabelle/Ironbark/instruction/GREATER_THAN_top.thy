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

subsubsection \<open>GREATER\_THAN Instruction Interface\<close>

theory GREATER_THAN_top

imports
  GREATER_THAN_decomposition
  GREATER_THAN_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) GREATER_THAN_decomp_all =
  GREATER_THAN_decomp_state
  GREATER_THAN_decomp_mixed
  GREATER_THAN_decomp_manipulation

lemmas (in Ironbark_world) GREATER_THAN_simps = 
  flag_GREATER_THAN
  memory_GREATER_THAN
  read_flag_GREATER_THAN
  common_flags_GREATER_THAN
  read_register_GREATER_THAN_diff
  read_register_GREATER_THAN_same
  read_ip_GREATER_THAN
  read_cycles_GREATER_THAN
  read_last_ip_GREATER_THAN
  read_memory_GREATER_THAN
  write_register_GREATER_THAN_same
  read_flag_GREATER_THAN_initial_state
  common_flags_GREATER_THAN_initial_state
  read_memory_GREATER_THAN_initial_state
  read_last_ip_GREATER_THAN_initial_state
  read_ip_GREATER_THAN_initial_state
  
end