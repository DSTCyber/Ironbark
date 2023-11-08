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

subsubsection \<open>BITWISE\_OR Instruction Interface\<close>

theory BITWISE_OR_top

imports
  BITWISE_OR_decomposition
  BITWISE_OR_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) BITWISE_OR_decomp_all =
  BITWISE_OR_decomp_state
  BITWISE_OR_decomp_mixed
  BITWISE_OR_decomp_manipulation

lemmas (in Ironbark_world) BITWISE_OR_simps = 
  flag_BITWISE_OR
  memory_BITWISE_OR
  read_flag_BITWISE_OR
  common_flags_BITWISE_OR
  read_register_BITWISE_OR_diff
  read_register_BITWISE_OR_same
  read_ip_BITWISE_OR
  read_cycles_BITWISE_OR
  read_last_ip_BITWISE_OR
  read_memory_BITWISE_OR
  write_register_BITWISE_OR_same
  read_flag_BITWISE_OR_initial_state
  common_flags_BITWISE_OR_initial_state
  read_memory_BITWISE_OR_initial_state
  read_last_ip_BITWISE_OR_initial_state
  read_ip_BITWISE_OR_initial_state
  
end