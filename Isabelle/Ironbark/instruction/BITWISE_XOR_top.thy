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

subsubsection \<open>BITWISE\_XOR Instruction Interface\<close>

theory BITWISE_XOR_top

imports
  BITWISE_XOR_decomposition
  BITWISE_XOR_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) BITWISE_XOR_decomp_all =
  BITWISE_XOR_decomp_state
  BITWISE_XOR_decomp_mixed
  BITWISE_XOR_decomp_manipulation

lemmas (in Ironbark_world) BITWISE_XOR_simps = 
  flag_BITWISE_XOR
  memory_BITWISE_XOR
  read_flag_BITWISE_XOR
  common_flags_BITWISE_XOR
  read_register_BITWISE_XOR_diff
  read_register_BITWISE_XOR_same
  read_ip_BITWISE_XOR
  read_cycles_BITWISE_XOR
  read_last_ip_BITWISE_XOR
  read_memory_BITWISE_XOR
  write_register_BITWISE_XOR_same
  read_flag_BITWISE_XOR_initial_state
  common_flags_BITWISE_XOR_initial_state
  read_memory_BITWISE_XOR_initial_state
  read_last_ip_BITWISE_XOR_initial_state
  read_ip_BITWISE_XOR_initial_state
  
end