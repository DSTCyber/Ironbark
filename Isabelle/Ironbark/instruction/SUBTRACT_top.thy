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

subsubsection \<open>SUBTRACT Instruction Interface\<close>

theory SUBTRACT_top

imports
  SUBTRACT_decomposition
  SUBTRACT_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) SUBTRACT_decomp_all =
  SUBTRACT_decomp_state
  SUBTRACT_decomp_mixed
  SUBTRACT_decomp_manipulation

lemmas (in Ironbark_world) SUBTRACT_simps = 
  flag_SUBTRACT
  memory_SUBTRACT
  read_flag_SUBTRACT
  common_flags_SUBTRACT
  read_register_SUBTRACT_diff
  read_register_SUBTRACT_same
  read_ip_SUBTRACT
  read_cycles_SUBTRACT
  read_last_ip_SUBTRACT
  read_memory_SUBTRACT
  write_register_SUBTRACT_same
  read_flag_SUBTRACT_initial_state
  common_flags_SUBTRACT_initial_state
  read_memory_SUBTRACT_initial_state
  read_last_ip_SUBTRACT_initial_state
  read_ip_SUBTRACT_initial_state
  
end