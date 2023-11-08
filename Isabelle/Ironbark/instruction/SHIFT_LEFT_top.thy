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

subsubsection \<open>SHIFT\_LEFT Instruction Interface\<close>

theory SHIFT_LEFT_top

imports
  SHIFT_LEFT_decomposition
  SHIFT_LEFT_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) SHIFT_LEFT_decomp_all =
  SHIFT_LEFT_decomp_state
  SHIFT_LEFT_decomp_mixed
  SHIFT_LEFT_decomp_manipulation

lemmas (in Ironbark_world) SHIFT_LEFT_simps = 
  flag_SHIFT_LEFT
  memory_SHIFT_LEFT
  read_flag_SHIFT_LEFT
  common_flags_SHIFT_LEFT
  read_register_SHIFT_LEFT_diff
  read_register_SHIFT_LEFT_same
  read_ip_SHIFT_LEFT
  read_cycles_SHIFT_LEFT
  read_last_ip_SHIFT_LEFT
  read_memory_SHIFT_LEFT
  write_register_SHIFT_LEFT_same
  read_flag_SHIFT_LEFT_initial_state
  common_flags_SHIFT_LEFT_initial_state
  read_memory_SHIFT_LEFT_initial_state
  read_last_ip_SHIFT_LEFT_initial_state
  read_ip_SHIFT_LEFT_initial_state
  
end