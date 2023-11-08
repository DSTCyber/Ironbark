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

subsubsection \<open>SHIFT\_RIGHT Instruction Interface\<close>

theory SHIFT_RIGHT_top

imports
  SHIFT_RIGHT_decomposition
  SHIFT_RIGHT_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) SHIFT_RIGHT_decomp_all =
  SHIFT_RIGHT_decomp_state
  SHIFT_RIGHT_decomp_mixed
  SHIFT_RIGHT_decomp_manipulation

lemmas (in Ironbark_world) SHIFT_RIGHT_simps = 
  flag_SHIFT_RIGHT
  memory_SHIFT_RIGHT
  read_flag_SHIFT_RIGHT
  common_flags_SHIFT_RIGHT
  read_register_SHIFT_RIGHT_diff
  read_register_SHIFT_RIGHT_same
  read_ip_SHIFT_RIGHT
  read_cycles_SHIFT_RIGHT
  read_last_ip_SHIFT_RIGHT
  read_memory_SHIFT_RIGHT
  write_register_SHIFT_RIGHT_same
  read_flag_SHIFT_RIGHT_initial_state
  common_flags_SHIFT_RIGHT_initial_state
  read_memory_SHIFT_RIGHT_initial_state
  read_last_ip_SHIFT_RIGHT_initial_state
  read_ip_SHIFT_RIGHT_initial_state
  
end