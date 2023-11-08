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

subsubsection \<open>JUMP Instruction Interface\<close>

theory JUMP_top

imports
  JUMP_decomposition
  JUMP_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) JUMP_decomp_all =
  JUMP_decomp_state
  JUMP_decomp_mixed
  JUMP_decomp_manipulation

lemmas (in Ironbark_world) JUMP_simps = 
  flag_JUMP
  memory_JUMP
  read_flag_JUMP
  common_flags_JUMP
  read_register_JUMP
  read_ip_JUMP
  read_cycles_JUMP
  read_last_ip_JUMP
  read_memory_JUMP
  read_flag_JUMP_initial_state
  common_flags_JUMP_initial_state
  read_memory_JUMP_initial_state
  read_last_ip_JUMP_initial_state
  read_ip_JUMP_initial_state
  
end