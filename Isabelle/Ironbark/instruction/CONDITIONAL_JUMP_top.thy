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

subsubsection \<open>CONDITIONAL\_JUMP Instruction Interface\<close>

theory CONDITIONAL_JUMP_top

imports
  CONDITIONAL_JUMP_decomposition
  CONDITIONAL_JUMP_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) CONDITIONAL_JUMP_decomp_all =
  CONDITIONAL_JUMP_decomp_state
  CONDITIONAL_JUMP_decomp_mixed
  CONDITIONAL_JUMP_decomp_manipulation

lemmas (in Ironbark_world) CONDITIONAL_JUMP_simps = 
  flag_CONDITIONAL_JUMP
  memory_CONDITIONAL_JUMP
  read_flag_CONDITIONAL_JUMP
  common_flags_CONDITIONAL_JUMP_fall
  common_flags_CONDITIONAL_JUMP_jump
  read_register_CONDITIONAL_JUMP
  read_ip_CONDITIONAL_JUMP_jump
  read_ip_CONDITIONAL_JUMP_fall
  read_cycles_CONDITIONAL_JUMP
  read_last_ip_CONDITIONAL_JUMP
  read_memory_CONDITIONAL_JUMP
  read_flag_CONDITIONAL_JUMP_initial_state
  common_flags_CONDITIONAL_JUMP_initial_state
  read_memory_CONDITIONAL_JUMP_initial_state
  read_last_ip_CONDITIONAL_JUMP_initial_state
  read_ip_CONDITIONAL_JUMP_initial_state
  
end