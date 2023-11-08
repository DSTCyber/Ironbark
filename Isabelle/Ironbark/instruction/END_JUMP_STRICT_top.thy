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

subsubsection \<open>END\_JUMP\_STRICT Instruction Interface\<close>

theory END_JUMP_STRICT_top

imports
  END_JUMP_STRICT_decomposition
  END_JUMP_STRICT_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) END_JUMP_STRICT_decomp_all =
  END_JUMP_STRICT_decomp_state
  END_JUMP_STRICT_decomp_mixed
  END_JUMP_STRICT_decomp_manipulation

lemmas (in Ironbark_world) END_JUMP_STRICT_simps = 
  flag_END_JUMP_STRICT
  memory_END_JUMP_STRICT
  read_flag_END_JUMP_STRICT
  common_flags_END_JUMP_STRICT
  read_register_END_JUMP_STRICT
  read_ip_END_JUMP_STRICT
  read_cycles_END_JUMP_STRICT
  read_last_ip_END_JUMP_STRICT
  read_memory_END_JUMP_STRICT
  END_JUMP_STRICT_initial_state_errors
  
end