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

subsubsection \<open>NOP Instruction Interface\<close>

theory NOP_top

imports
  NOP_decomposition
  NOP_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) NOP_decomp_all =
  NOP_decomp_state
  NOP_decomp_mixed
  NOP_decomp_manipulation

lemmas (in Ironbark_world) NOP_simps = 
  flag_NOP
  register_NOP
  memory_NOP
  read_flag_NOP
  common_flags_NOP
  read_register_NOP
  read_ip_NOP
  read_cycles_NOP
  read_last_ip_NOP
  read_memory_NOP
  write_register_NOP_same
  read_flag_NOP_initial_state
  common_flags_NOP_initial_state
  read_memory_NOP_initial_state
  read_last_ip_NOP_initial_state
  read_ip_NOP_initial_state
  
end