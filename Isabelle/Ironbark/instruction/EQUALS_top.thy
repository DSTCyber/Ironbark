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

subsubsection \<open>EQUALS Instruction Interface\<close>

theory EQUALS_top

imports
  EQUALS_decomposition
  EQUALS_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) EQUALS_decomp_all =
  EQUALS_decomp_state
  EQUALS_decomp_mixed
  EQUALS_decomp_manipulation

lemmas (in Ironbark_world) EQUALS_simps = 
  flag_EQUALS
  memory_EQUALS
  read_flag_EQUALS
  common_flags_EQUALS
  read_register_EQUALS_diff
  read_register_EQUALS_same
  read_ip_EQUALS
  read_cycles_EQUALS
  read_last_ip_EQUALS
  read_memory_EQUALS
  write_register_EQUALS_same
  read_flag_EQUALS_initial_state
  common_flags_EQUALS_initial_state
  read_memory_EQUALS_initial_state
  read_last_ip_EQUALS_initial_state
  read_ip_EQUALS_initial_state
  
end