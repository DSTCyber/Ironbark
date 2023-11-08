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

subsubsection \<open>LOAD\_STATIC\_DATA Instruction Interface\<close>

theory LOAD_STATIC_DATA_top

imports
  LOAD_STATIC_DATA_decomposition
  LOAD_STATIC_DATA_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) LOAD_STATIC_DATA_decomp_all =
  LOAD_STATIC_DATA_decomp_state
  LOAD_STATIC_DATA_decomp_mixed
  LOAD_STATIC_DATA_decomp_manipulation

lemmas (in Ironbark_world) LOAD_STATIC_DATA_simps = 
  flag_LOAD_STATIC_DATA
  memory_LOAD_STATIC_DATA
  read_flag_LOAD_STATIC_DATA
  common_flags_LOAD_STATIC_DATA
  read_register_LOAD_STATIC_DATA_diff
  read_register_LOAD_STATIC_DATA_same
  read_ip_LOAD_STATIC_DATA
  read_cycles_LOAD_STATIC_DATA
  read_last_ip_LOAD_STATIC_DATA
  read_memory_LOAD_STATIC_DATA
  write_register_LOAD_STATIC_DATA_same
  read_flag_LOAD_STATIC_DATA_initial_state
  common_flags_LOAD_STATIC_DATA_initial_state
  read_memory_LOAD_STATIC_DATA_initial_state
  read_last_ip_LOAD_STATIC_DATA_initial_state
  read_ip_LOAD_STATIC_DATA_initial_state
  
end