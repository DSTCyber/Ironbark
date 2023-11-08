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

subsubsection \<open>STORE\_OUTPUT\_DATA Instruction Interface\<close>

theory STORE_OUTPUT_DATA_top

imports
  STORE_OUTPUT_DATA_decomposition
  STORE_OUTPUT_DATA_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) STORE_OUTPUT_DATA_decomp_all =
  STORE_OUTPUT_DATA_decomp_state
  STORE_OUTPUT_DATA_decomp_mixed
  STORE_OUTPUT_DATA_decomp_manipulation

lemmas (in Ironbark_world) STORE_OUTPUT_DATA_simps = 
  flag_STORE_OUTPUT_DATA
  memory_STORE_OUTPUT_DATA_same
  memory_STORE_OUTPUT_DATA_diff
  read_flag_STORE_OUTPUT_DATA
  common_flags_STORE_OUTPUT_DATA
  read_register_STORE_OUTPUT_DATA
  read_ip_STORE_OUTPUT_DATA
  read_cycles_STORE_OUTPUT_DATA
  read_last_ip_STORE_OUTPUT_DATA
  read_memory_STORE_OUTPUT_DATA_same
  read_memory_STORE_OUTPUT_DATA_diff
  read_flag_STORE_OUTPUT_DATA_initial_state
  common_flags_STORE_OUTPUT_DATA_initial_state
  read_memory_STORE_OUTPUT_DATA_initial_state
  read_last_ip_STORE_OUTPUT_DATA_initial_state
  read_ip_STORE_OUTPUT_DATA_initial_state
  
end