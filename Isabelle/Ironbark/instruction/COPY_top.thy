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

subsubsection \<open>COPY Instruction Interface\<close>

theory COPY_top

imports
  COPY_decomposition
  COPY_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) COPY_decomp_all =
  COPY_decomp_state
  COPY_decomp_mixed
  COPY_decomp_manipulation

lemmas (in Ironbark_world) COPY_simps = 
  flag_COPY
  memory_COPY
  read_flag_COPY
  common_flags_COPY
  read_register_COPY_diff
  read_register_COPY_same
  read_ip_COPY
  read_cycles_COPY
  read_last_ip_COPY
  read_memory_COPY
  write_register_COPY_same
  read_flag_COPY_initial_state
  common_flags_COPY_initial_state
  read_memory_COPY_initial_state
  read_last_ip_COPY_initial_state
  read_ip_COPY_initial_state
  
end