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

subsubsection \<open>RANDOMISE Instruction Interface\<close>

theory RANDOMISE_top

imports
  RANDOMISE_decomposition
  RANDOMISE_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) RANDOMISE_decomp_all =
  RANDOMISE_decomp_state
  RANDOMISE_decomp_mixed
  RANDOMISE_decomp_manipulation

lemmas (in Ironbark_world) RANDOMISE_simps = 
  flag_RANDOMISE
  memory_RANDOMISE
  read_flag_RANDOMISE
  common_flags_RANDOMISE
  read_register_RANDOMISE_diff
  read_register_RANDOMISE_same
  read_ip_RANDOMISE
  read_cycles_RANDOMISE
  read_last_ip_RANDOMISE
  read_memory_RANDOMISE
  write_register_RANDOMISE_same
  read_flag_RANDOMISE_initial_state
  common_flags_RANDOMISE_initial_state
  read_memory_RANDOMISE_initial_state
  read_last_ip_RANDOMISE_initial_state
  read_ip_RANDOMISE_initial_state
  
end