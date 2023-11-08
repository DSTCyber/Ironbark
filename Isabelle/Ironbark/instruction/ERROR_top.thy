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

subsubsection \<open>ERROR Instruction Interface\<close>

theory ERROR_top

imports
  ERROR_decomposition
  ERROR_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) ERROR0_decomp_all =
  ERROR_decomp_state(1)
  ERROR_decomp_manipulation(1)
  ERROR_decomp_manipulation2(1)

lemmas (in Ironbark_world) ERROR1_decomp_all =
  ERROR_decomp_state(2)
  ERROR_decomp_manipulation(2)
  ERROR_decomp_manipulation2(2)

lemmas (in Ironbark_world) ERROR_decomp_all =
  ERROR0_decomp_all
  ERROR1_decomp_all

lemmas (in Ironbark_world) ERROR_simps = 
  flag_ERROR
  register_ERROR
  memory_ERROR
  read_flag_ERROR
  common_flags_ERROR
  read_register_ERROR
  read_memory_ERROR
  read_flag_ERROR_initial_state
  common_flags_ERROR_initial_state
  read_register_ERROR_initial_state
  read_memory_ERROR_initial_state
  
end