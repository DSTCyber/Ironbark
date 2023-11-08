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

subsubsection \<open>HALT Instruction Interface\<close>

theory HALT_top

imports
  HALT_decomposition
  HALT_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) HALT_decomp_all =
  HALT_decomp_state
  HALT_decomp_manipulation

lemmas (in Ironbark_world) HALT_simps = 
  flag_HALT
  register_HALT
  memory_HALT
  read_flag_HALT
  common_flags_HALT
  read_register_HALT
  read_memory_HALT
  read_flag_HALT_initial_state
  common_flags_HALT_initial_state
  read_register_HALT_initial_state
  read_memory_HALT_initial_state

end