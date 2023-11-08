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

subsubsection \<open>RETURN Instruction Interface\<close>

theory RETURN_top

imports
  RETURN_decomposition
  RETURN_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) RETURN_decomp_all =
  RETURN_decomp_state
  RETURN_decomp_mixed
  RETURN_decomp_manipulation

lemmas (in Ironbark_world) RETURN_simps = 
  memory_RETURN
  read_flag_RETURN
  common_flags_RETURN
  read_ip_RETURN
  read_cycles_RETURN
  read_last_ip_RETURN
  read_memory_RETURN
  read_call_memory_RETURN
  read_flag_RETURN_initial_state
  common_flags_RETURN_initial_state
  read_memory_RETURN_initial_state
  read_last_ip_RETURN_initial_state
  read_ip_RETURN_initial_state
  
end