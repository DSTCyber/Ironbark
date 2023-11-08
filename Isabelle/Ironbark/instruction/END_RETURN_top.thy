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

subsubsection \<open>END\_RETURN Instruction Interface\<close>

theory END_RETURN_top

imports
  END_RETURN_decomposition
  END_RETURN_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) END_RETURN_decomp_all =
  END_RETURN_decomp_state
  END_RETURN_decomp_mixed
  END_RETURN_decomp_manipulation

lemmas (in Ironbark_world) END_RETURN_simps = 
  flag_END_RETURN
  memory_END_RETURN
  read_flag_END_RETURN
  common_flags_END_RETURN
  read_register_END_RETURN
  read_ip_END_RETURN
  read_cycles_END_RETURN
  read_last_ip_END_RETURN
  read_memory_END_RETURN
  END_RETURN_initial_state_errors
  
end