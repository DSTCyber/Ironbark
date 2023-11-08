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

subsubsection \<open>CALL Instruction Interface\<close>

theory CALL_top

imports
  CALL_decomposition
  CALL_simps

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) CALL_decomp_all =
  CALL_decomp_state
  CALL_decomp_mixed
  CALL_decomp_manipulation

lemmas (in Ironbark_world) CALL_simps = 
  memory_CALL
  read_flag_CALL
  common_flags_CALL
  read_register_CALL
  read_ip_CALL
  read_cycles_CALL
  read_last_ip_CALL
  read_call_pointer_CALL
  read_memory_CALL
  read_call_memory_CALL
  read_flag_CALL_initial_state
  common_flags_CALL_initial_state
  read_memory_CALL_initial_state
  read_last_ip_CALL_initial_state
  read_ip_CALL_initial_state
  
end