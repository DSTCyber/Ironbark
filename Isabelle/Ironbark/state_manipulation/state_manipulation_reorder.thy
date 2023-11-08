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

subsubsection \<open>Interface for State Manipulation Reordering\<close>

theory state_manipulation_reorder

imports
  flag_reorder
  register_reorder
  memory_reorder

begin

text \<open>This file provides a single point for importing all the content related to 
reordering at the state manipulation layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) register_reorder = 
  write_register_write_memory
  diff_registers_write_write
  register_post_reorder

lemmas (in Ironbark_world) flag_reorder =
  flag_flag_reorder
  post_instruction_flag_reorder
  backup_registers_flag_reorder

lemmas (in Ironbark_world) state_manipulation_reorder =
  permission_simps
  register_reorder
  flag_reorder

end