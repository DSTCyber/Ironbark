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

subsubsection \<open>Interface for State Manipulation Simplification\<close>

theory state_manipulation_simps

imports
  flag_simps
  register_simps
  memory_simps
  special_simps
  initial_state_simps
  standard_error_simps
  post_instruction_simps
  permission_sets

begin

text \<open>This file provides a single point for importing all the simplification rules at 
the state manipulation layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) flag_simps = 
  register_memory_state_set_clear_flag
  read_register_memory_set_clear_flag
  get_end_jump_set_clear_other
  get_end_jump_set_clear_same
  get_end_call_set_clear_other
  get_end_call_set_clear_same
  get_end_return_set_clear_other
  get_end_return_set_clear_same
  get_halt_set_clear_other
  get_halt_set_clear_same
  get_error_set_clear_other
  get_error_set_clear_same

lemmas (in Ironbark_world) register_simps = 
  flag_state_write_register
  memory_write_register
  read_flag_write_register
  common_flags_write_register
  same_registers_read_write
  diff_registers_read_write
  read_memory_write_register
  same_registers_write_read
  same_registers_write_write
  register_state_write_backup

lemmas (in Ironbark_world) memory_simps = 
  state_write_memory
  read_flag_write_memory
  common_flags_write_memory
  read_register_write_memory
  diff_memory_read_write
  same_addr_read_write
  diff_addr_read_write
  same_addr_write_read
  same_addr_write_write

lemmas (in Ironbark_world) backup_simps = 
  flags_backup_registers_before_call
  registers_backup_registers_before_call
  memory_backup_registers_before_call
  read_flags_backup_registers_before_call
  read_registers_backup_registers_before_call
  read_memory_backup_registers_before_call
  read_call_memory_backup_registers_before_call
  read_call_memory_backup_registers_before_call'

lemmas (in Ironbark_world) restore_simps = 
  flags_restore_registers_after_return
  memory_restore_registers_after_return
  read_flag_restore_registers_after_return
  read_register_after_return_same
  read_register_restore_registers_after_return_diff
  read_memory_restore_registers_after_return

lemmas (in Ironbark_world) initial_state_simps = 
  memory_initial_state
  read_register_initial_state
  flags_initial_state

lemmas (in Ironbark_world) standard_error_simps = 
  memory_register_state_standard_error
  read_flag_standard_error
  read_memory_register_state_standard_error

lemmas (in Ironbark_world) post_instruction_simps = 
  read_register_standard_post_instruction
  read_last_instruction_pointer_standard_post_instruction
  read_instruction_pointer_standard_post_instruction
  read_cycles_register_standard_post_instruction
  memory_standard_post_instruction
  read_memory_standard_post_instruction
  check_status_post_instruction

lemmas check_permission_exclusion =
  check_write_permission_exclusion
  check_read_permission_exclusion

lemmas permission_simps =
  check_permission_sets
  check_write_permission_exclusion
  check_read_permission_exclusion
  check_read_permission_set
  check_write_permission_set

lemmas (in Ironbark_world) state_manipulation_simps = 
  register_set
  flag_simps
  register_simps
  memory_simps
  backup_simps
  restore_simps
  initial_state_simps
  standard_error_simps
  post_instruction_simps
  permission_simps

end