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

subsubsection \<open>Interface for State Manipulation Decomposition\<close>

theory state_manipulation_decomposition

imports
  post_instruction_decomp
  register_decomposition
  flag_decomposition
  memory_decomposition

begin

text \<open>In this section we collect up all the decomposition rules for decomposing 
state manipulation operations into state level operations.\<close>

text \<open>Note that we also include the register\_set lemmas as a matter of convenience 
because we found that it is often needed in order to apply the decomposition rules. We 
also include slice\_def and slice1\_def, primarily to help the get\_opcode, get\_reg1, 
get\_reg2, reg\_reg3, and get\_immediate operations decompose into a more 
understandable form.\<close>

lemmas (in Ironbark_world) state_manipulation_decomp =
  register_set
  register_decomp
  flag_decomp
  memory_decomp

  check_read_permission_def 
  check_write_permission_def

  halted_def 
  returned_def 
  called_def
  
  get_opcode_def 
  get_immediate_def
  get_reg1_def 
  get_reg2_def 
  get_reg3_def
  slice_def 
  slice1_def
  
  standard_error_def
  post_instruction_decomp_state
  backup_registers_before_call_def
  restore_registers_after_return_def

end