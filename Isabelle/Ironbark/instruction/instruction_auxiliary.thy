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

subsection \<open>Properties of Ironbark Instructions\<close>

theory instruction_auxiliary

imports
  "Ironbark_state_manipulation.state_manipulation_top"
  instruction_implementations

begin

text \<open>We use this file as an anchor point for the start of the instruction layer of 
reasoning.\<close>

text \<open>For convenience, we gather the definitions of each instruction into 
\<open>instruction_impl_defs\<close>.\<close>

lemmas (in Ironbark_world) instruction_impl_defs = 
  ERROR0_def
  ERROR1_def
  NOP_def
  LOAD_IMMEDIATE_def
  LOAD_STATIC_DATA_def
  STORE_STATIC_DATA_def
  LOAD_DYNAMIC_DATA_def
  STORE_DYNAMIC_DATA_def
  LOAD_INPUT_DATA_def
  STORE_OUTPUT_DATA_def
  COPY_def
  ADD_def
  SUBTRACT_def
  SHIFT_LEFT_def
  SHIFT_RIGHT_def
  BITWISE_AND_def
  BITWISE_OR_def
  BITWISE_XOR_def
  BITWISE_NAND_def
  BITWISE_NOT_def
  LESS_THAN_def
  GREATER_THAN_def
  EQUALS_def
  NOT_EQUALS_def
  RANDOMISE_def
  END_JUMP_def
  END_JUMP_STRICT_def
  JUMP_def
  CONDITIONAL_JUMP_def
  END_CALL_def
  CALL_def
  END_RETURN_def
  RETURN_def
  HALT_def
  ILLEGAL_def

end