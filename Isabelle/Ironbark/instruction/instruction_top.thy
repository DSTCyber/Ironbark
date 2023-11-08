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

theory instruction_top

imports
  instruction_auxiliary
  ERROR_top
  NOP_top
  LOAD_IMMEDIATE_top
  LOAD_STATIC_DATA_top
  STORE_STATIC_DATA_top
  LOAD_DYNAMIC_DATA_top
  STORE_DYNAMIC_DATA_top
  LOAD_INPUT_DATA_top
  STORE_OUTPUT_DATA_top
  COPY_top
  ADD_top
  SUBTRACT_top
  SHIFT_LEFT_top
  SHIFT_RIGHT_top
  BITWISE_AND_top
  BITWISE_OR_top
  BITWISE_XOR_top
  BITWISE_NAND_top
  BITWISE_NOT_top
  LESS_THAN_top
  GREATER_THAN_top
  EQUALS_top
  NOT_EQUALS_top
  RANDOMISE_top
  END_JUMP_top
  END_JUMP_STRICT_top
  JUMP_top
  CONDITIONAL_JUMP_top
  END_CALL_top
  CALL_top
  END_RETURN_top
  RETURN_top
  HALT_top
  ILLEGAL_top

begin

text \<open>This file provides a single point for importing all the content at the 
instruction layer.

We also collect groups of related lemmas and bundle them for easier reference later.\<close>

lemmas (in Ironbark_world) instruction_decomp_manipulation =
  ERROR_decomp_manipulation
  NOP_decomp_manipulation
  LOAD_IMMEDIATE_decomp_manipulation
  LOAD_STATIC_DATA_decomp_manipulation
  STORE_STATIC_DATA_decomp_manipulation
  LOAD_DYNAMIC_DATA_decomp_manipulation
  STORE_DYNAMIC_DATA_decomp_manipulation
  LOAD_INPUT_DATA_decomp_manipulation
  STORE_OUTPUT_DATA_decomp_manipulation
  COPY_decomp_manipulation
  ADD_decomp_manipulation
  SUBTRACT_decomp_manipulation
  SHIFT_LEFT_decomp_manipulation
  SHIFT_RIGHT_decomp_manipulation
  BITWISE_AND_decomp_manipulation
  BITWISE_OR_decomp_manipulation
  BITWISE_XOR_decomp_manipulation
  BITWISE_NAND_decomp_manipulation
  BITWISE_NOT_decomp_manipulation
  LESS_THAN_decomp_manipulation
  GREATER_THAN_decomp_manipulation
  EQUALS_decomp_manipulation
  NOT_EQUALS_decomp_manipulation
  RANDOMISE_decomp_manipulation
  END_JUMP_decomp_manipulation_jump
  END_JUMP_decomp_manipulation_fall
  END_JUMP_STRICT_decomp_manipulation
  JUMP_decomp_manipulation
  CONDITIONAL_JUMP_decomp_manipulation
  END_CALL_decomp_manipulation
  CALL_decomp_manipulation
  END_RETURN_decomp_manipulation
  RETURN_decomp_manipulation
  HALT_decomp_manipulation
  ILLEGAL_decomp_manipulation

lemmas (in Ironbark_world) instruction_decomp_state =
  ERROR_decomp_state
  NOP_decomp_state
  LOAD_IMMEDIATE_decomp_state
  LOAD_STATIC_DATA_decomp_state
  STORE_STATIC_DATA_decomp_state
  LOAD_DYNAMIC_DATA_decomp_state
  STORE_DYNAMIC_DATA_decomp_state
  LOAD_INPUT_DATA_decomp_state
  STORE_OUTPUT_DATA_decomp_state
  COPY_decomp_state
  ADD_decomp_state
  SUBTRACT_decomp_state
  SHIFT_LEFT_decomp_state
  SHIFT_RIGHT_decomp_state
  BITWISE_AND_decomp_state
  BITWISE_OR_decomp_state
  BITWISE_XOR_decomp_state
  BITWISE_NAND_decomp_state
  BITWISE_NOT_decomp_state
  LESS_THAN_decomp_state
  GREATER_THAN_decomp_state
  EQUALS_decomp_state
  NOT_EQUALS_decomp_state
  RANDOMISE_decomp_state
  END_JUMP_decomp_state_jump
  END_JUMP_decomp_state_fall
  END_JUMP_STRICT_decomp_state
  JUMP_decomp_state
  CONDITIONAL_JUMP_decomp_state
  END_CALL_decomp_state
  CALL_decomp_state
  END_RETURN_decomp_state
  RETURN_decomp_state
  HALT_decomp_state
  ILLEGAL_decomp_state

lemmas (in Ironbark_world) instruction_decomp_mixed =
  permission_simps

  NOP_decomp_mixed
  LOAD_IMMEDIATE_decomp_mixed
  LOAD_STATIC_DATA_decomp_mixed
  STORE_STATIC_DATA_decomp_mixed
  LOAD_DYNAMIC_DATA_decomp_mixed
  STORE_DYNAMIC_DATA_decomp_mixed
  LOAD_INPUT_DATA_decomp_mixed
  STORE_OUTPUT_DATA_decomp_mixed
  COPY_decomp_mixed
  ADD_decomp_mixed
  SUBTRACT_decomp_mixed
  SHIFT_LEFT_decomp_mixed
  SHIFT_RIGHT_decomp_mixed
  BITWISE_AND_decomp_mixed
  BITWISE_OR_decomp_mixed
  BITWISE_XOR_decomp_mixed
  BITWISE_NAND_decomp_mixed
  BITWISE_NOT_decomp_mixed
  LESS_THAN_decomp_mixed
  GREATER_THAN_decomp_mixed
  EQUALS_decomp_mixed
  NOT_EQUALS_decomp_mixed
  RANDOMISE_decomp_mixed
  END_JUMP_decomp_mixed_jump
  END_JUMP_decomp_mixed_fall
  END_JUMP_STRICT_decomp_mixed
  JUMP_decomp_mixed
  CONDITIONAL_JUMP_decomp_mixed
  END_CALL_decomp_mixed
  CALL_decomp_mixed
  END_RETURN_decomp_mixed
  RETURN_decomp_mixed

lemmas (in Ironbark_world) instruction_simps = 
  initial_state_simps
  permission_simps

  NOP_simps
  LOAD_IMMEDIATE_simps
  LOAD_STATIC_DATA_simps
  STORE_STATIC_DATA_simps
  LOAD_DYNAMIC_DATA_simps
  STORE_DYNAMIC_DATA_simps
  LOAD_INPUT_DATA_simps
  STORE_OUTPUT_DATA_simps
  COPY_simps
  ADD_simps
  SUBTRACT_simps
  SHIFT_LEFT_simps
  SHIFT_RIGHT_simps
  BITWISE_AND_simps
  BITWISE_OR_simps
  BITWISE_XOR_simps
  BITWISE_NAND_simps
  BITWISE_NOT_simps
  LESS_THAN_simps
  GREATER_THAN_simps
  EQUALS_simps
  NOT_EQUALS_simps
  RANDOMISE_simps
  END_JUMP_simps
  END_JUMP_STRICT_simps
  JUMP_simps
  CONDITIONAL_JUMP_simps
  END_CALL_simps
  CALL_simps
  END_RETURN_simps
  RETURN_simps
  HALT_simps
  ILLEGAL_simps
  ERROR_simps

end