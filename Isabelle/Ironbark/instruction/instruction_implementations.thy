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

subsection \<open>Defining the Ironbark Instructions\<close>

theory instruction_implementations

imports
  "Ironbark_state_manipulation.state_manipulation_implementations"
  "HOL-Library.Monad_Syntax"

begin

text \<open>This file describes all the instructions in the Ironbark processor.\<close>

text \<open>We begin by assigning each instruction that we will define an opcode. We also 
try to group them into groups of related functionality. Note that 0x00 and 0xFF are 
errors. This is done so that when there is no program memory attached, the processor 
will error (assuming that reading from something that isn't there gives all-0s or 
all-1s, which we expect to be the most likely behaviour of any hardware 
implementation).\<close>

\<comment>\<open>misc\<close>
abbreviation (input) \<open>ERROR0_opcode             :: 8 word \<equiv> 0x00\<close>
abbreviation (input) \<open>NOP_opcode                :: 8 word \<equiv> 0x01\<close>
\<comment>\<open>data movement\<close>
abbreviation (input) \<open>LOAD_IMMEDIATE_opcode     :: 8 word \<equiv> 0x02\<close>
abbreviation (input) \<open>LOAD_STATIC_DATA_opcode   :: 8 word \<equiv> 0x03\<close>
abbreviation (input) \<open>STORE_STATIC_DATA_opcode  :: 8 word \<equiv> 0x04\<close>
abbreviation (input) \<open>LOAD_DYNAMIC_DATA_opcode  :: 8 word \<equiv> 0x05\<close>
abbreviation (input) \<open>STORE_DYNAMIC_DATA_opcode :: 8 word \<equiv> 0x06\<close>
abbreviation (input) \<open>LOAD_INPUT_DATA_opcode    :: 8 word \<equiv> 0x07\<close>
abbreviation (input) \<open>STORE_OUTPUT_DATA_opcode  :: 8 word \<equiv> 0x08\<close>
abbreviation (input) \<open>COPY_opcode               :: 8 word \<equiv> 0x09\<close>
\<comment>\<open>arithmetic\<close>
abbreviation (input) \<open>ADD_opcode                :: 8 word \<equiv> 0x0A\<close>
abbreviation (input) \<open>SUBTRACT_opcode           :: 8 word \<equiv> 0x0B\<close>
abbreviation (input) \<open>SHIFT_LEFT_opcode         :: 8 word \<equiv> 0x0C\<close>
abbreviation (input) \<open>SHIFT_RIGHT_opcode        :: 8 word \<equiv> 0x0D\<close>
abbreviation (input) \<open>BITWISE_AND_opcode        :: 8 word \<equiv> 0x0E\<close>
abbreviation (input) \<open>BITWISE_OR_opcode         :: 8 word \<equiv> 0x0F\<close>
abbreviation (input) \<open>BITWISE_XOR_opcode        :: 8 word \<equiv> 0x10\<close>
abbreviation (input) \<open>BITWISE_NAND_opcode       :: 8 word \<equiv> 0x11\<close>
abbreviation (input) \<open>BITWISE_NOT_opcode        :: 8 word \<equiv> 0x12\<close>
abbreviation (input) \<open>LESS_THAN_opcode          :: 8 word \<equiv> 0x13\<close>
abbreviation (input) \<open>GREATER_THAN_opcode       :: 8 word \<equiv> 0x14\<close>
abbreviation (input) \<open>EQUALS_opcode             :: 8 word \<equiv> 0x15\<close>
abbreviation (input) \<open>NOT_EQUALS_opcode         :: 8 word \<equiv> 0x16\<close>
abbreviation (input) \<open>RANDOMISE_opcode          :: 8 word \<equiv> 0x17\<close>
\<comment>\<open>control flow\<close>
abbreviation (input) \<open>END_JUMP_opcode           :: 8 word \<equiv> 0x18\<close>
abbreviation (input) \<open>END_JUMP_STRICT_opcode    :: 8 word \<equiv> 0x19\<close>
abbreviation (input) \<open>JUMP_opcode               :: 8 word \<equiv> 0x1A\<close>
abbreviation (input) \<open>CONDITIONAL_JUMP_opcode   :: 8 word \<equiv> 0x1B\<close>
abbreviation (input) \<open>END_CALL_opcode           :: 8 word \<equiv> 0x1C\<close>
abbreviation (input) \<open>CALL_opcode               :: 8 word \<equiv> 0x1D\<close>
abbreviation (input) \<open>END_RETURN_opcode         :: 8 word \<equiv> 0x1E\<close>
abbreviation (input) \<open>RETURN_opcode             :: 8 word \<equiv> 0x1F\<close>
\<comment>\<open>misc\<close>
abbreviation (input) \<open>HALT_opcode               :: 8 word \<equiv> 0x20\<close>
abbreviation (input) \<open>ERROR1_opcode             :: 8 word \<equiv> 0xFF\<close>

text \<open>Finally, we define what the behaviour is for each instruction. They are defined 
below in the same order as the opcodes given above.
Most instructions are of the form: @{text [display, margin=4] \<open>
if (guards) then
  do instruction
else
  error\<close>} \<close>

definition
  ERROR0 :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>ERROR0 state \<equiv> (standard_error state)\<close>

definition (in Ironbark_world)
  NOP :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>NOP state \<equiv>
      if (typical_flags state) then
        standard_post_instruction common_instruction_duration state
      else
        standard_error state\<close>

definition (in Ironbark_world)
  LOAD_IMMEDIATE :: \<open>8 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>LOAD_IMMEDIATE reg1 immediate state \<equiv>
      if
        check_write_permission reg1 
        \<and> typical_flags state
      then
        let
          state1 = write_register reg1 immediate state 
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  LOAD_STATIC_DATA :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>LOAD_STATIC_DATA reg1 reg2 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register
              reg1
              (read_static_memory (read_register reg2 state) state)
              state
        in
          standard_post_instruction memory_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  STORE_STATIC_DATA :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>STORE_STATIC_DATA reg1 reg2 state \<equiv>
      if
        check_read_permission reg1
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_static_memory
              (read_register reg1 state)
              (read_register reg2 state)
              state
        in
          standard_post_instruction memory_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  LOAD_DYNAMIC_DATA :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>LOAD_DYNAMIC_DATA reg1 reg2 state \<equiv>
      if
        check_write_permission reg1 
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register
              reg1
              (read_dynamic_memory (read_register reg2 state) state)
              state
        in
          standard_post_instruction memory_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  STORE_DYNAMIC_DATA :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>STORE_DYNAMIC_DATA reg1 reg2 state \<equiv>
      if
        check_read_permission reg1
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_dynamic_memory
              (read_register reg1 state)
              (read_register reg2 state)
              state
        in
          standard_post_instruction memory_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  LOAD_INPUT_DATA :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>LOAD_INPUT_DATA reg1 reg2 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register
              reg1
              (read_input_memory (read_register reg2 state) state)
              state
        in
          standard_post_instruction memory_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  STORE_OUTPUT_DATA :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>STORE_OUTPUT_DATA reg1 reg2 state \<equiv>
      if
        check_read_permission reg1
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_output_memory
              (read_register reg1 state)
              (read_register reg2 state)
              state
        in
          standard_post_instruction memory_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  COPY :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>COPY reg1 reg2 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register
              reg1
              (read_register reg2 state)
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  ADD :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>ADD reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1 
        \<and> check_read_permission reg2 
        \<and> check_read_permission reg3 
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register
              reg1
              ((read_register reg2 state) + (read_register reg3 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  SUBTRACT :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>SUBTRACT reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1 
        \<and> check_read_permission reg2 
        \<and> check_read_permission reg3 
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              ((read_register reg2 state) - (read_register reg3 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  SHIFT_LEFT :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>SHIFT_LEFT reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              (push_bit (unat (read_register reg3 state)) (read_register reg2 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  SHIFT_RIGHT :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>SHIFT_RIGHT reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register
              reg1
              (drop_bit (unat (read_register reg3 state)) (read_register reg2 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  BITWISE_AND :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>BITWISE_AND reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              (and (read_register reg2 state) (read_register reg3 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  BITWISE_OR :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>BITWISE_OR reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              (or (read_register reg2 state) (read_register reg3 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  BITWISE_XOR :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>BITWISE_XOR reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              (xor (read_register reg2 state) (read_register reg3 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  BITWISE_NAND :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>BITWISE_NAND reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1 
        \<and> check_read_permission reg2 
        \<and> check_read_permission reg3 
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              (not (and (read_register reg2 state) (read_register reg3 state)))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  BITWISE_NOT :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>BITWISE_NOT reg1 reg2 state \<equiv>
      if 
        check_write_permission reg1
        \<and> check_read_permission reg2 
        \<and> typical_flags state
      then
        let 
          state1 = 
            write_register
              reg1
              (not (read_register reg2 state))
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  LESS_THAN :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>LESS_THAN reg1 reg2 reg3 state \<equiv>
      if
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        if (read_register reg2 state < read_register reg3 state) then
          let 
            state1 = write_register reg1 0x01 state
          in
            standard_post_instruction common_instruction_duration state1
        else
          let 
            state1 = write_register reg1 0x00 state
          in
            standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  GREATER_THAN :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>GREATER_THAN reg1 reg2 reg3 state \<equiv>
      if 
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        if (read_register reg2 state > read_register reg3 state) then
          let 
            state1 = write_register reg1 0x01 state 
          in
            standard_post_instruction common_instruction_duration state1
        else
          let 
            state1 = write_register reg1 0x00 state 
          in
            standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  EQUALS :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>EQUALS reg1 reg2 reg3 state \<equiv>
      if 
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        if (read_register reg2 state = read_register reg3 state) then
          let 
            state1 = write_register reg1 0x01 state 
          in
            standard_post_instruction common_instruction_duration state1
        else
          let 
            state1 = write_register reg1 0x00 state 
          in
            standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  NOT_EQUALS :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>NOT_EQUALS reg1 reg2 reg3 state \<equiv>
      if 
        check_write_permission reg1
        \<and> check_read_permission reg2
        \<and> check_read_permission reg3
        \<and> typical_flags state
      then
        if (read_register reg2 state = read_register reg3 state) then
          let 
            state1 = write_register reg1 0x00 state 
          in
            standard_post_instruction common_instruction_duration state1
        else
          let 
            state1 = write_register reg1 0x01 state 
          in
            standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  RANDOMISE :: \<open>8 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>RANDOMISE reg1 state \<equiv>
      if 
        check_write_permission reg1
        \<and> typical_flags state
      then
        let
          state1 = 
            write_register 
              reg1 
              (random_stream time) 
              state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  END_JUMP :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>END_JUMP immediate state \<equiv>
      if
        get_error         state = 0x0
        \<and> get_halt        state = 0x0
        \<and> get_end_call    state = 0x0
        \<and> get_end_return  state = 0x0
      then
        if 
          get_end_jump state = 0
          \<or> (read_register last_instruction_pointer_ref state = immediate)
        then
          let
            state1 = clear_end_jump state
          in
            standard_post_instruction common_instruction_duration state1
        else
          standard_error state
      else
        standard_error state\<close>


definition (in Ironbark_world)
  END_JUMP_STRICT :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>END_JUMP_STRICT immediate state \<equiv>
      if
        end_jump_flags state
        \<and> (read_register last_instruction_pointer_ref state = immediate)
      then
        let
          state1 = clear_end_jump state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  JUMP :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>JUMP immediate state \<equiv>
      if (typical_flags state) then
        let
          state1 = set_end_jump state;
          state2 =
            write_register
              last_instruction_pointer_ref
              (read_register instruction_pointer_ref state1)
              state1;
          state3 =
            write_register
              instruction_pointer_ref
              immediate
              state2
        in
          write_register 
            cycles_register_ref 
            ((read_register cycles_register_ref state3) + common_instruction_duration) 
            state3
      else
        standard_error state\<close>

definition (in Ironbark_world)
  CONDITIONAL_JUMP :: \<open>8 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>CONDITIONAL_JUMP reg1 immediate state \<equiv>
      if
        check_read_permission reg1
        \<and> typical_flags state
      then
        if (read_register reg1 state = 0x00) then
          standard_post_instruction common_instruction_duration state
        else
          let
            state1 = set_end_jump state;
            state2 = 
              write_register
                last_instruction_pointer_ref
                (read_register instruction_pointer_ref state1)
                state1;
            state3 = 
              write_register 
                instruction_pointer_ref 
                immediate 
                state2
          in
            write_register 
              cycles_register_ref 
              ((read_register cycles_register_ref state3) 
                + common_instruction_duration) 
              state3
      else
        standard_error state\<close>


definition (in Ironbark_world)
  END_CALL :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>END_CALL state \<equiv>
      if end_call_flags state then
        let
          state1 = clear_end_call state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  CALL :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>CALL immediate state \<equiv>
      if (typical_flags state) then
        let
          state1 = set_end_call state;
          state2 = backup_registers_before_call state1;
          state3 = 
            write_register
              call_frame_pointer_ref
              ((read_register call_frame_pointer_ref state2) + 67)
              state2;
          state4 = 
            write_register
              last_instruction_pointer_ref
              (read_register instruction_pointer_ref state3)
              state3;
          state5 = 
            write_register 
              instruction_pointer_ref 
              immediate 
              state4
        in
          write_register
            cycles_register_ref
            ((read_register cycles_register_ref state5) + call_duration)
            state5
      else
        standard_error state\<close>

definition (in Ironbark_world)
  END_RETURN :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>END_RETURN immediate state \<equiv>
      if
        end_return_flags state 
        \<and> (read_register last_instruction_pointer_ref state = immediate)
      then
        let
          state1 = clear_end_return state
        in
          standard_post_instruction common_instruction_duration state1
      else
        standard_error state\<close>

definition (in Ironbark_world)
  RETURN :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>RETURN state \<equiv>
      if (typical_flags state) then
        let 
          state1 = set_end_return state;
          state2 = 
            write_register
              last_instruction_pointer_ref
              (read_register instruction_pointer_ref state1)
              state1;
          state3 = restore_registers_after_return state2;
          state4 = 
            write_register
              call_frame_pointer_ref
              ((read_register call_frame_pointer_ref state3) - 67)
              state3;
          state5 = 
            write_register
              instruction_pointer_ref
              ((read_register instruction_pointer_ref state4) + 1)
              state4
        in
          write_register
            cycles_register_ref
            ((read_register cycles_register_ref state5) + call_duration)
            state5
      else
        standard_error state\<close>

definition (in Ironbark_world)
  HALT :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>HALT state \<equiv>
      if (typical_flags state) then
        set_halt state
      else
        standard_error state\<close>

definition
  ERROR1 :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>ERROR1 state \<equiv> (standard_error state)\<close>

text \<open>The following definition is for an `illegal' instruction. An illegal instruction
is executed whenever the opcode is not one of the defined opcodes. The exact operation
is made apparent when viewing the definition of execute\_instruction\<close>

definition (in Ironbark_world)
  ILLEGAL :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>ILLEGAL state \<equiv> standard_error state\<close>

end