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

subsection \<open>Defining Sequential Execution\<close>

theory execution_implementations

imports
  "Ironbark_instruction.instruction_implementations"

begin

text \<open>Execution is done in a fetch-decode-execute loop. We start by defining each of 
the steps.\<close>

text \<open>Fetch is done by simply accessing of the program memory at the current 
instruction pointer.\<close>

definition
  fetch_instruction :: \<open>sequential_state \<Rightarrow> 96 word\<close>
  where
    \<open>fetch_instruction state \<equiv>
      read_program_memory
        (read_register instruction_pointer_ref state)
        state\<close>

text \<open>Since all instructions have the same form, decode is just the application of 
get\_opcode, get\_reg1, get\_reg2, get\_reg3, and get\_immediate functions to the 
value fetched from memory.\<close>

definition
  decode_instruction :: \<open>96 word \<Rightarrow> (8 word * 8 word * 8 word * 8 word * 64 word)\<close>
  where
    \<open>decode_instruction instruction \<equiv> 
      let 
        opcode = get_opcode instruction;
        reg1 = get_reg1 instruction;
        reg2 = get_reg2 instruction;
        reg3 = get_reg3 instruction;
        immediate = get_immediate instruction
      in 
        (opcode, reg1, reg2, reg3, immediate)\<close>

text \<open>Execution is essentially a large switch on the opcode. Since a switch is not 
available in Isabelle, we are forced to use if, else-if, else-if, else-if, ..., else. 
However, this is logically equivalent to a switch statement, and we expect an 
implementation would use a switch statement.\<close>

fun (in Ironbark_world)
  execute_instruction :: 
    \<open>(8 word * 8 word * 8 word * 8 word * 64 word) 
    \<Rightarrow> sequential_state 
    \<Rightarrow> sequential_state\<close>
  where
    \<open>execute_instruction (opcode, reg1, reg2, reg3, immediate) state = 
    (
      \<comment>\<open>error\<close>
      if (opcode = ERROR0_opcode) then
        ERROR0 state
      else if (opcode = ERROR1_opcode) then
        ERROR1 state

      \<comment>\<open>no-operation\<close>
      else if (opcode = NOP_opcode) then
        NOP state

      \<comment>\<open>load immediate\<close>
      else if (opcode = LOAD_IMMEDIATE_opcode) then
        LOAD_IMMEDIATE reg1 immediate state

      \<comment>\<open>static data load/store\<close>
      else if (opcode = LOAD_STATIC_DATA_opcode) then
        LOAD_STATIC_DATA reg1 reg2 state
      else if (opcode = STORE_STATIC_DATA_opcode) then
        STORE_STATIC_DATA reg1 reg2 state

      \<comment>\<open>dynamic data load/store\<close>
      else if (opcode = LOAD_DYNAMIC_DATA_opcode) then
        LOAD_DYNAMIC_DATA reg1 reg2 state
      else if (opcode = STORE_DYNAMIC_DATA_opcode) then
        STORE_DYNAMIC_DATA reg1 reg2 state

      \<comment>\<open>mapped memory load/store\<close>
      else if (opcode = LOAD_INPUT_DATA_opcode) then
        LOAD_INPUT_DATA reg1 reg2 state
      else if (opcode = STORE_OUTPUT_DATA_opcode) then
        STORE_OUTPUT_DATA reg1 reg2 state

      \<comment>\<open>arithmetic operations\<close>
      else if (opcode = COPY_opcode) then
        COPY reg1 reg2 state
      else if (opcode = ADD_opcode) then
        ADD reg1 reg2 reg3 state
      else if (opcode = SUBTRACT_opcode) then
        SUBTRACT reg1 reg2 reg3 state
      else if (opcode = SHIFT_LEFT_opcode) then
        SHIFT_LEFT reg1 reg2 reg3 state
      else if (opcode = SHIFT_RIGHT_opcode) then
        SHIFT_RIGHT reg1 reg2 reg3 state

      \<comment>\<open>bitwise operations\<close>
      else if (opcode = BITWISE_AND_opcode) then
        BITWISE_AND reg1 reg2 reg3 state
      else if (opcode = BITWISE_OR_opcode) then
        BITWISE_OR reg1 reg2 reg3 state
      else if (opcode = BITWISE_XOR_opcode) then
        BITWISE_XOR reg1 reg2 reg3 state
      else if (opcode = BITWISE_NAND_opcode) then
        BITWISE_NAND reg1 reg2 reg3 state
      else if (opcode = BITWISE_NOT_opcode) then
        BITWISE_NOT reg1 reg2 state

      \<comment>\<open>comparison operations\<close>
      else if (opcode = LESS_THAN_opcode) then
        LESS_THAN reg1 reg2 reg3 state
      else if (opcode = GREATER_THAN_opcode) then
        GREATER_THAN reg1 reg2 reg3 state
      else if (opcode = EQUALS_opcode) then
        EQUALS reg1 reg2 reg3 state
      else if (opcode = NOT_EQUALS_opcode) then
        NOT_EQUALS reg1 reg2 reg3 state

      \<comment>\<open>non-deterministic operations\<close>
      else if (opcode = RANDOMISE_opcode) then
        RANDOMISE reg1 state

      \<comment>\<open>control flow\<close>
      else if (opcode = END_JUMP_opcode) then
        END_JUMP immediate state
      else if (opcode = END_JUMP_STRICT_opcode) then
        END_JUMP_STRICT immediate state
      else if (opcode = JUMP_opcode) then
        JUMP immediate state
      else if (opcode = CONDITIONAL_JUMP_opcode) then
        CONDITIONAL_JUMP reg1 immediate state
      else if (opcode = END_CALL_opcode) then
        END_CALL state
      else if (opcode = CALL_opcode) then
        CALL immediate state
      else if (opcode = END_RETURN_opcode) then
        END_RETURN immediate state
      else if (opcode = RETURN_opcode) then
        RETURN state

      \<comment>\<open>termination\<close>
      else if (opcode = HALT_opcode) then
        HALT state
      else
        ILLEGAL state
    )\<close>

text \<open>Because we defined a function via the Isabelle fun command, its definition is 
automatically put in the simp set. We do not want this, so we remove it.\<close>

declare (in Ironbark_world) execute_instruction.simps [simp del]

text \<open>We now bundle the components of execution into a single function. We also at 
this point provide a guard for termination if there is either an error or halt flag 
set, to enforce termination. It is debateable whether the cycles register
should continue to increment after termination. We do not let it increment here, as 
we are not interested in reasoning about behaviour after termination, as there is 
nothing of note, and any deviation between this and an implementation where these 
change after termination is of no security impact, and is not a property we rely on 
for any proofs.\<close>

definition (in Ironbark_world)
  execute_next_instruction :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>execute_next_instruction state \<equiv>
      if 
        get_halt state = 0x1 
        \<or> get_error state = 0x1 
      then
        state
      else
        execute_instruction 
          (decode_instruction (fetch_instruction state))
          state\<close>

text \<open>The characteristic behaviour of the Ironbark processor is to continue executing 
the next instruction as long as it is supplied with power, and does not halt or error, 
which we interpret laxly as forever. Thus we expect to see the next instruction 
executed for an infinite number of instructions.\<close>

text \<open>To provide easier reasoning when executing multiple instructions, we provide a 
definition for executing a specific number of instructions.\<close>

primrec (in Ironbark_world)
  execute_multiple_instructions :: \<open>sequential_state \<Rightarrow> nat \<Rightarrow> sequential_state\<close>
  where
    execute_multiple_instructions_0: \<open>execute_multiple_instructions state 0 = state\<close>
  | execute_multiple_instructions_Suc: 
      \<open>execute_multiple_instructions state (Suc num_instructions) 
        = execute_next_instruction 
            (execute_multiple_instructions state num_instructions)\<close>

text \<open>The following to definitions require some explanation. 

The finish\_function\_trace function returns the program trace of a program until 
just before it would return from a function. This should only be used in `leaf' 
functions which do not call sub-functions. The step parameter is the maximum number 
of steps that can be taken, and is only provided so that we can show that the 
function terminates. Proofs that use this function are intended to be generalised for 
an arbitrary value of step.

Finally, we note that the details of these functions are the subject of some active 
debate, and have not been tested, are subject to change, and thus at the time of 
writing, caution against their use when building on this work.\<close>

primrec (in Ironbark_world) 
   finish_function_trace :: \<open>sequential_state list \<Rightarrow> nat \<Rightarrow> sequential_state list\<close>
   where
     \<open>finish_function_trace program_trace 0 = program_trace\<close>
   | \<open>finish_function_trace program_trace (Suc step) =
     (
       let
         current_state = last (finish_function_trace program_trace step);
         instruction = fetch_instruction current_state
       in
         if (get_opcode instruction = RETURN_opcode) then
           finish_function_trace program_trace step
         else
           (finish_function_trace program_trace step) 
             @ [execute_next_instruction current_state]
     )\<close>

end