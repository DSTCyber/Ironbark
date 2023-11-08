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

subsection \<open>Defining the Ways to Manipulate the Ironbark Processor State\<close>

text \<open>In this section we provide definitions for manipulating the state of an 
Ironbark processor. These are the lowest level functions for altering the state, 
which all future layers will use.\<close>

theory state_manipulation_implementations

imports
  "Ironbark_state.state_implementations"
  HOL.Option

begin

text \<open>Reading a register takes a register identifier (``regID'') and a state to read 
from as inputs, and returns the 64-bit value in the corresponding register.\<close>

text \<open>Note that there is no check on the regID being a legitimate register, as a map 
will return `None' if it doesn't exist by default, which is the closest to the 
desired behaviour as possible. However, it doesn't actually matter as all 
instructions check that their register operands are in the register set before 
execution anyway.\<close>

text \<open>There is also no check if the register is readable here. This is necessary 
because a register is sometimes indirectly read as part of an instruction. The 
read-only/write-only restrictions are done in each instruction based on the `user' 
supplied register in an instruction.\<close>

definition 
  read_register :: \<open>8 word \<Rightarrow> sequential_state \<Rightarrow> 64 word\<close>
  where
    \<open>read_register regID state \<equiv> the (register_state state regID)\<close>

text \<open>The write register operation takes the register to write to, the 64-bit value to 
write to it, and the (entire) current state as inputs. It returns the (entire) state 
after the write is complete.\<close>

text \<open>Note that while it checks that the register being written to exists here, it is 
not necessary, for the same reason given for reading registers. Regardless, the check 
is made in order to match as close as possible to how we anticipate an implementation 
would operate. There is also no check if the register is writeable, for the same 
reasons mentioned for reading registers.\<close>

definition 
  write_register :: \<open>8 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>write_register regID value state \<equiv>
      if regID \<in> registers then
        state\<lparr>register_state := (register_state state)(regID \<mapsto> value)\<rparr>
      else
        state\<lparr>flag_state := (flag_state state) \<lparr>halt := 1, error := 1\<rparr>\<rparr>\<close>

text \<open>We now provide the mechanism to check if a register is readable and writeable, 
which is fairly self-explanatory.\<close>

definition 
  check_read_permission :: \<open>8 word \<Rightarrow> bool\<close>
  where
    \<open>check_read_permission regID \<equiv> (regID \<in> readable_registers)\<close>

definition 
  check_write_permission :: \<open>8 word \<Rightarrow> bool\<close>
  where
    \<open>check_write_permission regID \<equiv> (regID \<in> writeable_registers)\<close>

text \<open>For reading and writing flags, rather than using a general function for all 
flags, we define individual functions to get, set, or clear each flag.\<close>

\<comment>\<open>get\<close>
definition \<open>get_end_jump    state \<equiv> end_jump    (flag_state state)\<close>
definition \<open>get_end_call    state \<equiv> end_call    (flag_state state)\<close>
definition \<open>get_end_return  state \<equiv> end_return  (flag_state state)\<close>
definition \<open>get_halt        state \<equiv> halt        (flag_state state)\<close>
definition \<open>get_error       state \<equiv> error       (flag_state state)\<close>

\<comment>\<open>set\<close>
definition 
  set_end_jump :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>set_end_jump state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>end_jump := 1\<rparr>\<rparr>\<close>

definition 
  set_end_call :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>set_end_call state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>end_call := 1\<rparr>\<rparr>\<close>

definition 
  set_end_return :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>set_end_return state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>end_return := 1\<rparr>\<rparr>\<close>
definition 
  set_halt :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>set_halt state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>halt := 1\<rparr>\<rparr>\<close>

definition 
  set_error :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>set_error state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>error := 1\<rparr>\<rparr>\<close>

\<comment>\<open>clear\<close>
definition
  clear_end_jump :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>clear_end_jump state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>end_jump := 0\<rparr>\<rparr>\<close>

definition
  clear_end_call :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>clear_end_call state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>end_call := 0\<rparr>\<rparr>\<close>

definition
  clear_end_return :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>clear_end_return state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>end_return := 0\<rparr>\<rparr>\<close>

definition
  clear_halt :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>clear_halt state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>halt := 0\<rparr>\<rparr>\<close>

definition
  clear_error :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>clear_error state \<equiv> state\<lparr>flag_state := (flag_state state)\<lparr>error := 0\<rparr>\<rparr>\<close>

text \<open>When reasoning about the state, it is sometimes useful to be able to describe 
certain special states, which are given below.\<close>

definition 
  halted :: \<open>sequential_state \<Rightarrow> bool\<close>
  where
    \<open>halted state \<equiv> (get_halt state = 1)\<close>

definition 
  errored :: \<open>sequential_state \<Rightarrow> bool\<close>
  where
    \<open>errored state \<equiv> (get_error state = 1)\<close>

definition 
  returned :: \<open>sequential_state \<Rightarrow> bool\<close>
  where
    \<open>returned state \<equiv> (get_end_return state = 1)\<close>

definition 
  called :: \<open>sequential_state \<Rightarrow> bool\<close>
  where
    \<open>called state \<equiv> (get_end_call state = 1)\<close>

text \<open>For brevity, it is often convenient to use the following definitions to describe the state of 
all the flag registers. These definitions describe the most common sets of flag states 
encountered in normal execution.\<close>

abbreviation
  \<open>typical_flags state \<equiv>
    get_end_return  state = 0 
    \<and> get_end_call  state = 0 
    \<and> get_end_jump  state = 0 
    \<and> get_halt      state = 0 
    \<and> get_error     state = 0\<close>

abbreviation
  \<open>end_return_flags state \<equiv>
    get_end_return  state = 1 
    \<and> get_end_call  state = 0 
    \<and> get_end_jump  state = 0 
    \<and> get_halt      state = 0 
    \<and> get_error     state = 0\<close>

abbreviation
  \<open>end_call_flags state \<equiv>
    get_end_return  state = 0 
    \<and> get_end_call  state = 1 
    \<and> get_end_jump  state = 0 
    \<and> get_halt      state = 0 
    \<and> get_error     state = 0\<close>

abbreviation
  \<open>end_jump_flags state \<equiv>
    get_end_return  state = 0 
    \<and> get_end_call  state = 0 
    \<and> get_end_jump  state = 1 
    \<and> get_halt      state = 0 
    \<and> get_error     state = 0\<close>

abbreviation
  \<open>halt_flags state \<equiv>
    get_end_return  state = 0 
    \<and> get_end_call  state = 0 
    \<and> get_end_jump  state = 0 
    \<and> get_halt      state = 1 
    \<and> get_error     state = 0\<close>

abbreviation
  \<open>error_flags state \<equiv>
    get_end_return  state = 0 
    \<and> get_end_call  state = 0 
    \<and> get_end_jump  state = 0 
    \<and> get_halt      state = 1 
    \<and> get_error     state = 1\<close>

text \<open>Next, we describe reading and writing to memory. We assume that memory is 
perfect, and that all addressable spaces exist. As noted earlier, this is almost 
certainly not the case in reality, and is a gap between our model and reality.\<close>

text \<open>Note that even though program memory region is not writeable, we still define 
the function that would write to it, because we expect that the implementation of it 
would use a media which can physically be written to. However, we will later prove 
that there is no sequence of instructions which can result in an Ironbark processor 
writing to program memory.\<close>

definition
  read_program_memory :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> 96 word\<close>
  where
    \<open>read_program_memory address state \<equiv> the (program_memory state address)\<close>

definition
  write_program_memory :: \<open>64 word \<Rightarrow> 96 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>write_program_memory address value state 
    \<equiv> state\<lparr>program_memory := (program_memory state)(address \<mapsto> value)\<rparr>\<close>

definition
  read_call_memory :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> 64 word\<close>
  where
    \<open>read_call_memory address state \<equiv> the (call_memory state address)\<close>

definition
  write_call_memory :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>write_call_memory address value state 
    \<equiv> state\<lparr>call_memory := (call_memory state)(address \<mapsto> value)\<rparr>\<close>

definition
  read_static_memory :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> 64 word\<close>
  where
    \<open>read_static_memory address state \<equiv> the (static_memory state address)\<close>

definition
  write_static_memory :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>write_static_memory address value state 
    \<equiv> state\<lparr>static_memory := (static_memory state)(address \<mapsto> value)\<rparr>\<close>

definition
  read_dynamic_memory :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> 64 word\<close>
  where
    \<open>read_dynamic_memory address state \<equiv> the (dynamic_memory state address)\<close>

definition
  write_dynamic_memory :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>write_dynamic_memory address value state 
    \<equiv> state\<lparr>dynamic_memory := (dynamic_memory state)(address \<mapsto> value)\<rparr>\<close>

text \<open>We only provide definitions for reading input memory, and writing output memory,
as we expect these to actually be physically implemented in a read-only and write-only 
manner.\<close>

definition (in Ironbark_world)
  read_input_memory :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> 64 word\<close>
  where
    \<open>read_input_memory address state \<equiv> the (input_memory state time address)\<close>

definition
  write_output_memory :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>write_output_memory address value state 
    \<equiv> state\<lparr>output_memory := (output_memory state)(address \<mapsto> value)\<rparr>\<close>

text \<open>For program memory, we also define a few helper definitions for extracting the 
different parts of an instruction.\<close>

definition
  get_opcode :: \<open>96 word \<Rightarrow> 8 word\<close>
  where
    \<open>get_opcode instr \<equiv> slice 88 instr\<close>

definition
  get_immediate :: \<open>96 word \<Rightarrow> 64 word\<close>
  where
    \<open>get_immediate instr \<equiv> ucast (take_bit 64 (slice 0 instr)::64 word)\<close>

definition
  get_reg1 :: \<open>96 word \<Rightarrow> 8 word\<close>
  where
    \<open>get_reg1 instr \<equiv> ucast (take_bit 8 (slice 80 instr)::16 word)\<close>

definition
  get_reg2 :: \<open>96 word \<Rightarrow> 8 word\<close>
  where
    \<open>get_reg2 instr \<equiv> ucast (take_bit 8 (slice 72 instr)::24 word)\<close>

definition
  get_reg3 :: \<open>96 word \<Rightarrow> 8 word\<close>
  where
    \<open>get_reg3 instr \<equiv> ucast (take_bit 8 (slice 64 instr)::32 word)\<close>

text \<open>The following two definitions are specific state manipulations that are used 
across many instructions, and so are placed here for re-usability across instructions.\<close>

text \<open>Standard error just sets the halt and error flags in the state.\<close>

definition 
  standard_error :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
  \<open>standard_error state 
  \<equiv> set_halt (set_error state)\<close>

text \<open>Standard post instruction updates the cycles register, last instruction pointer, 
and the instruction pointer. Note that branch instructions will not use the standard 
post instruction because it would overwrite the instruction pointer that they set.\<close>

definition 
  standard_post_instruction :: \<open>64 word \<Rightarrow> sequential_state \<Rightarrow> sequential_state\<close>
  where
  \<open>standard_post_instruction instruction_duration state \<equiv> 
    let
      \<comment>\<open>update cycles register\<close>
      state1 = 
        write_register
          cycles_register_ref
          ((read_register cycles_register_ref state) + instruction_duration)
          state;
      \<comment>\<open>update that this was the last instruction\<close>
      state2 = 
        write_register
          last_instruction_pointer_ref
          (read_register instruction_pointer_ref state1)
          state1
    in
      \<comment>\<open>move instruction pointer to the next instruction\<close>
      write_register
        instruction_pointer_ref
        ((read_register instruction_pointer_ref state2) + 0x1)
        state2\<close>


text \<open>These last two definitions are provided as a matter of convenience for the 
definitions of the call and return instructions, respectively. While their definitions 
are long, their operations can be described quite simply. The 
backup\_registers\_before\_call function backs up the state of various registers to 
call memory, and restore\_registers\_after\_return restores those same registers from 
call memory.\<close>

definition
  backup_registers_before_call :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>backup_registers_before_call state \<equiv>
      state
      \<lparr>
        call_memory := 
          (call_memory state) 
          (
            (read_register call_frame_pointer_ref state) + 66 
              \<mapsto> (read_register r00_ref  state),
            (read_register call_frame_pointer_ref state) + 65
              \<mapsto> (read_register r01_ref  state),
            (read_register call_frame_pointer_ref state) + 64
              \<mapsto> (read_register r02_ref  state),
            (read_register call_frame_pointer_ref state) + 63
              \<mapsto> (read_register r03_ref  state),
            (read_register call_frame_pointer_ref state) + 62
              \<mapsto> (read_register r04_ref  state),
            (read_register call_frame_pointer_ref state) + 61
              \<mapsto> (read_register r05_ref  state),
            (read_register call_frame_pointer_ref state) + 60
              \<mapsto> (read_register r06_ref  state),
            (read_register call_frame_pointer_ref state) + 59
              \<mapsto> (read_register r07_ref  state),
            (read_register call_frame_pointer_ref state) + 58
              \<mapsto> (read_register r08_ref  state),
            (read_register call_frame_pointer_ref state) + 57
              \<mapsto> (read_register r09_ref  state),
            (read_register call_frame_pointer_ref state) + 56
              \<mapsto> (read_register r10_ref  state),
            (read_register call_frame_pointer_ref state) + 55
              \<mapsto> (read_register r11_ref  state),
            (read_register call_frame_pointer_ref state) + 54
              \<mapsto> (read_register r12_ref  state),
            (read_register call_frame_pointer_ref state) + 53
              \<mapsto> (read_register r13_ref  state),
            (read_register call_frame_pointer_ref state) + 52
              \<mapsto> (read_register r14_ref  state),
            (read_register call_frame_pointer_ref state) + 51
              \<mapsto> (read_register r15_ref  state),
            (read_register call_frame_pointer_ref state) + 50
              \<mapsto> (read_register p00_ref  state),
            (read_register call_frame_pointer_ref state) + 49
              \<mapsto> (read_register p01_ref  state),
            (read_register call_frame_pointer_ref state) + 48
              \<mapsto> (read_register p02_ref  state),
            (read_register call_frame_pointer_ref state) + 47
              \<mapsto> (read_register p03_ref  state),
            (read_register call_frame_pointer_ref state) + 46
              \<mapsto> (read_register p04_ref  state),
            (read_register call_frame_pointer_ref state) + 45
              \<mapsto> (read_register p05_ref  state),
            (read_register call_frame_pointer_ref state) + 44
              \<mapsto> (read_register p06_ref  state),
            (read_register call_frame_pointer_ref state) + 43
              \<mapsto> (read_register p07_ref  state),
            (read_register call_frame_pointer_ref state) + 42
              \<mapsto> (read_register p08_ref  state),
            (read_register call_frame_pointer_ref state) + 41
              \<mapsto> (read_register p09_ref  state),
            (read_register call_frame_pointer_ref state) + 40
              \<mapsto> (read_register p10_ref  state),
            (read_register call_frame_pointer_ref state) + 39
              \<mapsto> (read_register p11_ref  state),
            (read_register call_frame_pointer_ref state) + 38
              \<mapsto> (read_register p12_ref  state),
            (read_register call_frame_pointer_ref state) + 37
              \<mapsto> (read_register p13_ref  state),
            (read_register call_frame_pointer_ref state) + 36
              \<mapsto> (read_register p14_ref  state),
            (read_register call_frame_pointer_ref state) + 35
              \<mapsto> (read_register p15_ref  state),
            (read_register call_frame_pointer_ref state) + 34
              \<mapsto> (read_register c00_ref  state),
            (read_register call_frame_pointer_ref state) + 33
              \<mapsto> (read_register c01_ref  state),
            (read_register call_frame_pointer_ref state) + 32
              \<mapsto> (read_register c02_ref  state),
            (read_register call_frame_pointer_ref state) + 31
              \<mapsto> (read_register c03_ref  state),
            (read_register call_frame_pointer_ref state) + 30
              \<mapsto> (read_register c04_ref  state),
            (read_register call_frame_pointer_ref state) + 29
              \<mapsto> (read_register c05_ref  state),
            (read_register call_frame_pointer_ref state) + 28
              \<mapsto> (read_register c06_ref  state),
            (read_register call_frame_pointer_ref state) + 27
              \<mapsto> (read_register c07_ref  state),
            (read_register call_frame_pointer_ref state) + 26
              \<mapsto> (read_register c08_ref  state),
            (read_register call_frame_pointer_ref state) + 25
              \<mapsto> (read_register c09_ref  state),
            (read_register call_frame_pointer_ref state) + 24
              \<mapsto> (read_register c10_ref  state),
            (read_register call_frame_pointer_ref state) + 23
              \<mapsto> (read_register c11_ref  state),
            (read_register call_frame_pointer_ref state) + 22
              \<mapsto> (read_register c12_ref  state),
            (read_register call_frame_pointer_ref state) + 21
              \<mapsto> (read_register c13_ref  state),
            (read_register call_frame_pointer_ref state) + 20
              \<mapsto> (read_register c14_ref  state),
            (read_register call_frame_pointer_ref state) + 19
              \<mapsto> (read_register c15_ref  state),
            (read_register call_frame_pointer_ref state) + 18
              \<mapsto> (read_register arg00_ref  state),
            (read_register call_frame_pointer_ref state) + 17
              \<mapsto> (read_register arg01_ref  state),
            (read_register call_frame_pointer_ref state) + 16
              \<mapsto> (read_register arg02_ref  state),
            (read_register call_frame_pointer_ref state) + 15
              \<mapsto> (read_register arg03_ref  state),
            (read_register call_frame_pointer_ref state) + 14
              \<mapsto> (read_register arg04_ref  state),
            (read_register call_frame_pointer_ref state) + 13
              \<mapsto> (read_register arg05_ref  state),
            (read_register call_frame_pointer_ref state) + 12
              \<mapsto> (read_register arg06_ref  state),
            (read_register call_frame_pointer_ref state) + 11
              \<mapsto> (read_register arg07_ref  state),
            (read_register call_frame_pointer_ref state) + 10
              \<mapsto> (read_register arg08_ref  state),
            (read_register call_frame_pointer_ref state) +  9
              \<mapsto> (read_register arg09_ref  state),
            (read_register call_frame_pointer_ref state) +  8
              \<mapsto> (read_register arg10_ref  state),
            (read_register call_frame_pointer_ref state) +  7
              \<mapsto> (read_register arg11_ref  state),
            (read_register call_frame_pointer_ref state) +  6
              \<mapsto> (read_register arg12_ref  state),
            (read_register call_frame_pointer_ref state) +  5
              \<mapsto> (read_register arg13_ref  state),
            (read_register call_frame_pointer_ref state) +  4
              \<mapsto> (read_register arg14_ref  state),
            (read_register call_frame_pointer_ref state) +  3
              \<mapsto> (read_register arg15_ref  state),
            (read_register call_frame_pointer_ref state) +  2 
              \<mapsto> (read_register static_data_frame_pointer_ref state),
            (read_register call_frame_pointer_ref state) +  1 
              \<mapsto> (read_register static_data_stack_pointer_ref state),
            (read_register call_frame_pointer_ref state) +  0 
              \<mapsto> (read_register instruction_pointer_ref state)
          )
      \<rparr>\<close>

definition
  restore_registers_after_return :: \<open>sequential_state \<Rightarrow> sequential_state\<close>
  where
    \<open>restore_registers_after_return state \<equiv>
      state
      \<lparr>
        register_state := 
          (register_state state) 
          (
            r00_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  1) 
                state,
            r01_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  2) 
                state,
            r02_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  3)
                state,
            r03_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  4)
                state,
            r04_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  5)
                state,
            r05_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  6)
                state,
            r06_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  7)
                state,
            r07_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  8)
                state,
            r08_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) -  9)
                state,
            r09_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 10)
                state,
            r10_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 11)
                state,
            r11_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 12)
                state,
            r12_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 13)
                state,
            r13_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 14)
                state,
            r14_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 15)
                state,
            r15_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 16)
                state,
            p00_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 17)
                state,
            p01_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 18)
                state,
            p02_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 19)
                state,
            p03_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 20)
                state,
            p04_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 21)
                state,
            p05_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 22)
                state,
            p06_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 23)
                state,
            p07_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 24)
                state,
            p08_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 25)
                state,
            p09_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 26)
                state,
            p10_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 27)
                state,
            p11_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 28)
                state,
            p12_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 29)
                state,
            p13_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 30)
                state,
            p14_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 31)
                state,
            p15_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 32)
                state,
            c00_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 33)
                state,
            c01_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 34)
                state,
            c02_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 35)
                state,
            c03_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 36)
                state,
            c04_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 37)
                state,
            c05_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 38)
                state,
            c06_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 39)
                state,
            c07_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 40)
                state,
            c08_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 41)
                state,
            c09_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 42)
                state,
            c10_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 43)
                state,
            c11_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 44)
                state,
            c12_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 45)
                state,
            c13_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 46)
                state,
            c14_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 47)
                state,
            c15_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 48)
                state,
            arg00_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 49)
                state,
            arg01_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 50)
                state,
            arg02_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 51)
                state,
            arg03_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 52)
                state,
            arg04_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 53)
                state,
            arg05_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 54)
                state,
            arg06_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 55)
                state,
            arg07_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 56)
                state,
            arg08_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 57)
                state,
            arg09_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 58)
                state,
            arg10_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 59)
                state,
            arg11_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 60)
                state,
            arg12_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 61)
                state,
            arg13_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 62)
                state,
            arg14_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 63)
                state,
            arg15_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 64)
                state,
            static_data_frame_pointer_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 65)
                state,
            static_data_stack_pointer_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 66)
                state,
            instruction_pointer_ref \<mapsto> 
              read_call_memory 
                ((read_register call_frame_pointer_ref state) - 67) 
                state
          )
      \<rparr>\<close>

end