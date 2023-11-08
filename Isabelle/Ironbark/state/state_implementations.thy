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

subsection \<open>Defining the Ironbark Processor State\<close>

text \<open>In this section we give a formal definition of the state of the Ironbark 
processor. In making these definitions we made some assumptions which are not stated 
in the definitions themselves, but may be relevant to real-world security applications. 
The most notable assumptions made is that the hardware is functionally perfect. That 
is to say that the hardware never produces a fault under any circumstances. We also 
assume that there are no observable side effects of execution other than timing.\<close>

theory state_implementations

imports
  "Ironbark_prelim.preliminaries"

begin

text \<open>We begin our definitions with defining the state that the processor has.\<close>

text \<open>The following abbreviations are used to map a number (called a ``regID'' or 
``register identifier'') to each of the registers in the Ironbark architecture. The 
allocation can be summarised by the following (where `*' is a wildcard): \\
r*\_ref   -> 0x0* \\
p*\_ref   -> 0x1* \\
c*\_ref   -> 0x2* \\
arg*\_ref -> 0x3* \\
ret*\_ref -> 0x4* \\

Special registers are allocated/mapped from 0x50 onwards, and are grouped with 
similar kinds of registers.\<close>

 \<comment>\<open>general registers\<close>
abbreviation (input) \<open>r00_ref :: 8 word \<equiv> 0x0\<close>
abbreviation (input) \<open>r01_ref :: 8 word \<equiv> 0x1\<close>
abbreviation (input) \<open>r02_ref :: 8 word \<equiv> 0x2\<close>
abbreviation (input) \<open>r03_ref :: 8 word \<equiv> 0x3\<close>
abbreviation (input) \<open>r04_ref :: 8 word \<equiv> 0x4\<close>
abbreviation (input) \<open>r05_ref :: 8 word \<equiv> 0x5\<close>
abbreviation (input) \<open>r06_ref :: 8 word \<equiv> 0x6\<close>
abbreviation (input) \<open>r07_ref :: 8 word \<equiv> 0x7\<close>
abbreviation (input) \<open>r08_ref :: 8 word \<equiv> 0x8\<close>
abbreviation (input) \<open>r09_ref :: 8 word \<equiv> 0x9\<close>
abbreviation (input) \<open>r10_ref :: 8 word \<equiv> 0xa\<close>
abbreviation (input) \<open>r11_ref :: 8 word \<equiv> 0xb\<close>
abbreviation (input) \<open>r12_ref :: 8 word \<equiv> 0xc\<close>
abbreviation (input) \<open>r13_ref :: 8 word \<equiv> 0xd\<close>
abbreviation (input) \<open>r14_ref :: 8 word \<equiv> 0xe\<close>
abbreviation (input) \<open>r15_ref :: 8 word \<equiv> 0xf\<close>

\<comment>\<open>pointer registers\<close>
abbreviation (input) \<open>p00_ref :: 8 word \<equiv> 0x10\<close>
abbreviation (input) \<open>p01_ref :: 8 word \<equiv> 0x11\<close>
abbreviation (input) \<open>p02_ref :: 8 word \<equiv> 0x12\<close>
abbreviation (input) \<open>p03_ref :: 8 word \<equiv> 0x13\<close>
abbreviation (input) \<open>p04_ref :: 8 word \<equiv> 0x14\<close>
abbreviation (input) \<open>p05_ref :: 8 word \<equiv> 0x15\<close>
abbreviation (input) \<open>p06_ref :: 8 word \<equiv> 0x16\<close>
abbreviation (input) \<open>p07_ref :: 8 word \<equiv> 0x17\<close>
abbreviation (input) \<open>p08_ref :: 8 word \<equiv> 0x18\<close>
abbreviation (input) \<open>p09_ref :: 8 word \<equiv> 0x19\<close>
abbreviation (input) \<open>p10_ref :: 8 word \<equiv> 0x1a\<close>
abbreviation (input) \<open>p11_ref :: 8 word \<equiv> 0x1b\<close>
abbreviation (input) \<open>p12_ref :: 8 word \<equiv> 0x1c\<close>
abbreviation (input) \<open>p13_ref :: 8 word \<equiv> 0x1d\<close>
abbreviation (input) \<open>p14_ref :: 8 word \<equiv> 0x1e\<close>
abbreviation (input) \<open>p15_ref :: 8 word \<equiv> 0x1f\<close>

\<comment>\<open>constant registers\<close>
abbreviation (input) \<open>c00_ref :: 8 word \<equiv> 0x20\<close>
abbreviation (input) \<open>c01_ref :: 8 word \<equiv> 0x21\<close>
abbreviation (input) \<open>c02_ref :: 8 word \<equiv> 0x22\<close>
abbreviation (input) \<open>c03_ref :: 8 word \<equiv> 0x23\<close>
abbreviation (input) \<open>c04_ref :: 8 word \<equiv> 0x24\<close>
abbreviation (input) \<open>c05_ref :: 8 word \<equiv> 0x25\<close>
abbreviation (input) \<open>c06_ref :: 8 word \<equiv> 0x26\<close>
abbreviation (input) \<open>c07_ref :: 8 word \<equiv> 0x27\<close>
abbreviation (input) \<open>c08_ref :: 8 word \<equiv> 0x28\<close>
abbreviation (input) \<open>c09_ref :: 8 word \<equiv> 0x29\<close>
abbreviation (input) \<open>c10_ref :: 8 word \<equiv> 0x2a\<close>
abbreviation (input) \<open>c11_ref :: 8 word \<equiv> 0x2b\<close>
abbreviation (input) \<open>c12_ref :: 8 word \<equiv> 0x2c\<close>
abbreviation (input) \<open>c13_ref :: 8 word \<equiv> 0x2d\<close>
abbreviation (input) \<open>c14_ref :: 8 word \<equiv> 0x2e\<close>
abbreviation (input) \<open>c15_ref :: 8 word \<equiv> 0x2f\<close>

\<comment>\<open>argument registers\<close>
abbreviation (input) \<open>arg00_ref :: 8 word \<equiv> 0x30\<close>
abbreviation (input) \<open>arg01_ref :: 8 word \<equiv> 0x31\<close>
abbreviation (input) \<open>arg02_ref :: 8 word \<equiv> 0x32\<close>
abbreviation (input) \<open>arg03_ref :: 8 word \<equiv> 0x33\<close>
abbreviation (input) \<open>arg04_ref :: 8 word \<equiv> 0x34\<close>
abbreviation (input) \<open>arg05_ref :: 8 word \<equiv> 0x35\<close>
abbreviation (input) \<open>arg06_ref :: 8 word \<equiv> 0x36\<close>
abbreviation (input) \<open>arg07_ref :: 8 word \<equiv> 0x37\<close>
abbreviation (input) \<open>arg08_ref :: 8 word \<equiv> 0x38\<close>
abbreviation (input) \<open>arg09_ref :: 8 word \<equiv> 0x39\<close>
abbreviation (input) \<open>arg10_ref :: 8 word \<equiv> 0x3a\<close>
abbreviation (input) \<open>arg11_ref :: 8 word \<equiv> 0x3b\<close>
abbreviation (input) \<open>arg12_ref :: 8 word \<equiv> 0x3c\<close>
abbreviation (input) \<open>arg13_ref :: 8 word \<equiv> 0x3d\<close>
abbreviation (input) \<open>arg14_ref :: 8 word \<equiv> 0x3e\<close>
abbreviation (input) \<open>arg15_ref :: 8 word \<equiv> 0x3f\<close>

\<comment>\<open>return registers\<close>
abbreviation (input) \<open>ret00_ref :: 8 word \<equiv> 0x40\<close>
abbreviation (input) \<open>ret01_ref :: 8 word \<equiv> 0x41\<close>
abbreviation (input) \<open>ret02_ref :: 8 word \<equiv> 0x42\<close>
abbreviation (input) \<open>ret03_ref :: 8 word \<equiv> 0x43\<close>
abbreviation (input) \<open>ret04_ref :: 8 word \<equiv> 0x44\<close>
abbreviation (input) \<open>ret05_ref :: 8 word \<equiv> 0x45\<close>
abbreviation (input) \<open>ret06_ref :: 8 word \<equiv> 0x46\<close>
abbreviation (input) \<open>ret07_ref :: 8 word \<equiv> 0x47\<close>
abbreviation (input) \<open>ret08_ref :: 8 word \<equiv> 0x48\<close>
abbreviation (input) \<open>ret09_ref :: 8 word \<equiv> 0x49\<close>
abbreviation (input) \<open>ret10_ref :: 8 word \<equiv> 0x4a\<close>
abbreviation (input) \<open>ret11_ref :: 8 word \<equiv> 0x4b\<close>
abbreviation (input) \<open>ret12_ref :: 8 word \<equiv> 0x4c\<close>
abbreviation (input) \<open>ret13_ref :: 8 word \<equiv> 0x4d\<close>
abbreviation (input) \<open>ret14_ref :: 8 word \<equiv> 0x4e\<close>
abbreviation (input) \<open>ret15_ref :: 8 word \<equiv> 0x4f\<close>

\<comment>\<open>special address registers\<close>
abbreviation (input) \<open>arg_frame_pointer_ref           :: 8 word \<equiv> 0x50\<close>
abbreviation (input) \<open>arg_stack_pointer_ref           :: 8 word \<equiv> 0x51\<close>
abbreviation (input) \<open>dynamic_data_frame_pointer_ref  :: 8 word \<equiv> 0x52\<close>
abbreviation (input) \<open>dynamic_data_stack_pointer_ref  :: 8 word \<equiv> 0x53\<close>
abbreviation (input) \<open>static_data_frame_pointer_ref   :: 8 word \<equiv> 0x54\<close>
abbreviation (input) \<open>static_data_stack_pointer_ref   :: 8 word \<equiv> 0x55\<close>

\<comment>\<open>special purpose registers\<close>
abbreviation (input) \<open>cycles_register_ref           :: 8 word \<equiv> 0x56\<close>
abbreviation (input) \<open>last_instruction_pointer_ref  :: 8 word \<equiv> 0x57\<close>
abbreviation (input) \<open>instruction_pointer_ref       :: 8 word \<equiv> 0x58\<close>
abbreviation (input) \<open>call_frame_pointer_ref        :: 8 word \<equiv> 0x59\<close>

text \<open>We also explicitly define a few sets of registers, to make groups of registers 
easier to reference in future lemmas and definitions. These are the definitions for 
which registers are generic, special purpose, and special address. We also define the 
set of all registers (which is just the union of those sets). We also define sets for 
which registers are readable, and writeable.\<close>

text \<open>We start with the set of generic registers. They are `generic' in that a program
is able to freely read and write to them using any instruction. While they can be used
for any purpose, it is intended that pointer registers (p00 to p15) are for storing
pointers, constant registers (c00 to c15) are for holding constants, argument registers
(arg00 to arg15) are for holding arguments to function calls, and return registers
(ret00 to ret15) are for holding the return value of functions.\<close>

definition
  generic_registers :: \<open>8 word set\<close>
  where
    \<open>generic_registers \<equiv> {
      r00_ref,   r01_ref,    r02_ref,   r03_ref,
      r04_ref,   r05_ref,    r06_ref,   r07_ref,
      r08_ref,   r09_ref,    r10_ref,   r11_ref,
      r12_ref,   r13_ref,    r14_ref,   r15_ref,

      p00_ref,   p01_ref,    p02_ref,   p03_ref,
      p04_ref,   p05_ref,    p06_ref,   p07_ref,
      p08_ref,   p09_ref,    p10_ref,   p11_ref,
      p12_ref,   p13_ref,    p14_ref,   p15_ref,

      c00_ref,   c01_ref,   c02_ref,   c03_ref,
      c04_ref,   c05_ref,   c06_ref,   c07_ref,
      c08_ref,   c09_ref,   c10_ref,   c11_ref,
      c12_ref,   c13_ref,   c14_ref,   c15_ref,

      arg00_ref, arg01_ref, arg02_ref, arg03_ref,
      arg04_ref, arg05_ref, arg06_ref, arg07_ref,
      arg08_ref, arg09_ref, arg10_ref, arg11_ref,
      arg12_ref, arg13_ref, arg14_ref, arg15_ref,

      ret00_ref, ret01_ref, ret02_ref, ret03_ref,
      ret04_ref, ret05_ref, ret06_ref, ret07_ref,
      ret08_ref, ret09_ref, ret10_ref, ret11_ref,
      ret12_ref, ret13_ref, ret14_ref, ret15_ref
    }\<close>

text \<open>Next, we define the special purpose registers. They are `special purpose' in that
the processor manages them as a side effect of execution, rather than being directly
used by a program.\<close>

definition
  special_purpose_registers :: \<open>8 word set\<close>
  where
    \<open>special_purpose_registers \<equiv> {
      cycles_register_ref,
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      call_frame_pointer_ref
    }\<close>

text \<open>Next, we define the special address registers. They are `special addresses' in
that they point to the boundaries of important pieces of memory, which a program may
want to carefully maintain.\<close>

definition
  special_address_registers :: \<open>8 word set\<close>
  where
    \<open>special_address_registers \<equiv> {
      arg_frame_pointer_ref,
      arg_stack_pointer_ref,
      dynamic_data_frame_pointer_ref,
      dynamic_data_stack_pointer_ref,
      static_data_frame_pointer_ref,
      static_data_stack_pointer_ref
    }\<close>

text \<open>Next, we define the set of registers which are readable. Here, readable means
that a program is allowed to specify the register as a `source' for an instruction, and
does not refer to its physical ability to be read.\<close>

definition
  readable_registers :: \<open>8 word set\<close>
  where
    \<open>readable_registers \<equiv> 
      generic_registers 
      \<union> {cycles_register_ref} 
      \<union> special_address_registers\<close>

text \<open>Likewise, we define the set of registers which are writeable. Here, writeable 
means that a program is allowed to specify the register as a `destination' for an 
instruction, and does not refer to its physical ability to be written to.\<close>

definition
  writeable_registers :: \<open>8 word set\<close>
  where
    \<open>writeable_registers \<equiv> generic_registers \<union> special_address_registers\<close>

text \<open>Last, we define the set of all registers.\<close>

definition
  registers :: \<open>8 word set\<close>
  where
    \<open>registers \<equiv> 
      generic_registers 
      \<union> special_purpose_registers 
      \<union> special_address_registers\<close>

text \<open>The following is a record of all the flags in the Ironbark architecture. While 
a flag could be thought of conceptually as a one-bit register, we consider them 
categorically distinct for the purposes of this model and treat them accordingly. 
This distinction becomes more apparent in future definitions.\<close>

record flag_record =
  end_return    :: \<open>1 word\<close>
  end_call      :: \<open>1 word\<close>
  end_jump      :: \<open>1 word\<close>
  halt          :: \<open>1 word\<close>
  error         :: \<open>1 word\<close>

text \<open>The following defines what the complete state of the processor is. The state is
made up of the flags (`flag\_state'), the registers (`register\_state'), and 6 memory 
components (program, call, static, dynamic, input, and output memory).\<close>

text \<open>Each register is indexed by its register ID (as defined using the abbreviations 
above), and stores a 64-bit value. Whilst the map type used here allows for registers 
which we have not defined to exist, such registers would not exist on a physical 
board. Additionally, controls in how the state changes are used to prevent reading and 
writing to non-existent registers.\<close>

text \<open>All memory regions are indexed by 64-bit values, and each index points to a 
unique 64-bit value, except for program memory, which points to unique 96-bit values. 
Since it is almost certain that any implementation will not have
access to $64*(2^{64})*5 + 96*(2^{64})$ bits of physical memory, an implementation may 
produce an out of memory exception where the model does not, potentially creating an 
exploitable gap between this model and reality. We do not address this gap.\<close>

text \<open>We note that input memory is indexed by both a nat and a 64 bit value. This 
represents the input memory at a particular time (nat), at a  particular address (64 
word). The need to parameterise by time is done because we assume input memory is 
externally controlled.\<close>

record sequential_state =
  flag_state       ::  \<open>flag_record\<close>
  register_state   ::  \<open>(8 word,  64 word) map\<close>
  program_memory   ::  \<open>(64 word, 96 word) map\<close>
  call_memory      ::  \<open>(64 word, 64 word) map\<close>
  static_memory    ::  \<open>(64 word, 64 word) map\<close>
  dynamic_memory   ::  \<open>(64 word, 64 word) map\<close>
  input_memory     ::  \<open>nat \<Rightarrow> ((64 word, 64 word) map)\<close>
  output_memory    ::  \<open>(64 word, 64 word) map\<close>

text \<open>Next, we introduce a locale to relate the operation of our processor to the 
`real' time. This is intended to provide a mechanism to meaningfully talk about
sequencing and synchronising events that are occuring in either multiple instances of
an Ironbark processor, or an Ironbark processor and some external process. For this,
we introduce the time parameter as the `true' time.\<close>

text \<open>Next, we introduce a locale to create two parameters with a type signature but 
no definition or value. These are used to model random numbers and the ability for 
the input memory to arbitrarily change without anything in the model doing anything 
to it. The input\_memory\_stream parameter essentially gives us a function from time 
to the input memory state at that time.\<close>

text \<open>We also create 3 parameters for the duration of various instructions which are 
used for timing analysis. The memory\_instruction\_duration parameter parameter is 
the duration, in clock cycles, to complete a memory access instruction. The 
call\_duration parameter is the duration, in clock cycles, to complete a call or 
return instruction (which includes various registers being stored to memory). The 
common\_instruction\_duration is the duration, in clock cycles, of all other 
instructions.\<close>

text \<open>In an ideal world, memory\_instruction\_duration = call\_duration = 
common\_instruction\_duration = 1. However, we have found that implementing hardware 
to do this is nontrivial, and results in a complicated hardware implementation that 
is difficult to understand. Thus, we generalise the design using the three parameters, 
which may be any fixed finite value.\<close>



locale Ironbark_world = 
  fixes time :: \<open>nat\<close>

  fixes random_stream :: \<open>nat \<Rightarrow> 64 word\<close>
  fixes input_memory_stream :: \<open>nat \<Rightarrow> (64 word, 64 word) map\<close>

  fixes memory_instruction_duration :: \<open>64 word\<close>
  fixes call_duration :: \<open>64 word\<close>
  fixes common_instruction_duration :: \<open>64 word\<close>
  
begin
end

text \<open>We note here that the exact treatment of input memory, output memory, and time 
is a matter of active debate. Future iterations may change their treatment. However, 
we also note that the current work is mostly agnostic to the details of their 
implementation and should not greatly impact anything we show here. Nonetheless, when 
building on this work, users should be mindful of the potential change.\<close>

text \<open>Finally, we define the initial state of the processor, which is with everything 
initialised to 0, and memory being `empty', except for input\_memory, which we bind to 
the input\_memory\_stream because it is not controlled by Ironbark.\<close>
definition (in Ironbark_world)
  initial_state :: \<open>sequential_state\<close>
  where
    \<open>initial_state \<equiv> 
    (\<lparr>
      flag_state = 
      (\<lparr>
        end_return  = 0x0,
        end_call    = 0x0,
        end_jump    = 0x0,
        halt        = 0x0,
        error       = 0x0
      \<rparr>),
      register_state = Map.empty
      (
        r00_ref   \<mapsto> 0x00,
        r01_ref   \<mapsto> 0x00,
        r02_ref   \<mapsto> 0x00,
        r03_ref   \<mapsto> 0x00,
        r04_ref   \<mapsto> 0x00,
        r05_ref   \<mapsto> 0x00,
        r06_ref   \<mapsto> 0x00,
        r07_ref   \<mapsto> 0x00,
        r08_ref   \<mapsto> 0x00,
        r09_ref   \<mapsto> 0x00,
        r10_ref   \<mapsto> 0x00,
        r11_ref   \<mapsto> 0x00,
        r12_ref   \<mapsto> 0x00,
        r13_ref   \<mapsto> 0x00,
        r14_ref   \<mapsto> 0x00,
        r15_ref   \<mapsto> 0x00,
        p00_ref   \<mapsto> 0x00,
        p01_ref   \<mapsto> 0x00,
        p02_ref   \<mapsto> 0x00,
        p03_ref   \<mapsto> 0x00,
        p04_ref   \<mapsto> 0x00,
        p05_ref   \<mapsto> 0x00,
        p06_ref   \<mapsto> 0x00,
        p07_ref   \<mapsto> 0x00,
        p08_ref   \<mapsto> 0x00,
        p09_ref   \<mapsto> 0x00,
        p10_ref   \<mapsto> 0x00,
        p11_ref   \<mapsto> 0x00,
        p12_ref   \<mapsto> 0x00,
        p13_ref   \<mapsto> 0x00,
        p14_ref   \<mapsto> 0x00,
        p15_ref   \<mapsto> 0x00,
        c00_ref   \<mapsto> 0x00,
        c01_ref   \<mapsto> 0x00,
        c02_ref   \<mapsto> 0x00,
        c03_ref   \<mapsto> 0x00,
        c04_ref   \<mapsto> 0x00,
        c05_ref   \<mapsto> 0x00,
        c06_ref   \<mapsto> 0x00,
        c07_ref   \<mapsto> 0x00,
        c08_ref   \<mapsto> 0x00,
        c09_ref   \<mapsto> 0x00,
        c10_ref   \<mapsto> 0x00,
        c11_ref   \<mapsto> 0x00,
        c12_ref   \<mapsto> 0x00,
        c13_ref   \<mapsto> 0x00,
        c14_ref   \<mapsto> 0x00,
        c15_ref   \<mapsto> 0x00,
        arg00_ref \<mapsto> 0x00,
        arg01_ref \<mapsto> 0x00,
        arg02_ref \<mapsto> 0x00,
        arg03_ref \<mapsto> 0x00,
        arg04_ref \<mapsto> 0x00,
        arg05_ref \<mapsto> 0x00,
        arg06_ref \<mapsto> 0x00,
        arg07_ref \<mapsto> 0x00,
        arg08_ref \<mapsto> 0x00,
        arg09_ref \<mapsto> 0x00,
        arg10_ref \<mapsto> 0x00,
        arg11_ref \<mapsto> 0x00,
        arg12_ref \<mapsto> 0x00,
        arg13_ref \<mapsto> 0x00,
        arg14_ref \<mapsto> 0x00,
        arg15_ref \<mapsto> 0x00,
        ret00_ref \<mapsto> 0x00,
        ret01_ref \<mapsto> 0x00,
        ret02_ref \<mapsto> 0x00,
        ret03_ref \<mapsto> 0x00,
        ret04_ref \<mapsto> 0x00,
        ret05_ref \<mapsto> 0x00,
        ret06_ref \<mapsto> 0x00,
        ret07_ref \<mapsto> 0x00,
        ret08_ref \<mapsto> 0x00,
        ret09_ref \<mapsto> 0x00,
        ret10_ref \<mapsto> 0x00,
        ret11_ref \<mapsto> 0x00,
        ret12_ref \<mapsto> 0x00,
        ret13_ref \<mapsto> 0x00,
        ret14_ref \<mapsto> 0x00,
        ret15_ref \<mapsto> 0x00,
        \<comment>\<open>special purpose\<close>
        cycles_register_ref           \<mapsto> 0x00,
        instruction_pointer_ref       \<mapsto> 0x00,
        last_instruction_pointer_ref  \<mapsto> 0x00,
        call_frame_pointer_ref        \<mapsto> 0x00,
        \<comment>\<open>special address\<close>
        arg_frame_pointer_ref           \<mapsto> 0x00,
        arg_stack_pointer_ref           \<mapsto> 0x00,
        dynamic_data_frame_pointer_ref  \<mapsto> 0x00,
        dynamic_data_stack_pointer_ref  \<mapsto> 0x00,
        static_data_frame_pointer_ref   \<mapsto> 0x00,
        static_data_stack_pointer_ref   \<mapsto> 0x00 
      ),
      program_memory  = Map.empty,
      call_memory     = Map.empty,
      static_memory   = Map.empty,
      dynamic_memory  = Map.empty,
      input_memory    = input_memory_stream,
      output_memory   = Map.empty
    \<rparr>)\<close>

end