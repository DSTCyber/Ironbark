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

subsubsection \<open>Simplification Rules Over Memory\<close>

theory memory_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules that apply state manipulation memory 
operations to a state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.

At the state layer, we show non-interference of writing memory on flags, registers and 
any memory address space that was not written to.\<close>

lemma (in Ironbark_world) state_write_memory:
  \<comment>\<open>non-interference with flags\<close>
  \<open>flag_state (write_program_memory address value1 state) = flag_state state\<close>
  \<open>flag_state (write_call_memory    address value2 state) = flag_state state\<close>
  \<open>flag_state (write_static_memory  address value2 state) = flag_state state\<close>
  \<open>flag_state (write_dynamic_memory address value2 state) = flag_state state\<close>
  \<open>flag_state (write_output_memory  address value2 state) = flag_state state\<close>

  \<comment>\<open>non-interference with registers\<close>
  \<open>register_state (write_program_memory address value1 state) = register_state state\<close>
  \<open>register_state (write_call_memory    address value2 state) = register_state state\<close>
  \<open>register_state (write_static_memory  address value2 state) = register_state state\<close>
  \<open>register_state (write_dynamic_memory address value2 state) = register_state state\<close>
  \<open>register_state (write_output_memory  address value2 state) = register_state state\<close>

  \<comment>\<open>non-interference with other memory address spaces\<close>
  \<open>program_memory (write_call_memory    address value2 state) = program_memory  state\<close>
  \<open>program_memory (write_static_memory  address value2 state) = program_memory  state\<close>
  \<open>program_memory (write_dynamic_memory address value2 state) = program_memory  state\<close>
  \<open>program_memory (write_output_memory  address value2 state) = program_memory  state\<close>

  \<open>call_memory    (write_program_memory address value1 state) = call_memory     state\<close>
  \<open>call_memory    (write_static_memory  address value2 state) = call_memory     state\<close>
  \<open>call_memory    (write_dynamic_memory address value2 state) = call_memory     state\<close>
  \<open>call_memory    (write_output_memory  address value2 state) = call_memory     state\<close>

  \<open>static_memory  (write_program_memory address value1 state) = static_memory   state\<close>
  \<open>static_memory  (write_call_memory    address value2 state) = static_memory   state\<close>
  \<open>static_memory  (write_dynamic_memory address value2 state) = static_memory   state\<close>
  \<open>static_memory  (write_output_memory  address value2 state) = static_memory   state\<close>

  \<open>dynamic_memory (write_program_memory address value1 state) = dynamic_memory  state\<close>
  \<open>dynamic_memory (write_call_memory    address value2 state) = dynamic_memory  state\<close>
  \<open>dynamic_memory (write_static_memory  address value2 state) = dynamic_memory  state\<close>
  \<open>dynamic_memory (write_output_memory  address value2 state) = dynamic_memory  state\<close>

  \<open>input_memory   (write_program_memory address value1 state) = input_memory    state\<close>
  \<open>input_memory   (write_call_memory    address value2 state) = input_memory    state\<close>
  \<open>input_memory   (write_static_memory  address value2 state) = input_memory    state\<close>
  \<open>input_memory   (write_dynamic_memory address value2 state) = input_memory    state\<close>
  \<open>input_memory   (write_output_memory  address value2 state) = input_memory    state\<close>

  \<open>output_memory  (write_program_memory address value1 state) = output_memory   state\<close>
  \<open>output_memory  (write_call_memory    address value2 state) = output_memory   state\<close>
  \<open>output_memory  (write_static_memory  address value2 state) = output_memory   state\<close>
  \<open>output_memory  (write_dynamic_memory address value2 state) = output_memory   state\<close>
  by(simp_all add: state_manipulation_decomp)

text \<open>The following lemma shows that if you write the value you read, then nothing 
changes.\<close>

lemma (in Ironbark_world) same_addr_write_read:
  \<open>(program_memory state) address \<noteq> None 
  \<Longrightarrow> write_program_memory address (read_program_memory address state) state = state\<close>

  \<open>(call_memory state) address \<noteq> None 
  \<Longrightarrow> write_call_memory address (read_call_memory address state) state = state\<close>

  \<open>(static_memory state) address \<noteq> None 
  \<Longrightarrow> write_static_memory address (read_static_memory address state) state = state\<close>

  \<open>(dynamic_memory state) address \<noteq> None 
  \<Longrightarrow> write_dynamic_memory address (read_dynamic_memory address state) state = state\<close>
  by(auto simp add: state_manipulation_decomp)

text \<open>At the state manipulation layer, we show many of the same non-interference 
properties, but using the appropriate read functions.\<close>

text \<open>The following lemma shows that individual flags are not affected by writing 
memory.\<close>

lemma (in Ironbark_world) read_flag_write_memory:
  assumes
    \<open>f \<in> {
      get_end_jump,
      get_end_call,
      get_end_return,
      get_halt,
      get_error
    }\<close>
  shows
    \<open>f (write_program_memory  address value1 state) = f state\<close>
    \<open>f (write_call_memory     address value2 state) = f state\<close>
    \<open>f (write_static_memory   address value2 state) = f state\<close>
    \<open>f (write_dynamic_memory  address value2 state) = f state\<close>
    \<open>f (write_output_memory   address value2 state) = f state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

text \<open>From this, we then show that our defined flag states will also be unaffected 
by writing memory.\<close>

lemma (in Ironbark_world) common_flags_write_memory:
  assumes
    \<open>f \<in> {
      typical_flags,
      end_call_flags,
      end_return_flags,
      end_jump_flags,
      halt_flags,
      error_flags
    }\<close>
  shows
    \<open>f (write_program_memory  address value1 state) = f state\<close>
    \<open>f (write_call_memory     address value2 state) = f state\<close>
    \<open>f (write_static_memory   address value2 state) = f state\<close>
    \<open>f (write_dynamic_memory  address value2 state) = f state\<close>
    \<open>f (write_output_memory   address value2 state) = f state\<close>
  using assms
  by(auto simp add: read_flag_write_memory)

text \<open>The following lemma shows that reading a register is unaffected by writing 
memory.\<close>

lemma (in Ironbark_world) read_register_write_memory:
  \<open>read_register  regID (write_program_memory  address value1 state) 
  = read_register regID state\<close>

  \<open>read_register  regID (write_call_memory     address value2 state) 
  = read_register regID state\<close>

  \<open>read_register  regID (write_static_memory   address value2 state) 
  = read_register regID state\<close>

  \<open>read_register  regID (write_dynamic_memory  address value2 state) 
  = read_register regID state\<close>

  \<open>read_register  regID (write_output_memory   address value2 state) 
  = read_register regID state\<close>
  by(simp_all add: state_manipulation_decomp)

text \<open>Next, we show that reading from one memory region is unaffected by writes to 
another (different) memory region.\<close>

lemma (in Ironbark_world) diff_memory_read_write:
  fixes
    value2 :: \<open>64 word\<close> 
    and value1 :: \<open>96 word\<close>
  shows
    \<open>read_program_memory  address1 (write_call_memory     address2 value2 state)
    = read_program_memory address1 state\<close>
    \<open>read_program_memory  address1 (write_static_memory   address2 value2 state)
    = read_program_memory address1 state\<close>
    \<open>read_program_memory  address1 (write_dynamic_memory  address2 value2 state)
    = read_program_memory address1 state\<close>
    \<open>read_program_memory  address1 (write_output_memory   address2 value2 state)
    = read_program_memory address1 state\<close>
  
    \<open>read_call_memory     address1 (write_program_memory  address2 value1 state)
    = read_call_memory    address1 state\<close>
    \<open>read_call_memory     address1 (write_static_memory   address2 value2 state)
    = read_call_memory    address1 state\<close>
    \<open>read_call_memory     address1 (write_dynamic_memory  address2 value2 state)
    = read_call_memory    address1 state\<close>
    \<open>read_call_memory     address1 (write_output_memory   address2 value2 state)
    = read_call_memory    address1 state\<close>
  
    \<open>read_static_memory   address1 (write_program_memory  address2 value1 state)
    = read_static_memory  address1 state\<close>
    \<open>read_static_memory   address1 (write_call_memory     address2 value2 state)
    = read_static_memory  address1 state\<close>
    \<open>read_static_memory   address1 (write_dynamic_memory  address2 value2 state)
    = read_static_memory  address1 state\<close>
    \<open>read_static_memory   address1 (write_output_memory   address2 value2 state)
    = read_static_memory  address1 state\<close>
  
    \<open>read_dynamic_memory  address1 (write_program_memory  address2 value1 state)
    = read_dynamic_memory address1 state\<close>
    \<open>read_dynamic_memory  address1 (write_call_memory     address2 value2 state)
    = read_dynamic_memory address1 state\<close>
    \<open>read_dynamic_memory  address1 (write_static_memory   address2 value2 state)
    = read_dynamic_memory address1 state\<close>
    \<open>read_dynamic_memory  address1 (write_output_memory   address2 value2 state)
    = read_dynamic_memory address1 state\<close>
  
    \<open>read_input_memory    address1 (write_program_memory  address2 value1 state)
    = read_input_memory   address1 state\<close>
    \<open>read_input_memory    address1 (write_call_memory     address2 value2 state)
    = read_input_memory   address1 state\<close>
    \<open>read_input_memory    address1 (write_static_memory   address2 value2 state)
    = read_input_memory   address1 state\<close>
    \<open>read_input_memory    address1 (write_dynamic_memory  address2 value2 state)
    = read_input_memory   address1 state\<close>
    \<open>read_input_memory    address1 (write_output_memory   address2 value2 state)
    = read_input_memory   address1 state\<close>
  by (simp_all add: state_manipulation_decomp)

text \<open>Here we show that if you read from the address that you write a value to, you 
will get the value you wrote.\<close>

lemma (in Ironbark_world) same_addr_read_write:
  fixes
    value1 :: \<open>96 word\<close> 
    and value2 :: \<open>64 word\<close>
  shows
    \<open>read_program_memory  address (write_program_memory address value1 state) = value1\<close>
    \<open>read_call_memory     address (write_call_memory    address value2 state) = value2\<close>
    \<open>read_static_memory   address (write_static_memory  address value2 state) = value2\<close>
    \<open>read_dynamic_memory  address (write_dynamic_memory address value2 state) = value2\<close>
  by (simp_all add: state_manipulation_decomp)

text \<open>We then show that reading from one address is not affected by writing to 
another (different) address.\<close>

lemma (in Ironbark_world) diff_addr_read_write:
  fixes
    value1 :: \<open>96 word\<close> 
    and value2 :: \<open>64 word\<close>
  assumes
    \<open>address1 \<noteq> address2\<close>
  shows
    \<open>read_program_memory  address1 (write_program_memory  address2 value1 state)
    = read_program_memory address1 state\<close>

    \<open>read_call_memory     address1 (write_call_memory     address2 value2 state)
    = read_call_memory    address1 state\<close>

    \<open>read_static_memory   address1 (write_static_memory   address2 value2 state)
    = read_static_memory  address1 state\<close>

    \<open>read_dynamic_memory  address1 (write_dynamic_memory  address2 value2 state)
    = read_dynamic_memory address1 state\<close>
  using assms by (simp_all add: state_manipulation_decomp)

text \<open>Finally, we show that if you overwrite something, only the last value is 
retained.\<close>

lemma (in Ironbark_world) same_addr_write_write:
  \<open>write_program_memory   address value1 (write_program_memory  address value2 state) 
  = write_program_memory  address value1 state\<close>

  \<open>write_call_memory      address value3 (write_call_memory     address value4 state) 
  = write_call_memory     address value3 state\<close>

  \<open>write_static_memory    address value3 (write_static_memory   address value4 state) 
  = write_static_memory   address value3 state\<close>

  \<open>write_dynamic_memory   address value3 (write_dynamic_memory  address value4 state) 
  = write_dynamic_memory  address value3 state\<close>

  \<open>write_output_memory    address value3 (write_output_memory   address value4 state) 
  = write_output_memory   address value3 state\<close>
  by (simp_all add: state_manipulation_decomp)

end