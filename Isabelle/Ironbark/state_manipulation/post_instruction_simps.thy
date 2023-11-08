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

subsubsection \<open>Simplification Rules Over standard\_post\_instruction\<close>

theory post_instruction_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules that apply standard\_post\_instruction 
to a state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) read_register_standard_post_instruction:
  assumes
    \<open>regID \<notin> {
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      cycles_register_ref
    }\<close>
  shows
    \<open>read_register  regID (standard_post_instruction instruction_duration state) 
    = read_register regID state\<close>
  using assms 
  by(simp add: state_manipulation_decomp)

lemma (in Ironbark_world) read_last_instruction_pointer_standard_post_instruction:
  \<open>read_register 
    last_instruction_pointer_ref 
    (standard_post_instruction instruction_duration state) 
  = read_register instruction_pointer_ref state\<close>
  by(simp add: state_manipulation_decomp)

lemma (in Ironbark_world) read_instruction_pointer_standard_post_instruction:
  \<open>read_register 
    instruction_pointer_ref 
    (standard_post_instruction instruction_duration state) 
  = read_register instruction_pointer_ref state + 1\<close>
  by(simp add: state_manipulation_decomp)

lemma (in Ironbark_world) read_cycles_register_standard_post_instruction:
  \<open>read_register 
    cycles_register_ref
    (standard_post_instruction instruction_duration state) 
  = read_register cycles_register_ref state + instruction_duration\<close>
  by(simp add: state_manipulation_decomp)

lemma (in Ironbark_world) memory_standard_post_instruction:
  \<open>program_memory   (standard_post_instruction instruction_duration state) 
  = program_memory  state\<close>

  \<open>call_memory      (standard_post_instruction instruction_duration state) 
  = call_memory     state\<close>

  \<open>static_memory    (standard_post_instruction instruction_duration state) 
  = static_memory   state\<close>

  \<open>dynamic_memory   (standard_post_instruction instruction_duration state) 
  = dynamic_memory  state\<close>

  \<open>input_memory     (standard_post_instruction instruction_duration state) 
  = input_memory    state\<close>

  \<open>output_memory    (standard_post_instruction instruction_duration state) 
  = output_memory   state\<close>

  \<open>flag_state       (standard_post_instruction instruction_duration state) 
  = flag_state      state\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) read_memory_standard_post_instruction:
  \<open>read_program_memory  address (standard_post_instruction instruction_duration state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (standard_post_instruction instruction_duration state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (standard_post_instruction instruction_duration state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (standard_post_instruction instruction_duration state) 
  = read_dynamic_memory address state\<close>

  \<open>get_end_jump     (standard_post_instruction instruction_duration state) 
  = get_end_jump    state\<close>

  \<open>get_end_call     (standard_post_instruction instruction_duration state) 
  = get_end_call    state\<close>

  \<open>get_end_return   (standard_post_instruction instruction_duration state) 
  = get_end_return  state\<close>

  \<open>get_halt         (standard_post_instruction instruction_duration state) 
  = get_halt        state\<close>

  \<open>get_error        (standard_post_instruction instruction_duration state) 
  = get_error       state\<close>
  by(simp_all add: state_manipulation_decomp memory_standard_post_instruction)

lemma (in Ironbark_world) check_status_post_instruction:
  \<open>typical_flags  (standard_post_instruction instruction_duration state) 
  = typical_flags state\<close>
  by(auto simp add: read_memory_standard_post_instruction)

lemma (in Ironbark_world) register_state_passover:
  assumes
    \<open>register_state state1 = register_state state2\<close>
  shows
    \<open>register_state   (standard_post_instruction instruction_duration state1) 
    = register_state  (standard_post_instruction instruction_duration state2)\<close>
  using assms 
  by(simp add: state_manipulation_decomp)

end