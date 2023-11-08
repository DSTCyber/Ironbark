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

subsubsection \<open>Simplification Rules Over standard\_error\<close>

theory standard_error_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules that apply standard\_error to a state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) memory_register_state_standard_error:
  \<open>program_memory (standard_error state) = program_memory state\<close>
  \<open>call_memory    (standard_error state) = call_memory    state\<close>
  \<open>static_memory  (standard_error state) = static_memory  state\<close>
  \<open>dynamic_memory (standard_error state) = dynamic_memory state\<close>
  \<open>input_memory   (standard_error state) = input_memory   state\<close>
  \<open>output_memory  (standard_error state) = output_memory  state\<close>
  \<open>register_state (standard_error state) = register_state state\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) read_flag_standard_error:
  \<open>get_error      (standard_error state) = 1\<close>
  \<open>get_halt       (standard_error state) = 1\<close>
  \<open>get_end_jump   (standard_error state) = get_end_jump   state\<close>
  \<open>get_end_call   (standard_error state) = get_end_call   state\<close>
  \<open>get_end_return (standard_error state) = get_end_return state\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) read_memory_register_state_standard_error:
  \<open>read_program_memory  address (standard_error state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (standard_error state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (standard_error state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (standard_error state) 
  = read_dynamic_memory address state\<close>

  \<open>read_register        regID   (standard_error state) 
  = read_register       regID   state\<close>
  by(simp_all add: state_manipulation_decomp)

end