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

subsubsection \<open>Simplification Rules Over Flags\<close>

theory flag_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules that apply get, set, or clear flag 
operations to a state.

We order the rules according to the secondary operator that is applied last in the 
normalised form.

At the state layer, we bundle all the simplification rules into the one lemma, which 
essentially shows that set/clear flag only affects the flag state (and therefore the 
register\_state, program\_memory, call\_memory, static\_memory, dynamic\_memory, 
input\_memory, and output\_memory are all unaffected, regardless of which set or 
clear operation is performed.\<close>

lemma (in Ironbark_world) register_memory_state_set_clear_flag:
  assumes
    \<open>f \<in> {set_end_jump,   set_end_call,   set_end_return,   set_halt,   set_error,
          clear_end_jump, clear_end_call, clear_end_return, clear_halt, clear_error}\<close>
  shows
    \<open>register_state (f state) = register_state  state\<close>
    \<open>program_memory (f state) = program_memory  state\<close>
    \<open>call_memory    (f state) = call_memory     state\<close>
    \<open>static_memory  (f state) = static_memory   state\<close>
    \<open>dynamic_memory (f state) = dynamic_memory  state\<close>
    \<open>input_memory   (f state) = input_memory    state\<close>
    \<open>output_memory  (f state) = output_memory   state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

text \<open>At the state manipulation layer, we show the same non-interference properties 
for the respective read functions.\<close>

lemma (in Ironbark_world) read_register_memory_set_clear_flag:
  assumes
    \<open>f \<in> {set_end_jump,   set_end_call,   set_end_return,   set_halt,   set_error,
          clear_end_jump, clear_end_call, clear_end_return, clear_halt, clear_error}\<close>
  shows
    \<open>read_register        regID (f state) = read_register       regID state\<close>
    \<open>read_program_memory  addr1 (f state) = read_program_memory addr1 state\<close>
    \<open>read_call_memory     addr2 (f state) = read_call_memory    addr2 state\<close>
    \<open>read_static_memory   addr2 (f state) = read_static_memory  addr2 state\<close>
    \<open>read_dynamic_memory  addr2 (f state) = read_dynamic_memory addr2 state\<close>
    \<open>read_input_memory    addr2 (f state) = read_input_memory   addr2 state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

text \<open>The following lemmas show that the set/clear flags only set their flag, and 
the other flags are not affected. We also include rules that show if you read the 
flag you write, you get what was written.\<close>

lemma (in Ironbark_world) get_end_jump_set_clear_other:
  assumes
    \<open>f \<in> {set_end_call,   set_end_return,   set_halt,   set_error,
          clear_end_call, clear_end_return, clear_halt, clear_error}\<close>
  shows
    \<open>get_end_jump (f state) = get_end_jump state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

lemma (in Ironbark_world) get_end_jump_set_clear_same:
  \<open>get_end_jump (set_end_jump   state) = 1\<close>
  \<open>get_end_jump (clear_end_jump state) = 0\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) get_end_call_set_clear_other:
  assumes
    \<open>f \<in> {set_end_jump,   set_end_return,   set_halt,   set_error,
          clear_end_jump, clear_end_return, clear_halt, clear_error}\<close>
  shows
    \<open>get_end_call (f state) = get_end_call state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

lemma (in Ironbark_world) get_end_call_set_clear_same:
  \<open>get_end_call (set_end_call   state) = 1\<close>
  \<open>get_end_call (clear_end_call state) = 0\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) get_end_return_set_clear_other:
  assumes
    \<open>f \<in> {set_end_jump,   set_end_call,   set_halt,   set_error,
          clear_end_jump, clear_end_call, clear_halt, clear_error}\<close>
  shows
    \<open>get_end_return (f state) = get_end_return state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

lemma (in Ironbark_world) get_end_return_set_clear_same:
  \<open>get_end_return (set_end_return   state) = 1\<close>
  \<open>get_end_return (clear_end_return state) = 0\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) get_halt_set_clear_other:
  assumes
    \<open>f \<in> {set_end_jump,   set_end_call,   set_end_return,   set_error,
          clear_end_jump, clear_end_call, clear_end_return, clear_error}\<close>
  shows
    \<open>get_halt (f state) = get_halt state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

lemma (in Ironbark_world) get_halt_set_clear_same:
  \<open>get_halt (set_halt   state) = 1\<close>
  \<open>get_halt (clear_halt state) = 0\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) get_error_set_clear_other:
  assumes
    \<open>f \<in> {set_end_jump,   set_end_call,   set_end_return,   set_halt,
          clear_end_jump, clear_end_call, clear_end_return, clear_halt}\<close>
  shows
    \<open>get_error (f state) = get_error state\<close>
  using assms
  by(auto simp add: state_manipulation_decomp)

lemma (in Ironbark_world) get_error_set_clear_same:
  \<open>get_error (set_error   state) = 1\<close>
  \<open>get_error (clear_error state) = 0\<close>
  by(simp_all add: state_manipulation_decomp)

end