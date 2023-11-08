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

subsubsection \<open>Simplification Rules Over the Initial State\<close>

theory initial_state_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules where the state is the initial state.

We order the rules according to the operator that is applied last in the normalised 
form.

At the state layer, we bundle all the simplification rules into the one lemma, which 
shows that memory is empty, except for input memory, which is set to a function with 
no definition.\<close>

lemma (in Ironbark_world) memory_initial_state:
  \<open>program_memory initial_state = Map.empty\<close>
  \<open>call_memory    initial_state = Map.empty\<close>
  \<open>static_memory  initial_state = Map.empty\<close>
  \<open>dynamic_memory initial_state = Map.empty\<close>
  \<open>input_memory   initial_state = input_memory_stream\<close>
  \<open>output_memory  initial_state = Map.empty\<close>
  by (simp_all add: initial_state_def)

text \<open>At the state manipulation layer we show the same properties, but using the 
equivalent read functions. These functions also make it easier to express the state 
of registers and flags, so we also include those. We also found it is sometimes 
useful to include lemmas which include an arbitrary value in program memory.\<close>

lemma (in Ironbark_world) flags_initial_state:
  \<comment>\<open>flags on the initial state\<close>
  \<open>get_end_jump   initial_state = 0\<close>
  \<open>get_end_call   initial_state = 0\<close>
  \<open>get_end_return initial_state = 0\<close>
  \<open>get_halt       initial_state = 0\<close>
  \<open>get_error      initial_state = 0\<close>
  \<comment>\<open>with arbitrary program\<close>
  \<open>get_end_jump   (initial_state\<lparr>program_memory := program\<rparr>) = 0\<close>
  \<open>get_end_call   (initial_state\<lparr>program_memory := program\<rparr>) = 0\<close>
  \<open>get_end_return (initial_state\<lparr>program_memory := program\<rparr>) = 0\<close>
  \<open>get_halt       (initial_state\<lparr>program_memory := program\<rparr>) = 0\<close>
  \<open>get_error      (initial_state\<lparr>program_memory := program\<rparr>) = 0\<close>
  unfolding initial_state_def
  by(auto simp add: state_manipulation_decomp)

lemma (in Ironbark_world) typical_flags_initial_state:
  \<open>typical_flags initial_state\<close>
  \<open>typical_flags (initial_state\<lparr>program_memory := program\<rparr>)\<close>
  by (simp_all add: initial_state_def state_manipulation_decomp)

lemma (in Ironbark_world) read_register_initial_state:
  \<open>rID \<in> registers 
  \<Longrightarrow> read_register rID initial_state = 0\<close>

  \<open>rID \<in> registers 
  \<Longrightarrow> read_register rID (initial_state\<lparr>program_memory := program\<rparr>) = 0\<close>
  unfolding registers_def
  unfolding 
    generic_registers_def 
    special_purpose_registers_def 
    special_address_registers_def
  by(auto simp add: initial_state_def read_register_def)

end