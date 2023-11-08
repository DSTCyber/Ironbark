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

subsubsection \<open>Decomposition Rules Over STORE\_OUTPUT\_DATA\<close>

theory STORE_OUTPUT_DATA_decomposition

imports
  instruction_auxiliary

begin

text \<open>As with most instructions, we provide three lemmas which are different ways of 
decomposing the \<open>STORE_OUTPUT_DATA\<close> instruction. The three lemmas are the `special' 
case where we assume the guards of the instruction will pass.

The first lemma shows how it decomposes to state level operations in native 
Isabelle/HOL (\<open>state\<close>). The second is a decomposition that is a mix of native 
Isabelle/HOL components, with each component expressed at the state manipulation level. 
The third is a decomposition purely expressed in state manipulation operations.\<close>

lemma (in Ironbark_world) STORE_OUTPUT_DATA_decomp_state:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>STORE_OUTPUT_DATA reg1 reg2 state = 
      state
      \<lparr>
        output_memory := 
          (output_memory state)
          (
            the (register_state state reg1) \<mapsto> the (register_state state reg2)
          ),
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref),
            instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref) + 1,
            cycles_register_ref 
              \<mapsto> the (register_state state cycles_register_ref) 
                + memory_instruction_duration
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) STORE_OUTPUT_DATA_decomp_mixed:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>STORE_OUTPUT_DATA reg1 reg2 state = 
      state
      \<lparr>
        output_memory := 
          (output_memory state)
          (
            read_register reg1 state \<mapsto> read_register reg2 state
          ),
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> read_register instruction_pointer_ref state,
            instruction_pointer_ref 
              \<mapsto> (read_register instruction_pointer_ref state) + 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref state) 
                + memory_instruction_duration
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) STORE_OUTPUT_DATA_decomp_manipulation:
  assumes
    \<open>typical_flags state\<close>
    \<open>check_read_permission reg1\<close>
    \<open>check_read_permission reg2\<close>
  shows
    \<open>STORE_OUTPUT_DATA reg1 reg2 state = 
      standard_post_instruction 
        memory_instruction_duration
        (write_output_memory
          (read_register reg1 state)
          (read_register reg2 state)
          state)\<close>
  using assms
  by(simp add: instruction_impl_defs)

end