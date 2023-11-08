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

subsubsection \<open>Decomposition Rules Over END\_JUMP\<close>

theory END_JUMP_decomposition

imports
  instruction_auxiliary

begin

text \<open>Unlike most instructions, we provide six lemmas for decomposing the 
\<open>END_JUMP\<close> instruction. 
Three lemmas are for when the end jump follows a jump, 
and the other three are for when it is not after a jump (or 
`falls through'). 
In all cases, they are the `special' case where we assume the guards of the 
instruction will pass.

As with most instructions, we have lemmas in each case for how it decomposes 
to state level operations in native Isabelle/HOL (\<open>state\<close>), 
a mix of native Isabelle/HOL components 
(with each component expressed at the state manipulation level), 
and expressed purely in state manipulation 
operations.\<close>

lemma (in Ironbark_world) END_JUMP_decomp_state_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>END_JUMP immediate state = 
      state
      \<lparr>
        flag_state := (flag_state state)\<lparr>end_jump := 0\<rparr>,
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref),
            instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref) + 1,
            cycles_register_ref 
              \<mapsto> the (register_state state cycles_register_ref) 
                + common_instruction_duration
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) END_JUMP_decomp_mixed_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>END_JUMP immediate state = 
      state
      \<lparr>
        flag_state := flag_state (clear_end_jump state),
        register_state := 
          (register_state state) (
            last_instruction_pointer_ref 
              \<mapsto> read_register instruction_pointer_ref state,
            instruction_pointer_ref 
              \<mapsto> (read_register instruction_pointer_ref state) + 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref state) 
                + common_instruction_duration
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) END_JUMP_decomp_manipulation_jump:
  assumes
    \<open>end_jump_flags state\<close>
    \<open>read_register last_instruction_pointer_ref state = immediate\<close>
  shows
    \<open>END_JUMP immediate state 
    = standard_post_instruction common_instruction_duration (clear_end_jump state)\<close>
  using assms
  by(simp add: instruction_impl_defs)

lemma (in Ironbark_world) END_JUMP_decomp_state_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>END_JUMP immediate state = 
      state
      \<lparr>
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref),
            instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref) + 1,
            cycles_register_ref 
              \<mapsto> the (register_state state cycles_register_ref) 
                + common_instruction_duration
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) END_JUMP_decomp_mixed_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>END_JUMP immediate state = 
      state
      \<lparr>
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> read_register instruction_pointer_ref state,
            instruction_pointer_ref 
              \<mapsto> (read_register instruction_pointer_ref state) + 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref state) 
                + common_instruction_duration
          )
      \<rparr>\<close>
  using assms
  apply(simp add: END_JUMP_decomp_state_fall)
  apply(simp add: state_manipulation_decomp)
  done

lemma (in Ironbark_world) END_JUMP_decomp_manipulation_fall:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>END_JUMP immediate state 
    = standard_post_instruction common_instruction_duration state\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  done

end