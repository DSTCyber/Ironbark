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

subsubsection \<open>Decomposition Rules for standard\_post\_instruction\<close>

theory post_instruction_decomp

imports
  state_manipulation_auxiliary

begin

text \<open>In this section we show how the standard\_post\_instruction definition can be 
decomposed either into several simpler state manipulation operations, or into 
operations on the state.\<close>

lemma post_instruction_decomp_manipulation:
  shows
    \<open>standard_post_instruction instruction_duration state = 
      write_register
        instruction_pointer_ref
        ((read_register instruction_pointer_ref state) + 0x1)
        (write_register
          last_instruction_pointer_ref
          (read_register instruction_pointer_ref state)
            (write_register
              cycles_register_ref
              ((read_register cycles_register_ref state) + instruction_duration)
              state))\<close>
  apply(simp add: standard_post_instruction_def)
  apply(simp add: Let_def)
  apply(simp add: read_register_def write_register_def)
  done

lemma post_instruction_decomp_state:
  shows
    \<open>standard_post_instruction instruction_duration state = 
      state
      \<lparr>
        register_state := 
          (register_state state)
          (
            instruction_pointer_ref 
              \<mapsto> ((read_register instruction_pointer_ref state) + 0x1),
            last_instruction_pointer_ref 
              \<mapsto> (read_register instruction_pointer_ref state),
            cycles_register_ref 
              \<mapsto> ((read_register cycles_register_ref state) + instruction_duration)
          )
      \<rparr>\<close>
  apply(simp add: post_instruction_decomp_manipulation)
  apply(simp add: read_register_def write_register_def)
  apply(simp add: state_simps)
  apply(simp add: fun_upd_twist)
  done

end