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

subsubsection \<open>Reordering Rules for Flags\<close>

theory flag_reorder

imports
  state_manipulation_simps

begin

text \<open>This file contains reordering rules that apply set or get flag operations to a 
state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma (in Ironbark_world) flag_flag_reorder:
  shows
    \<open>set_end_call   (set_end_return   state) = set_end_return   (set_end_call   state)\<close>
    \<open>set_end_jump   (set_end_return   state) = set_end_return   (set_end_jump   state)\<close>
    \<open>set_halt       (set_end_return   state) = set_end_return   (set_halt       state)\<close>
    \<open>set_error      (set_end_return   state) = set_end_return   (set_error      state)\<close>
    \<open>clear_end_call (set_end_return   state) = set_end_return   (clear_end_call state)\<close>
    \<open>clear_end_jump (set_end_return   state) = set_end_return   (clear_end_jump state)\<close>
    \<open>clear_halt     (set_end_return   state) = set_end_return   (clear_halt     state)\<close>
    \<open>clear_error    (set_end_return   state) = set_end_return   (clear_error    state)\<close>
    \<open>set_end_call   (clear_end_return state) = clear_end_return (set_end_call   state)\<close>
    \<open>set_end_jump   (clear_end_return state) = clear_end_return (set_end_jump   state)\<close>
    \<open>set_halt       (clear_end_return state) = clear_end_return (set_halt       state)\<close>
    \<open>set_error      (clear_end_return state) = clear_end_return (set_error      state)\<close>
    \<open>clear_end_call (clear_end_return state) = clear_end_return (clear_end_call state)\<close>
    \<open>clear_end_jump (clear_end_return state) = clear_end_return (clear_end_jump state)\<close>
    \<open>clear_halt     (clear_end_return state) = clear_end_return (clear_halt     state)\<close>
    \<open>clear_error    (clear_end_return state) = clear_end_return (clear_error    state)\<close>

    \<open>set_end_jump   (set_end_call     state) = set_end_call   (set_end_jump     state)\<close>
    \<open>set_halt       (set_end_call     state) = set_end_call   (set_halt         state)\<close>
    \<open>set_error      (set_end_call     state) = set_end_call   (set_error        state)\<close>
    \<open>clear_end_jump (set_end_call     state) = set_end_call   (clear_end_jump   state)\<close>
    \<open>clear_halt     (set_end_call     state) = set_end_call   (clear_halt       state)\<close>
    \<open>clear_error    (set_end_call     state) = set_end_call   (clear_error      state)\<close>
    \<open>set_end_jump   (clear_end_call   state) = clear_end_call (set_end_jump     state)\<close>
    \<open>set_halt       (clear_end_call   state) = clear_end_call (set_halt         state)\<close>
    \<open>set_error      (clear_end_call   state) = clear_end_call (set_error        state)\<close>
    \<open>clear_end_jump (clear_end_call   state) = clear_end_call (clear_end_jump   state)\<close>
    \<open>clear_halt     (clear_end_call   state) = clear_end_call (clear_halt       state)\<close>
    \<open>clear_error    (clear_end_call   state) = clear_end_call (clear_error      state)\<close>

    \<open>set_halt       (set_end_jump     state) = set_end_jump   (set_halt         state)\<close>
    \<open>set_error      (set_end_jump     state) = set_end_jump   (set_error        state)\<close>
    \<open>clear_halt     (set_end_jump     state) = set_end_jump   (clear_halt       state)\<close>
    \<open>clear_error    (set_end_jump     state) = set_end_jump   (clear_error      state)\<close>
    \<open>set_halt       (clear_end_jump   state) = clear_end_jump (set_halt         state)\<close>
    \<open>set_error      (clear_end_jump   state) = clear_end_jump (set_error        state)\<close>
    \<open>clear_halt     (clear_end_jump   state) = clear_end_jump (clear_halt       state)\<close>
    \<open>clear_error    (clear_end_jump   state) = clear_end_jump (clear_error      state)\<close>

    \<open>set_error      (set_halt         state) = set_halt       (set_error        state)\<close>
    \<open>clear_error    (set_halt         state) = set_halt       (clear_error      state)\<close>
    \<open>set_error      (clear_halt       state) = clear_halt     (set_error        state)\<close>
    \<open>clear_error    (clear_halt       state) = clear_halt     (clear_error      state)\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) post_instruction_flag_reorder:
  \<open>standard_post_instruction instruction_duration (set_end_jump      state) 
  = set_end_jump     (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (set_end_call      state) 
  = set_end_call     (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (set_end_return    state) 
  = set_end_return   (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (set_halt          state) 
  = set_halt         (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (set_error         state) 
  = set_error        (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (clear_end_jump    state) 
  = clear_end_jump   (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (clear_end_call    state) 
  = clear_end_call   (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (clear_end_return  state) 
  = clear_end_return (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (clear_halt        state) 
  = clear_halt       (standard_post_instruction instruction_duration state)\<close>

  \<open>standard_post_instruction instruction_duration (clear_error       state) 
  = clear_error      (standard_post_instruction instruction_duration state)\<close>
  by(simp_all add: state_manipulation_decomp)

lemma (in Ironbark_world) backup_registers_flag_reorder: 
  \<open>backup_registers_before_call (set_end_jump state1) 
  = set_end_jump (backup_registers_before_call state1)\<close>

  \<open>backup_registers_before_call (set_end_call state1) 
  = set_end_call (backup_registers_before_call state1)\<close>

  \<open>backup_registers_before_call (set_end_return state1) 
  = set_end_return (backup_registers_before_call state1)\<close>

  \<open>backup_registers_before_call (set_halt state1) 
  = set_halt (backup_registers_before_call state1)\<close>

  \<open>backup_registers_before_call (set_error state1) 
  = set_error (backup_registers_before_call state1)\<close>
  by (simp_all add: state_manipulation_decomp)

end