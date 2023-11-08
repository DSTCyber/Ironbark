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

subsubsection \<open>Decomposition Rules Over HALT\<close>

theory HALT_decomposition

imports
  instruction_auxiliary

begin

text \<open>We provide two lemmas which are different ways of decomposing the \<open>HALT\<close> 
instruction. The two lemmas are the `special' case where we assume the guards of the 
instruction will pass.

The first lemma shows how it decomposes to state level operations in native 
Isabelle/HOL (`state'). The second is a decomposition purely expressed in state 
manipulation operations. 

Because \<open>HALT\<close> only operates on flags, the typical mixed decomposition is not needed.\<close>

lemma (in Ironbark_world) HALT_decomp_state:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>HALT state = state \<lparr>flag_state := (flag_state state)\<lparr>halt := 1\<rparr>\<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_decomp)
  done

lemma (in Ironbark_world) HALT_decomp_manipulation:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>HALT state = set_halt state\<close>
  using assms
  by(simp add: instruction_impl_defs)

end