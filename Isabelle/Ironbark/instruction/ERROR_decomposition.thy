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

subsubsection \<open>Decomposition Rules Over ERROR0 and ERROR1\<close>

theory ERROR_decomposition

imports
  instruction_auxiliary

begin

text \<open>We provide three lemmas which are different ways of decomposing the 
\<open>error0\<close> and \<open>error1\<close> instructions. The two instructions are bundled because they have 
identical functional operation.

The first lemma shows how it decomposes to state level operations in native 
Isabelle/HOL (\<open>state\<close>). The second and third are decompositions purely expressed in 
state manipulation operations. However, the second lemma uses the standard error 
operation, while the third just uses set flag operations. As \<open>error\<close> only operates on 
flags, the usual mixed decomposition is not relevant.\<close>

lemma (in Ironbark_world) ERROR_decomp_state:
  \<open>ERROR0 state = state \<lparr>flag_state := (flag_state state)\<lparr>error := 1, halt := 1\<rparr>\<rparr>\<close>
  \<open>ERROR1 state = state \<lparr>flag_state := (flag_state state)\<lparr>error := 1, halt := 1\<rparr>\<rparr>\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_decomp)

lemma (in Ironbark_world) ERROR_decomp_manipulation:
  \<open>ERROR0 state = standard_error state\<close>
  \<open>ERROR1 state = standard_error state\<close>
  by(simp_all add: instruction_impl_defs)

lemma (in Ironbark_world) ERROR_decomp_manipulation2:
  \<open>ERROR0 state = set_halt (set_error state)\<close>
  \<open>ERROR1 state = set_halt (set_error state)\<close>
  by(simp_all add: instruction_impl_defs state_manipulation_decomp)

end