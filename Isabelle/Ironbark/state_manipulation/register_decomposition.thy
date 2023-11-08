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

subsubsection \<open>Decomposition Rules for Registers\<close>

theory register_decomposition

imports
  state_manipulation_auxiliary

begin

text \<open>In this section we collect the definition for reading a register, and show how 
writing registers can be decomposed to state level operations. These are used to 
decompose state manipulation operations into operations on the state components.\<close>

text \<open>We first collect the definition for reading registers - essentially just 
renaming it to match the naming pattern of other decomposition rules.\<close>

lemmas read_register_decomp = 
  read_register_def

text \<open>We then provide two ways of decomposing writing registers. The second is 
applicable to a subset of the first, but is convenient as we often have 
check\_write\_permission in the assumptions of future proofs, so we provide it here 
for convenience.\<close>

lemma write_register_set_decomp:
  assumes
    \<open>regID \<in> registers\<close>
  shows
    \<open>write_register regID value state 
    = state\<lparr>register_state := (register_state state)(regID \<mapsto> value)\<rparr>\<close>
  using assms
  unfolding write_register_def
  by(simp add: state_simps)

lemma write_check_permission_decomp:
  assumes
    \<open>check_write_permission regID\<close>
  shows
    \<open>write_register regID value state 
    = state\<lparr>register_state := (register_state state)(regID \<mapsto> value)\<rparr>\<close>
  using assms
  unfolding write_register_def check_write_permission_def
  by(simp add: state_simps)

text \<open>We then bundle the reading and writing versions together for easier reference 
when needed.\<close>

lemmas register_decomp =
  read_register_decomp
  write_register_set_decomp
  write_check_permission_decomp

end