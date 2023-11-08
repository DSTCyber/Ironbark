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

subsubsection \<open>Decomposition Rules for Flags\<close>

theory flag_decomposition

imports
  state_manipulation_auxiliary

begin

text \<open>In this section we collect up the various definitions relating to reading and 
writing flags for easy reference later. These are used to decompose state manipulation 
operations into operations on the state components.\<close>

text \<open>We first collect all the definitions for reading flags.\<close>

lemmas read_flag_decomp =
  get_error_def 
  get_halt_def 
  get_end_jump_def 
  get_end_call_def 
  get_end_return_def

text \<open>We then collect all the definitions for writing (set and clear).\<close>

lemmas set_clear_flag_decomp = 
  set_end_return_def 
  set_end_call_def 
  set_end_jump_def 
  set_halt_def 
  set_error_def 
  clear_end_return_def 
  clear_end_call_def 
  clear_end_jump_def 
  clear_halt_def 
  clear_error_def

text \<open>We then bundle the reading and writing versions together for easier reference 
when needed.\<close>

lemmas flag_decomp =
  read_flag_decomp
  set_clear_flag_decomp

end