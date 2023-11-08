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

subsubsection \<open>Decomposition Rules for Memory\<close>

theory memory_decomposition

imports
  state_manipulation_auxiliary

begin

text \<open>In this section we collect up the various definitions relating to reading and 
writing memory for easy reference later. These are used to decompose state 
manipulation operations into operations on the state.\<close>

text \<open>We first collect all the definitions for reading memory.\<close>

lemmas (in Ironbark_world) read_memory_decomp =
  read_program_memory_def
  read_call_memory_def
  read_static_memory_def
  read_dynamic_memory_def
  read_input_memory_def

text \<open>We then collect all the definitions for writing memory.\<close>

lemmas write_memory_decomp =
  write_program_memory_def 
  write_call_memory_def 
  write_static_memory_def
  write_dynamic_memory_def 
  write_output_memory_def

text \<open>We then bundle the reading and writing versions together for easier reference 
when needed.\<close>

lemmas (in Ironbark_world) memory_decomp =
  read_memory_decomp
  write_memory_decomp

end