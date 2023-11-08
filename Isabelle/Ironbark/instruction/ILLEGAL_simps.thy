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

subsubsection \<open>Simplification Rules Over ILLEGAL\<close>

theory ILLEGAL_simps

imports
  ILLEGAL_decomposition

begin

text\<open>For the \<open>ILLEGAL\<close> instruction, to avoid duplication, we just show 
equivalence to error. The simplification rules for error can then be applied.\<close>

lemma (in Ironbark_world) ILLEGAL_equiv_ERROR:
  \<open>ILLEGAL state = ERROR0 state\<close>
  by(simp_all add: instruction_impl_defs)

end