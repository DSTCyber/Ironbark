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

theory state_top

imports
  register_sets

begin

text \<open>Here we collect up all the results that are useful for future proofs, and place 
them under the one name for convenient reference later.\<close>

lemmas state_simps =
  register_subsets
  readable_set
  readable_exclude_set
  writeable_set
  writeable_exclude_set
  register_set

end