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

subsubsection \<open>Simplification Rules Over Check Permission Operations\<close>

theory permission_sets

imports
  state_manipulation_decomposition

begin

text \<open>This file contains lemmas relating to the check\_read\_permission and 
check\_write\_permission operations and their underlying readable\_registers and 
writeable\_registers definitions.\<close>

text \<open>Specifically, we show the sets that a regID can and can't belong to based on if 
it passes the check\_write\_permission and check\_read\_permission check.\<close>

lemma check_permission_sets:
  shows
    \<open>check_write_permission regID \<Longrightarrow> regID \<in> registers\<close>
    \<open>check_write_permission regID \<Longrightarrow> regID \<in> writeable_registers\<close>
    \<open>check_write_permission regID \<Longrightarrow> regID \<notin> special_purpose_registers\<close>
    \<open>check_write_permission regID \<Longrightarrow> regID \<notin> {
      cycles_register_ref,
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      call_frame_pointer_ref
    }\<close>
    \<open>check_read_permission  regID \<Longrightarrow> regID \<in> registers\<close>
    \<open>check_read_permission  regID \<Longrightarrow> regID \<in> readable_registers\<close>
    \<open>check_read_permission  regID \<Longrightarrow> regID \<notin> {
      instruction_pointer_ref, 
      last_instruction_pointer_ref, 
      call_frame_pointer_ref
    }\<close>
proof -
  have \<open>\<forall>x . (x \<in> special_purpose_registers \<longrightarrow> x \<notin> writeable_registers)\<close>
    unfolding special_purpose_registers_def writeable_registers_def
    unfolding generic_registers_def special_address_registers_def
    by(simp)
  then show 
    \<open>check_write_permission regID \<Longrightarrow> regID \<notin> special_purpose_registers\<close>
    \<open>check_write_permission regID \<Longrightarrow> regID \<notin> {
      cycles_register_ref,
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      call_frame_pointer_ref
    }\<close>
    unfolding check_write_permission_def
    unfolding special_purpose_registers_def
    by(auto)
  have
    \<open>instruction_pointer_ref      \<notin> readable_registers\<close>
    \<open>last_instruction_pointer_ref \<notin> readable_registers\<close>
    \<open>call_frame_pointer_ref       \<notin> readable_registers\<close>
    unfolding special_purpose_registers_def readable_registers_def
    unfolding generic_registers_def special_address_registers_def
    by(simp_all)
  then show 
    \<open>check_read_permission regID \<Longrightarrow> regID \<notin> {
      instruction_pointer_ref,
      last_instruction_pointer_ref,
      call_frame_pointer_ref
    }\<close>
    unfolding check_read_permission_def
    by(auto)
  show
    \<open>check_read_permission  regID \<Longrightarrow> regID \<in> registers\<close>
    \<open>check_read_permission  regID \<Longrightarrow> regID \<in> readable_registers\<close>
    \<open>check_write_permission regID \<Longrightarrow> regID \<in> registers\<close>
    \<open>check_write_permission regID \<Longrightarrow> regID \<in> writeable_registers\<close>
    using register_subsets
    by(simp_all add: check_write_permission_def check_read_permission_def)
qed

lemma check_write_permission_exclusion:
  assumes
    \<open>check_write_permission regID\<close>
  shows
    \<open>regID \<noteq> cycles_register_ref\<close>
    \<open>regID \<noteq> instruction_pointer_ref\<close>
    \<open>regID \<noteq> last_instruction_pointer_ref\<close>
    \<open>regID \<noteq> call_frame_pointer_ref\<close>
  using assms check_permission_sets
  by(simp_all)

lemma check_read_permission_exclusion:
  assumes
    \<open>check_read_permission regID\<close>
  shows
    \<open>regID \<noteq> instruction_pointer_ref\<close>
    \<open>regID \<noteq> last_instruction_pointer_ref\<close>
    \<open>regID \<noteq> call_frame_pointer_ref\<close>
  using assms check_permission_sets
  by(simp_all)

lemma check_read_permission_set:
  assumes
    \<open>regID \<in> {
      r00_ref,   r01_ref,   r02_ref,   r03_ref,
      r04_ref,   r05_ref,   r06_ref,   r07_ref,
      r08_ref,   r09_ref,   r10_ref,   r11_ref,
      r12_ref,   r13_ref,   r14_ref,   r15_ref,

      p00_ref,   p01_ref,   p02_ref,   p03_ref,
      p04_ref,   p05_ref,   p06_ref,   p07_ref,
      p08_ref,   p09_ref,   p10_ref,   p11_ref,
      p12_ref,   p13_ref,   p14_ref,   p15_ref,

      c00_ref,   c01_ref,   c02_ref,   c03_ref,
      c04_ref,   c05_ref,   c06_ref,   c07_ref,
      c08_ref,   c09_ref,   c10_ref,   c11_ref,
      c12_ref,   c13_ref,   c14_ref,   c15_ref,

      arg00_ref, arg01_ref, arg02_ref, arg03_ref,
      arg04_ref, arg05_ref, arg06_ref, arg07_ref,
      arg08_ref, arg09_ref, arg10_ref, arg11_ref,
      arg12_ref, arg13_ref, arg14_ref, arg15_ref,

      ret00_ref, ret01_ref, ret02_ref, ret03_ref,
      ret04_ref, ret05_ref, ret06_ref, ret07_ref,
      ret08_ref, ret09_ref, ret10_ref, ret11_ref,
      ret12_ref, ret13_ref, ret14_ref, ret15_ref,

      arg_frame_pointer_ref,
      arg_stack_pointer_ref,
      dynamic_data_frame_pointer_ref,
      dynamic_data_stack_pointer_ref,
      static_data_frame_pointer_ref,
      static_data_stack_pointer_ref,

      cycles_register_ref
    }\<close>
  shows
    \<open>check_read_permission regID\<close>
  using assms 
  unfolding check_read_permission_def
  unfolding readable_registers_def
  unfolding generic_registers_def special_address_registers_def
  by(simp add: insert_commute)

lemma check_write_permission_set:
  assumes
    \<open>regID \<in> {
      r00_ref,   r01_ref,   r02_ref,   r03_ref,
      r04_ref,   r05_ref,   r06_ref,   r07_ref,
      r08_ref,   r09_ref,   r10_ref,   r11_ref,
      r12_ref,   r13_ref,   r14_ref,   r15_ref,

      p00_ref,   p01_ref,   p02_ref,   p03_ref,
      p04_ref,   p05_ref,   p06_ref,   p07_ref,
      p08_ref,   p09_ref,   p10_ref,   p11_ref,
      p12_ref,   p13_ref,   p14_ref,   p15_ref,

      c00_ref,   c01_ref,   c02_ref,   c03_ref,
      c04_ref,   c05_ref,   c06_ref,   c07_ref,
      c08_ref,   c09_ref,   c10_ref,   c11_ref,
      c12_ref,   c13_ref,   c14_ref,   c15_ref,

      arg00_ref, arg01_ref, arg02_ref, arg03_ref,
      arg04_ref, arg05_ref, arg06_ref, arg07_ref,
      arg08_ref, arg09_ref, arg10_ref, arg11_ref,
      arg12_ref, arg13_ref, arg14_ref, arg15_ref,

      ret00_ref, ret01_ref, ret02_ref, ret03_ref,
      ret04_ref, ret05_ref, ret06_ref, ret07_ref,
      ret08_ref, ret09_ref, ret10_ref, ret11_ref,
      ret12_ref, ret13_ref, ret14_ref, ret15_ref,

      arg_frame_pointer_ref,
      arg_stack_pointer_ref,
      dynamic_data_frame_pointer_ref,
      dynamic_data_stack_pointer_ref,
      static_data_frame_pointer_ref,
      static_data_stack_pointer_ref
    }\<close>
  shows
    \<open>check_write_permission regID\<close>
  using assms 
  unfolding check_write_permission_def
  unfolding writeable_registers_def
  unfolding generic_registers_def special_address_registers_def
  by(simp add: insert_commute)

end