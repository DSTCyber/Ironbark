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

subsection \<open>Properties of Register Set Definitions\<close>

text \<open>In this section we will show that the way we defined different sets of 
registers are somewhat sensible, and various properties hold that may be expected. 
These properties are heavily used in future proofs that show that it is possible to 
write both secure programs and secure functions that always behave correctly if the 
assumptions made in the definitions hold.\<close>

theory register_sets

imports
  state_auxiliary

begin

text \<open>The following lemma shows that we didn't assign a register ID to multiple 
registers in different sets, by showing that all register sets are disjoint (i.e. 
unique sets with no overlap).\<close>

lemma generic_special_disjnt:
  \<open>disjnt generic_registers         special_purpose_registers\<close>
  \<open>disjnt generic_registers         special_address_registers\<close>
  \<open>disjnt special_purpose_registers special_address_registers\<close>
  unfolding 
    generic_registers_def
    special_purpose_registers_def
    special_address_registers_def
  by (simp_all)

text \<open>This is a rewrite of the above lemma using the pairwise disjoint operator.\<close>

lemma generic_special_disjnt':
  \<open>pairwise disjnt {
    generic_registers,
    special_purpose_registers,
    special_address_registers
  }\<close>
  unfolding
    generic_registers_def
    special_purpose_registers_def
    special_address_registers_def
  by (simp add: pairwise_def)

text \<open>The following lemma shows that we didn't miss any registers in the generic 
registers, showing that the numbers from 0x00 to 0x4f (inclusive) are the same as the 
generic register set.\<close>

lemma le_ret15_ref_generic:
  \<open>r \<le> 0x4f \<longleftrightarrow> r \<in> generic_registers\<close>
proof -
  have
    \<open>r \<in> generic_registers \<Longrightarrow> r \<le> 0x4f\<close>
    unfolding generic_registers_def
    by(auto)
  moreover have
    \<open>r \<le> 0x4f \<Longrightarrow> r \<in> generic_registers\<close>
    unfolding generic_registers_def
    by(simp add: word_le_decr)
  ultimately show ?thesis
    by(auto)
qed

text \<open>The following collection of lemmas shows that all of our subsets of registers 
are part of the full set of registers. It also shows that all generic registers are 
readable and writeable.\<close>

lemma register_subsets:
  \<open>regID \<in> readable_registers         \<Longrightarrow> regID \<in> registers\<close>
  \<open>regID \<in> writeable_registers        \<Longrightarrow> regID \<in> registers\<close>
  \<open>regID \<in> special_address_registers  \<Longrightarrow> regID \<in> registers\<close>
  \<open>regID \<in> special_purpose_registers  \<Longrightarrow> regID \<in> registers\<close>
  \<open>regID \<in> generic_registers          \<Longrightarrow> regID \<in> registers\<close>
  \<open>regID \<in> generic_registers \<Longrightarrow> regID \<in> readable_registers\<close>
  \<open>regID \<in> generic_registers \<Longrightarrow> regID \<in> writeable_registers\<close>
  unfolding 
    registers_def 
    writeable_registers_def 
    readable_registers_def 
    generic_registers_def 
    special_purpose_registers_def 
    special_address_registers_def
  by(auto)

text \<open>Here we write out the full set of the readable registers, which is convenient 
for future proofs.\<close>

lemma readable_set:
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
    \<open>regID \<in> readable_registers\<close>
  using assms
  unfolding readable_registers_def
  unfolding generic_registers_def
  unfolding special_address_registers_def
  by(simp add: insert_commute)

text \<open>Occasionally, we need to show that a register is not readable. We provide the 
following lemma for this purpose.\<close>

lemma readable_exclude_set:
  assumes
    \<open>regID \<in> readable_registers\<close>
  shows
    \<open>regID \<noteq> instruction_pointer_ref\<close>
    \<open>regID \<noteq> last_instruction_pointer_ref\<close>
    \<open>regID \<noteq> call_frame_pointer_ref\<close>
  using assms
  unfolding readable_registers_def
  unfolding generic_registers_def
  unfolding special_address_registers_def
  by(auto)

text \<open>As with readable registers, we also write out the full set of writeable 
registers for the convenience of future proofs.\<close>

lemma writeable_set:
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
    \<open>regID \<in> writeable_registers\<close>
  using assms
  unfolding writeable_registers_def
  unfolding generic_registers_def
  unfolding special_address_registers_def
  by(simp add: insert_commute)

text \<open>As with readable registers, we occasionally need to show that a register is not 
writeable. We provide the following lemma for this purpose.\<close>

lemma writeable_exclude_set:
  assumes
    \<open>regID \<in> writeable_registers\<close>
  shows
    \<open>regID \<noteq> cycles_register_ref\<close>
    \<open>regID \<noteq> instruction_pointer_ref\<close>
    \<open>regID \<noteq> last_instruction_pointer_ref\<close>
    \<open>regID \<noteq> call_frame_pointer_ref\<close>
  using assms
  unfolding writeable_registers_def
  unfolding generic_registers_def
  unfolding special_address_registers_def 
  by(auto)

text \<open>Finally, we also write out the full set of all registers for the convenience of 
future proofs.\<close>

lemma register_set:
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

      cycles_register_ref,
      instruction_pointer_ref, 
      last_instruction_pointer_ref,
      call_frame_pointer_ref,

      arg_frame_pointer_ref,
      arg_stack_pointer_ref,
      dynamic_data_frame_pointer_ref,
      dynamic_data_stack_pointer_ref,
      static_data_frame_pointer_ref,
      static_data_stack_pointer_ref
    }\<close>
  shows
    \<open>regID \<in> registers\<close>
  using assms
  unfolding registers_def
  unfolding 
    generic_registers_def
    special_purpose_registers_def
    special_address_registers_def
  by(simp add: insert_commute)

end