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

subsubsection \<open>Simplification Rules Over Other State Manipulation Operations\<close>

theory special_simps

imports
  state_manipulation_decomposition

begin

text \<open>This file contains simplification rules that apply 
backup\_registers\_before\_call or restore\_registers\_after\_return to a state.

We order the rules based on the second operator, according to which would be applied 
last in the normalised form.\<close>

lemma flags_backup_registers_before_call:
  \<open>flag_state (backup_registers_before_call state) = flag_state state\<close>
  by (simp add: backup_registers_before_call_def)

lemma registers_backup_registers_before_call:
  \<open>register_state (backup_registers_before_call state) = register_state state\<close>
  by (simp add: backup_registers_before_call_def)

lemma memory_backup_registers_before_call:
  \<open>program_memory (backup_registers_before_call state) = program_memory state\<close>
  \<open>static_memory  (backup_registers_before_call state) = static_memory  state\<close>
  \<open>dynamic_memory (backup_registers_before_call state) = dynamic_memory state\<close>
  \<open>input_memory   (backup_registers_before_call state) = input_memory   state\<close>
  \<open>output_memory  (backup_registers_before_call state) = output_memory  state\<close>
  by (simp_all add: backup_registers_before_call_def)

lemma flags_restore_registers_after_return:
  \<open>flag_state (restore_registers_after_return state) = flag_state state\<close>
  by (simp add: restore_registers_after_return_def)

lemma memory_restore_registers_after_return:
  \<open>program_memory (restore_registers_after_return state) = program_memory state\<close>
  \<open>call_memory    (restore_registers_after_return state) = call_memory    state\<close>
  \<open>static_memory  (restore_registers_after_return state) = static_memory  state\<close>
  \<open>dynamic_memory (restore_registers_after_return state) = dynamic_memory state\<close>
  \<open>input_memory   (restore_registers_after_return state) = input_memory   state\<close>
  \<open>output_memory  (restore_registers_after_return state) = output_memory  state\<close>
  by (simp_all add: restore_registers_after_return_def)

lemma read_flags_backup_registers_before_call:
  \<open>get_end_jump   (backup_registers_before_call state) = get_end_jump   state\<close>
  \<open>get_end_call   (backup_registers_before_call state) = get_end_call   state\<close>
  \<open>get_end_return (backup_registers_before_call state) = get_end_return state\<close>
  \<open>get_halt       (backup_registers_before_call state) = get_halt       state\<close>
  \<open>get_error      (backup_registers_before_call state) = get_error      state\<close>
  by (simp_all add: flags_backup_registers_before_call 
      get_end_jump_def get_end_call_def get_end_return_def get_halt_def get_error_def)

lemma read_registers_backup_registers_before_call:
  \<open>read_register  regID (backup_registers_before_call state) 
  = read_register regID state\<close>
  by (simp add: registers_backup_registers_before_call read_register_def)

lemma (in Ironbark_world) read_memory_backup_registers_before_call:
  \<open>read_program_memory  address (backup_registers_before_call state)
  = read_program_memory address state\<close>

  \<open>read_static_memory   address (backup_registers_before_call state)
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (backup_registers_before_call state)
  = read_dynamic_memory address state\<close>

  \<open>read_input_memory    address (backup_registers_before_call state)
  = read_input_memory   address state\<close>
  by (simp_all add: Let_def
        backup_registers_before_call_def
        read_program_memory_def read_call_memory_def read_static_memory_def
        read_dynamic_memory_def read_input_memory_def)

lemma read_call_memory_backup_registers_before_call:
  assumes
    \<open>address < (read_register call_frame_pointer_ref state)\<close>
    \<open>(read_register call_frame_pointer_ref state) < (2^64 - 66)\<close>
  shows
    \<open>read_call_memory   address (backup_registers_before_call state) 
    = read_call_memory  address state\<close>
proof -
  have
    \<open>address \<noteq> read_register call_frame_pointer_ref state\<close>
    using assms
    by(auto)
  moreover have
    \<open>\<forall>n \<in> {0 .. 66} . address \<noteq> read_register call_frame_pointer_ref state + n\<close>
    using assms
    by(uint_arith, auto)
  ultimately show ?thesis
    unfolding backup_registers_before_call_def
    by(simp add: read_call_memory_def)
qed

lemma read_call_memory_backup_registers_before_call':
  assumes
    \<open>\<forall>n \<in> {0 .. 66} . address \<noteq> read_register call_frame_pointer_ref state + n\<close>
  shows
    \<open>read_call_memory   address (backup_registers_before_call state) 
    = read_call_memory  address state\<close>
  using assms
  by(auto simp add: backup_registers_before_call_def read_call_memory_def)

lemma read_flag_restore_registers_after_return:
  \<open>get_end_jump   (restore_registers_after_return state) = get_end_jump   state\<close>
  \<open>get_end_call   (restore_registers_after_return state) = get_end_call   state\<close>
  \<open>get_end_return (restore_registers_after_return state) = get_end_return state\<close>
  \<open>get_halt       (restore_registers_after_return state) = get_halt       state\<close>
  \<open>get_error      (restore_registers_after_return state) = get_error      state\<close>
  by (simp_all add: flags_restore_registers_after_return
      get_end_jump_def get_end_call_def get_end_return_def get_halt_def get_error_def)

lemma read_register_after_return_same:
  assumes
    \<open>regID \<notin> {
      r00_ref,   r01_ref,   r02_ref,   r03_ref,
      r04_ref,  r05_ref,    r06_ref,   r07_ref,
      r08_ref,   r09_ref,   r10_ref,   r11_ref,
      r12_ref,  r13_ref,    r14_ref,   r15_ref,
      p00_ref,   p01_ref,   p02_ref,   p03_ref,
      p04_ref,  p05_ref,    p06_ref,   p07_ref,
      p08_ref,   p09_ref,   p10_ref,   p11_ref,
      p12_ref,  p13_ref,    p14_ref,   p15_ref,
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
      static_data_frame_pointer_ref,
      static_data_stack_pointer_ref,
      instruction_pointer_ref
    }\<close>
  shows
    \<open>read_register    regID (restore_registers_after_return state) 
      = read_register regID state\<close>
  using assms
  by(simp_all add: restore_registers_after_return_def read_register_def)

lemma read_register_restore_registers_after_return_diff:
  \<open>read_register r00_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  1) state\<close>

  \<open>read_register r01_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  2) state\<close>

  \<open>read_register r02_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  3) state\<close>

  \<open>read_register r03_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  4) state\<close>

  \<open>read_register r04_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  5) state\<close>

  \<open>read_register r05_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  6) state\<close>

  \<open>read_register r06_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  7) state\<close>

  \<open>read_register r07_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  8) state\<close>

  \<open>read_register r08_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) -  9) state\<close>

  \<open>read_register r09_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 10) state\<close>

  \<open>read_register r10_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 11) state\<close>

  \<open>read_register r11_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 12) state\<close>

  \<open>read_register r12_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 13) state\<close>

  \<open>read_register r13_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 14) state\<close>

  \<open>read_register r14_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 15) state\<close>

  \<open>read_register r15_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 16) state\<close>

  \<open>read_register p00_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 17) state\<close>

  \<open>read_register p01_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 18) state\<close>

  \<open>read_register p02_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 19) state\<close>

  \<open>read_register p03_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 20) state\<close>

  \<open>read_register p04_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 21) state\<close>

  \<open>read_register p05_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 22) state\<close>

  \<open>read_register p06_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 23) state\<close>

  \<open>read_register p07_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 24) state\<close>

  \<open>read_register p08_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 25) state\<close>

  \<open>read_register p09_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 26) state\<close>

  \<open>read_register p10_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 27) state\<close>

  \<open>read_register p11_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 28) state\<close>

  \<open>read_register p12_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 29) state\<close>

  \<open>read_register p13_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 30) state\<close>

  \<open>read_register p14_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 31) state\<close>

  \<open>read_register p15_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 32) state\<close>

  \<open>read_register c00_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 33) state\<close>

  \<open>read_register c01_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 34) state\<close>

  \<open>read_register c02_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 35) state\<close>

  \<open>read_register c03_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 36) state\<close>

  \<open>read_register c04_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 37) state\<close>

  \<open>read_register c05_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 38) state\<close>

  \<open>read_register c06_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 39) state\<close>

  \<open>read_register c07_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 40) state\<close>

  \<open>read_register c08_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 41) state\<close>

  \<open>read_register c09_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 42) state\<close>

  \<open>read_register c10_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 43) state\<close>

  \<open>read_register c11_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 44) state\<close>

  \<open>read_register c12_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 45) state\<close>

  \<open>read_register c13_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 46) state\<close>

  \<open>read_register c14_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 47) state\<close>

  \<open>read_register c15_ref  (restore_registers_after_return state) 
  = read_call_memory      ((read_register call_frame_pointer_ref state) - 48) state\<close>

  \<open>read_register arg00_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 49) state\<close>

  \<open>read_register arg01_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 50) state\<close>

  \<open>read_register arg02_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 51) state\<close>

  \<open>read_register arg03_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 52) state\<close>

  \<open>read_register arg04_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 53) state\<close>

  \<open>read_register arg05_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 54) state\<close>

  \<open>read_register arg06_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 55) state\<close>

  \<open>read_register arg07_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 56) state\<close>

  \<open>read_register arg08_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 57) state\<close>

  \<open>read_register arg09_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 58) state\<close>

  \<open>read_register arg10_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 59) state\<close>

  \<open>read_register arg11_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 60) state\<close>

  \<open>read_register arg12_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 61) state\<close>

  \<open>read_register arg13_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 62) state\<close>

  \<open>read_register arg14_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 63) state\<close>

  \<open>read_register arg15_ref  (restore_registers_after_return state) 
  = read_call_memory        ((read_register call_frame_pointer_ref state) - 64) state\<close>

  \<open>read_register static_data_frame_pointer_ref (restore_registers_after_return state) 
  = read_call_memory ((read_register call_frame_pointer_ref state) - 65) state\<close>

  \<open>read_register static_data_stack_pointer_ref (restore_registers_after_return state) 
  = read_call_memory ((read_register call_frame_pointer_ref state) - 66) state\<close>

  \<open>read_register instruction_pointer_ref       (restore_registers_after_return state) 
  = read_call_memory ((read_register call_frame_pointer_ref state) - 67) state\<close>
  by(simp_all add: restore_registers_after_return_def read_register_def)

lemma (in Ironbark_world) read_memory_restore_registers_after_return:
  \<open>read_program_memory    address (restore_registers_after_return state) 
  = read_program_memory address state\<close>

  \<open>read_call_memory     address (restore_registers_after_return state) 
  = read_call_memory    address state\<close>

  \<open>read_static_memory   address (restore_registers_after_return state) 
  = read_static_memory  address state\<close>

  \<open>read_dynamic_memory  address (restore_registers_after_return state) 
  = read_dynamic_memory address state\<close>

  \<open>read_input_memory    address (restore_registers_after_return state) 
  = read_input_memory   address state\<close>
  by (simp_all add: restore_registers_after_return_def read_memory_decomp)

end