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

subsubsection \<open>Decomposition Rules Over CALL\<close>

theory CALL_decomposition

imports
  instruction_auxiliary

begin

text \<open>As with most instructions, we provide three lemmas which are different ways 
of decomposing the \<open>CALL\<close> instruction. 
The three lemmas are the `special' case where we assume the guards of the 
instruction will pass.

The first lemma shows how it decomposes to state level operations in native 
Isabelle/HOL (\<open>state\<close>). 
The second is a decomposition that is a mix of native Isabelle/HOL components, 
with each component expressed at the state manipulation level. 
The third is a decomposition purely expressed in
state manipulation operations.\<close>

lemma (in Ironbark_world) CALL_decomp_state:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>CALL immediate state = 
      state
      \<lparr>
        call_memory := 
          (call_memory state) 
          (
            (read_register call_frame_pointer_ref state) + 66 
              \<mapsto> (read_register r00_ref state),
            (read_register call_frame_pointer_ref state) + 65
              \<mapsto> (read_register r01_ref state),
            (read_register call_frame_pointer_ref state) + 64
              \<mapsto> (read_register r02_ref state),
            (read_register call_frame_pointer_ref state) + 63
              \<mapsto> (read_register r03_ref state),
            (read_register call_frame_pointer_ref state) + 62
              \<mapsto> (read_register r04_ref state),
            (read_register call_frame_pointer_ref state) + 61
              \<mapsto> (read_register r05_ref state),
            (read_register call_frame_pointer_ref state) + 60
              \<mapsto> (read_register r06_ref state),
            (read_register call_frame_pointer_ref state) + 59
              \<mapsto> (read_register r07_ref state),
            (read_register call_frame_pointer_ref state) + 58
              \<mapsto> (read_register r08_ref state),
            (read_register call_frame_pointer_ref state) + 57
              \<mapsto> (read_register r09_ref state),
            (read_register call_frame_pointer_ref state) + 56
              \<mapsto> (read_register r10_ref state),
            (read_register call_frame_pointer_ref state) + 55
              \<mapsto> (read_register r11_ref state),
            (read_register call_frame_pointer_ref state) + 54
              \<mapsto> (read_register r12_ref state),
            (read_register call_frame_pointer_ref state) + 53
              \<mapsto> (read_register r13_ref state),
            (read_register call_frame_pointer_ref state) + 52
              \<mapsto> (read_register r14_ref state),
            (read_register call_frame_pointer_ref state) + 51
              \<mapsto> (read_register r15_ref state),
            (read_register call_frame_pointer_ref state) + 50
              \<mapsto> (read_register p00_ref state),
            (read_register call_frame_pointer_ref state) + 49
              \<mapsto> (read_register p01_ref state),
            (read_register call_frame_pointer_ref state) + 48
              \<mapsto> (read_register p02_ref state),
            (read_register call_frame_pointer_ref state) + 47
              \<mapsto> (read_register p03_ref state),
            (read_register call_frame_pointer_ref state) + 46
              \<mapsto> (read_register p04_ref state),
            (read_register call_frame_pointer_ref state) + 45
              \<mapsto> (read_register p05_ref state),
            (read_register call_frame_pointer_ref state) + 44
              \<mapsto> (read_register p06_ref state),
            (read_register call_frame_pointer_ref state) + 43
              \<mapsto> (read_register p07_ref state),
            (read_register call_frame_pointer_ref state) + 42
              \<mapsto> (read_register p08_ref state),
            (read_register call_frame_pointer_ref state) + 41
              \<mapsto> (read_register p09_ref state),
            (read_register call_frame_pointer_ref state) + 40
              \<mapsto> (read_register p10_ref state),
            (read_register call_frame_pointer_ref state) + 39
              \<mapsto> (read_register p11_ref state),
            (read_register call_frame_pointer_ref state) + 38
              \<mapsto> (read_register p12_ref state),
            (read_register call_frame_pointer_ref state) + 37
              \<mapsto> (read_register p13_ref state),
            (read_register call_frame_pointer_ref state) + 36
              \<mapsto> (read_register p14_ref state),
            (read_register call_frame_pointer_ref state) + 35
              \<mapsto> (read_register p15_ref state),
            (read_register call_frame_pointer_ref state) + 34
              \<mapsto> (read_register c00_ref state),
            (read_register call_frame_pointer_ref state) + 33
              \<mapsto> (read_register c01_ref state),
            (read_register call_frame_pointer_ref state) + 32
              \<mapsto> (read_register c02_ref state),
            (read_register call_frame_pointer_ref state) + 31
              \<mapsto> (read_register c03_ref state),
            (read_register call_frame_pointer_ref state) + 30
              \<mapsto> (read_register c04_ref state),
            (read_register call_frame_pointer_ref state) + 29
              \<mapsto> (read_register c05_ref state),
            (read_register call_frame_pointer_ref state) + 28
              \<mapsto> (read_register c06_ref state),
            (read_register call_frame_pointer_ref state) + 27
              \<mapsto> (read_register c07_ref state),
            (read_register call_frame_pointer_ref state) + 26
              \<mapsto> (read_register c08_ref state),
            (read_register call_frame_pointer_ref state) + 25
              \<mapsto> (read_register c09_ref state),
            (read_register call_frame_pointer_ref state) + 24
              \<mapsto> (read_register c10_ref state),
            (read_register call_frame_pointer_ref state) + 23
              \<mapsto> (read_register c11_ref state),
            (read_register call_frame_pointer_ref state) + 22
              \<mapsto> (read_register c12_ref state),
            (read_register call_frame_pointer_ref state) + 21
              \<mapsto> (read_register c13_ref state),
            (read_register call_frame_pointer_ref state) + 20
              \<mapsto> (read_register c14_ref state),
            (read_register call_frame_pointer_ref state) + 19
              \<mapsto> (read_register c15_ref state),
            (read_register call_frame_pointer_ref state) + 18
              \<mapsto> (read_register arg00_ref state),
            (read_register call_frame_pointer_ref state) + 17
              \<mapsto> (read_register arg01_ref state),
            (read_register call_frame_pointer_ref state) + 16
              \<mapsto> (read_register arg02_ref state),
            (read_register call_frame_pointer_ref state) + 15
              \<mapsto> (read_register arg03_ref state),
            (read_register call_frame_pointer_ref state) + 14
              \<mapsto> (read_register arg04_ref state),
            (read_register call_frame_pointer_ref state) + 13
              \<mapsto> (read_register arg05_ref state),
            (read_register call_frame_pointer_ref state) + 12
              \<mapsto> (read_register arg06_ref state),
            (read_register call_frame_pointer_ref state) + 11
              \<mapsto> (read_register arg07_ref state),
            (read_register call_frame_pointer_ref state) + 10
              \<mapsto> (read_register arg08_ref state),
            (read_register call_frame_pointer_ref state) +  9
              \<mapsto> (read_register arg09_ref state),
            (read_register call_frame_pointer_ref state) +  8
              \<mapsto> (read_register arg10_ref state),
            (read_register call_frame_pointer_ref state) +  7
              \<mapsto> (read_register arg11_ref state),
            (read_register call_frame_pointer_ref state) +  6
              \<mapsto> (read_register arg12_ref state),
            (read_register call_frame_pointer_ref state) +  5
              \<mapsto> (read_register arg13_ref state),
            (read_register call_frame_pointer_ref state) +  4
              \<mapsto> (read_register arg14_ref state),
            (read_register call_frame_pointer_ref state) +  3
              \<mapsto> (read_register arg15_ref state),
            (read_register call_frame_pointer_ref state) +  2
              \<mapsto> (read_register static_data_frame_pointer_ref state),
            (read_register call_frame_pointer_ref state) +  1
              \<mapsto> (read_register static_data_stack_pointer_ref state),
            (read_register call_frame_pointer_ref state) +  0
              \<mapsto> (read_register instruction_pointer_ref state)
          ),
        flag_state := (flag_state state) \<lparr>end_call := 1\<rparr>,
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> the (register_state state instruction_pointer_ref),
            instruction_pointer_ref 
              \<mapsto> immediate,
            cycles_register_ref 
              \<mapsto> the (register_state state cycles_register_ref) + call_duration,
            call_frame_pointer_ref 
              \<mapsto> the (register_state state call_frame_pointer_ref) + 67
          )
      \<rparr>\<close>
  using assms
  apply(subst sequential_state_equality)
  apply(simp_all)
  apply(simp_all add: instruction_impl_defs)
  apply(simp_all add: state_manipulation_simps)
  apply(simp_all add: state_manipulation_decomp del: backup_registers_before_call_def)
  apply(simp_all add: state_manipulation_simps)
  apply(simp_all add: fun_upd_twist)
  apply(simp_all add: state_manipulation_decomp)
  apply(simp_all add: fun_upd_twist)
  done

lemma (in Ironbark_world) CALL_decomp_mixed:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>CALL immediate state = 
      state
      \<lparr>
        call_memory := call_memory (backup_registers_before_call state),
        flag_state := flag_state (set_end_call state),
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref 
              \<mapsto> read_register instruction_pointer_ref state,
            instruction_pointer_ref 
              \<mapsto> immediate,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref state) + call_duration,
            call_frame_pointer_ref 
              \<mapsto> read_register call_frame_pointer_ref state + 67
          )
      \<rparr>\<close>
  using assms
  apply(subst sequential_state_equality)
  apply(simp_all)
  apply(simp_all add: instruction_impl_defs)
  apply(simp_all add: state_manipulation_simps)
  apply(simp_all add: state_manipulation_decomp)
  apply(simp_all add: fun_upd_twist)
  done

lemma (in Ironbark_world) CALL_decomp_manipulation:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>CALL immediate state = 
      write_register
        cycles_register_ref
        ((read_register cycles_register_ref state) + call_duration)
        (write_register 
          instruction_pointer_ref 
          immediate 
          (write_register
            last_instruction_pointer_ref
            (read_register instruction_pointer_ref state)
              (write_register
                call_frame_pointer_ref
                ((read_register call_frame_pointer_ref state) + 67)
                (backup_registers_before_call
                  (set_end_call state)))))\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_simps Let_def)
  done

end