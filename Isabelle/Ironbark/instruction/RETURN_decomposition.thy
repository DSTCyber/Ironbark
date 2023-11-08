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

subsubsection \<open>Decomposition Rules Over RETURN\<close>

theory RETURN_decomposition

imports
  instruction_auxiliary

begin

text \<open>As with most instructions, we provide three lemmas which are different ways 
of decomposing the \<open>RETURN\<close> instruction. 
The three lemmas are the `special' case where we assume the guards of the 
instruction will pass.

The first lemma shows how it decomposes to state level operations in native 
Isabelle/HOL (\<open>state\<close>). 
The second is a decomposition that is a mix of native Isabelle/HOL components, 
with each component expressed at the state manipulation level. 
The third is a decomposition purely expressed in
state manipulation operations.\<close>

lemma (in Ironbark_world) RETURN_decomp_state:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>RETURN state = 
      state
      \<lparr>
        flag_state := (flag_state state)\<lparr>end_return := 1\<rparr>,
        register_state := 
          (register_state state) 
          (
            last_instruction_pointer_ref
              \<mapsto> the (register_state state instruction_pointer_ref),
    
            cycles_register_ref
              \<mapsto> the (register_state state cycles_register_ref) + call_duration,
    
            call_frame_pointer_ref
              \<mapsto> the (register_state state call_frame_pointer_ref) - 67,
    
            r00_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  1)
              ),
            r01_ref
              \<mapsto> the (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  2)
              ),
            r02_ref
              \<mapsto> the 
             (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  3)
              ),
            r03_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  4)
              ),
            r04_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  5)
              ),
            r05_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  6)
              ),
            r06_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  7)
              ),
            r07_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  8)
              ),
            r08_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) -  9)
              ),
            r09_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 10)
              ),
            r10_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 11)
              ),
            r11_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 12)
              ),
            r12_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 13)
              ),
            r13_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 14)
              ),
            r14_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 15)
              ),
            r15_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 16)
              ),
            p00_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 17)
              ),
            p01_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 18)
              ),
            p02_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 19)
              ),
            p03_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 20)
              ),
            p04_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 21)
              ),
            p05_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 22)
              ),
            p06_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 23)
              ),
            p07_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 24)
              ),
            p08_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 25)
              ),
            p09_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 26)
              ),
            p10_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 27)
              ),
            p11_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 28)
              ),
            p12_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 29)
              ),
            p13_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 30)
              ),
            p14_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 31)
              ),
            p15_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 32)
              ),
            c00_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 33)
              ),
            c01_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 34)
              ),
            c02_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 35)
              ),
            c03_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 36)
              ),
            c04_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 37)
              ),
            c05_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 38)
              ),
            c06_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 39)
              ),
            c07_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 40)
              ),
            c08_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 41)
              ),
            c09_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 42)
              ),
            c10_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 43)
              ),
            c11_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 44)
              ),
            c12_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 45)
              ),
            c13_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 46)
              ),
            c14_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 47)
              ),
            c15_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 48)
              ),
            arg00_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 49)
              ),
            arg01_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 50)
              ),
            arg02_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 51)
              ),
            arg03_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 52)
              ),
            arg04_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 53)
              ),
            arg05_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 54)
              ),
            arg06_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 55)
              ),
            arg07_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 56)
              ),
            arg08_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 57)
              ),
            arg09_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 58)
              ),
            arg10_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 59)
              ),
            arg11_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 60)
              ),
            arg12_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 61)
              ),
            arg13_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 62)
              ),
            arg14_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 63)
              ),
            arg15_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 64)
              ),
    
            static_data_frame_pointer_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 65)
              ),
    
            static_data_stack_pointer_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 66)
              ),
    
            instruction_pointer_ref
              \<mapsto> the 
              (
                call_memory 
                  state 
                  (the (register_state state call_frame_pointer_ref) - 67)
              ) + 1
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_simps)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) RETURN_decomp_mixed:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>RETURN state = 
      state
      \<lparr>
        flag_state := flag_state (set_end_return state),
        register_state := 
          (register_state (restore_registers_after_return state))
          (
            last_instruction_pointer_ref 
              \<mapsto> read_register instruction_pointer_ref state,
            instruction_pointer_ref 
              \<mapsto> read_call_memory 
                ((read_register call_frame_pointer_ref state) - 67)
                state 
              + 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref state) + call_duration,
            call_frame_pointer_ref 
              \<mapsto> (read_register call_frame_pointer_ref state) - 67
          )
      \<rparr>\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_simps)
  apply(simp add: state_manipulation_decomp)
  apply(simp add: fun_upd_twist)
  done

lemma (in Ironbark_world) RETURN_decomp_manipulation:
  assumes
    \<open>typical_flags state\<close>
  shows
    \<open>RETURN state = 
      write_register
        cycles_register_ref
        ((read_register cycles_register_ref state) + call_duration)
        (write_register
          instruction_pointer_ref
          (read_call_memory 
            ((read_register call_frame_pointer_ref state) - 67) 
            state 
          + 1)
          (write_register
            call_frame_pointer_ref
            ((read_register call_frame_pointer_ref state) - 67)
            (restore_registers_after_return (write_register
              last_instruction_pointer_ref
              (read_register instruction_pointer_ref state)
              (set_end_return state)))))\<close>
  using assms
  apply(simp add: instruction_impl_defs)
  apply(simp add: state_manipulation_simps)
  done

end