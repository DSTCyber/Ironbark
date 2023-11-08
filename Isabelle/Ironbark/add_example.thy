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

subsection \<open>Correctness of basic program\<close>

theory add_example

imports
  "Ironbark_execution.execution_top"

begin

text \<open>This file just contains a proof of a specific program doing 1 + 1 add will get 
the correct result (i.e. 2), along with some other claims about the state.\<close>

text \<open>The proof is structured to first have what instructions will be executed, before 
finally showing the proof goal.\<close>

lemma (in Ironbark_world) add_example:
  fixes 
    state :: sequential_state
  defines
    \<open>program \<equiv> 
      Map.empty 
      (
        0  \<mapsto> 0x020100000000000000000001,  \<comment>\<open>r01 = 0x1\<close>
        1  \<mapsto> 0x0A0201010000000000000000,  \<comment>\<open>r02 = r01 + r01\<close>
        2  \<mapsto> 0x200000000000000000000000   \<comment>\<open>halt\<close>
      )\<close>
  defines
    \<open>check_state \<equiv> \<lambda> state .
        read_register instruction_pointer_ref state = 2 
      \<and> halt_flags state 
      \<and> read_register r02_ref state = 2 
      \<and> read_register cycles_register_ref state = 2 * common_instruction_duration\<close>
  shows
    \<open>check_state 
      (execute_multiple_instructions 
        (initial_state\<lparr>program_memory := program\<rparr>)
        3)\<close>
proof -

  have
    \<open>read_register instruction_pointer_ref (initial_state\<lparr>program_memory := program\<rparr>) 
    = 0\<close>
    by(simp add: program_def initial_state_def read_register_decomp)

  have
    \<open>execute_next_instruction (initial_state\<lparr>program_memory := program\<rparr>) 
    = LOAD_IMMEDIATE r01_ref 1 (initial_state\<lparr>program_memory := program\<rparr>)\<close>
    apply(simp add: execute_next_instruction_def)
    apply(simp add: state_manipulation_simps)
    apply(simp add: fetch_instruction_def)
    apply(simp add: state_manipulation_simps)
    apply(simp add: read_program_memory_def)
    apply(subst program_def)
    apply(simp add: decode_instruction_def)
    apply(simp add: state_manipulation_decomp)
    apply(simp add: execute_instruction_simps)
    done

  then have
    \<open>execute_next_instruction 
      (execute_next_instruction 
        (initial_state\<lparr>program_memory := program\<rparr>))
    = ADD 
        r02_ref 
        r01_ref 
        r01_ref 
        (LOAD_IMMEDIATE r01_ref 1 (initial_state\<lparr>program_memory := program\<rparr>))\<close>
    apply(simp add: execute_next_instruction_def)
    apply(simp add: instruction_simps)
    apply(simp add: fetch_instruction_def)
    apply(simp add: instruction_simps)
    apply(simp add: state_manipulation_simps)
    apply(simp add: read_program_memory_def)
    apply(subst program_def)
    apply(simp add: decode_instruction_def)
    apply(simp add: state_manipulation_decomp)
    apply(simp add: execute_instruction_simps)
    done

  then have
    \<open>execute_next_instruction 
      (execute_next_instruction 
        (execute_next_instruction 
          (initial_state\<lparr>program_memory := program\<rparr>))) 
    = HALT 
        (ADD 
          r02_ref 
          r01_ref 
          r01_ref 
          (LOAD_IMMEDIATE r01_ref 1 (initial_state\<lparr>program_memory := program\<rparr>)))\<close>
    apply(simp)
    apply(simp (no_asm) add: execute_next_instruction_def)
    apply(simp add: instruction_simps)
    apply(simp add: fetch_instruction_def)
    apply(simp add: instruction_simps)
    apply(simp add: state_manipulation_simps)
    apply(simp add: read_program_memory_def)
    apply(subst program_def)
    apply(simp add: decode_instruction_def)
    apply(simp add: state_manipulation_decomp)
    apply(simp add: execute_instruction_simps)
    done

  then show 
    ?thesis
    apply(simp add: execute_multiple_instructions_def)
    apply(simp add: check_state_def)
    apply(intro conjI)
    apply(simp_all add: HALT_decomp_manipulation instruction_simps)
    apply(simp_all add: state_manipulation_simps)
    apply(simp_all add: instruction_simps)
    apply(simp_all add: state_manipulation_simps)
    done
qed

end