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

subsection \<open>Security Properties of Ironbark\<close>

theory security_properties

imports
  "execution_auxiliary"

begin

text \<open>In this section, we provide some key results which we believe are relevant to 
demonstrating the security of applications running on the Ironbark processor.\<close>

subsubsection \<open>Program Memory Immutable\<close>

text \<open>The first property we show is that there is no sequence of instructions that can 
result in program memory being written to. We show this over two steps. First, we show 
that an individual instruction cannot modify program memory, and then use an inductive 
step to show it for an arbitrary sequence.\<close>

lemma (in Ironbark_world) program_memory_immutable:
  fixes
    state :: sequential_state
  shows
    \<open>program_memory (execute_next_instruction state) = program_memory state\<close>
  apply(simp add: execute_next_instruction_def)
  apply(simp add: fetch_instruction_def)
  apply(simp add: decode_instruction_def)
  apply(simp add: execute_instruction.simps)
  apply(safe)
  apply(simp_all add: instruction_impl_defs)
  apply(simp_all add: state_manipulation_simps Let_def)
  done

lemma (in Ironbark_world) program_memory_immutable':
  fixes
    state :: sequential_state
  shows
    \<open>program_memory (execute_multiple_instructions state n) = program_memory state\<close>
proof (induct \<open>n\<close>)
  case 0
  then show ?case
    using program_memory_immutable
    by(simp)
next
  case (Suc n)
  then show ?case
    using program_memory_immutable
    by(simp)
qed

text \<open>From this, it follows that reading program memory also never changes, which we also 
show over the following two lemmas (single instruction first, then arbitrary sequence).\<close>

lemma (in Ironbark_world) read_program_memory_immutable:
  fixes
    state :: sequential_state
  shows
    \<open>read_program_memory  a (execute_next_instruction state) 
    = read_program_memory a state\<close>
  by (auto simp add: read_program_memory_def program_memory_immutable)

lemma (in Ironbark_world) read_program_memory_immutable':
  fixes
    state :: sequential_state
  shows
    \<open>read_program_memory  a (execute_multiple_instructions state n) 
    = read_program_memory a state\<close>
  by (auto simp add: read_program_memory_def program_memory_immutable')

text \<open>From this, we then show that the fetch decode and execute operations will all do the same
thing when the instruction pointer is the same\<close>

lemma (in Ironbark_world) fetch_consistent:
  assumes
    \<open>read_register instruction_pointer_ref state1 
    = read_register instruction_pointer_ref state2\<close>

    \<open>state2 = execute_multiple_instructions state1 n\<close>
  shows
    \<open>fetch_instruction state1 = fetch_instruction state2\<close>
  using assms
  by (simp add: fetch_instruction_def read_program_memory_immutable')

lemma (in Ironbark_world) decode_consistent:
  assumes
    \<open>read_register instruction_pointer_ref state1 
    = read_register instruction_pointer_ref state2\<close>

    \<open>state2 = execute_multiple_instructions state1 n\<close>
  shows
    \<open>decode_instruction (fetch_instruction state1) 
    = decode_instruction (fetch_instruction state2)\<close>
  using assms
  by (simp add: fetch_consistent)

lemma (in Ironbark_world) execute_consistent:
  assumes
    \<open>read_register instruction_pointer_ref state1 
    = read_register instruction_pointer_ref state2\<close>

    \<open>state2 = execute_multiple_instructions state1 n\<close>
  shows
    \<open>execute_instruction (decode_instruction (fetch_instruction state1)) 
    = execute_instruction (decode_instruction (fetch_instruction state2))\<close>
  using assms
  by (simp add: decode_consistent)

text \<open>Since program memory is static, we are also able to show that it will be the 
same at the end of any function trace. We show this both for our weak 
finish\_function\_trace, and the more complete full\_function\_trace.\<close>
 
lemma (in Ironbark_world) trace_program_memory:
  \<open>program_memory (last (finish_function_trace [x] y)) = program_memory x\<close>
proof (induct \<open>y\<close>)
  case 0
  then show ?case 
    by(simp add: program_memory_immutable)
next
  case (Suc y)
  then show ?case 
    by(simp add: program_memory_immutable Let_def)
qed
 
 
text \<open>From these, it trivially follows that reading program memory at the end of a 
function trace is unaffected as well.\<close>

lemma (in Ironbark_world) trace_read_program_memory:
  \<open>read_program_memory addr (last (finish_function_trace [x] y)) 
  = read_program_memory addr x\<close>
  by(simp add: read_program_memory_def trace_program_memory)

subsubsection \<open>Restricted Call Memory Modification\<close>

text \<open>Next, we show that the call memory cannot be written to by anything that is not 
a call instruction. We do this over two lemmas, first for a single instruction, and 
then for arbitrary sequences of instructions.\<close>

lemma (in Ironbark_world) call_memory_mostly_immutable:
  fixes 
    state :: sequential_state
  defines
    \<open>instruction_pointer_val \<equiv> read_register instruction_pointer_ref state\<close>
  defines
    \<open>instruction \<equiv> read_program_memory instruction_pointer_val state\<close>
  defines
    \<open>opcode \<equiv> get_opcode instruction\<close>
  assumes
    \<open>opcode \<noteq> CALL_opcode\<close>
  shows
    \<open>call_memory (execute_next_instruction state) = call_memory state\<close>
  using assms
  apply(simp)
  apply(simp add: execute_next_instruction_def)
  apply(simp add: fetch_instruction_def)
  apply(simp add: decode_instruction_def)
  apply(simp add: execute_instruction.simps)
  apply(safe)
  apply(simp_all add: instruction_impl_defs)
  apply(simp_all add: state_manipulation_simps Let_def)
  done

lemma (in Ironbark_world) call_memory_mostly_immutable':
  fixes state :: sequential_state
  assumes
    not_call: 
      \<open>\<forall> m \<le> n . 
        get_opcode 
          (read_program_memory 
            (read_register 
              instruction_pointer_ref 
              (execute_multiple_instructions state m))
            (execute_multiple_instructions state m)) 
        \<noteq> CALL_opcode\<close>
  shows
    \<open>call_memory (execute_multiple_instructions state n) = call_memory state\<close>
proof -
  have
    \<open>m \<le> n 
    \<longrightarrow> call_memory (execute_multiple_instructions state m) = call_memory state\<close> 
    (is "?P m") 
    for m
  proof (induct \<open>m\<close>)
    show 
      \<open>?P 0\<close>
      by (simp)
  next
    fix m
    assume \<open>?P m\<close>
    then show 
      \<open>?P (Suc m)\<close>
      apply(intro impI)
      apply(simp)
      apply(subst call_memory_mostly_immutable)
      apply(rule not_call[rule_format])
      apply(simp)
      apply(simp)
      done
  qed
  then show ?thesis
    by(simp)
qed

text \<open>We also show that the only two instructions which can modify the call frame 
pointer are the call and return instructions. This is done over two lemmas, first for 
a single instruction, and then over an arbitrary sequence.\<close>

lemma (in Ironbark_world) call_frame_pointer_mostly_immutable:
  fixes
    state :: sequential_state
  defines
    \<open>instruction \<equiv> 
      read_program_memory 
        (read_register instruction_pointer_ref state) 
        state\<close>
  defines
    \<open>r1 \<equiv> get_reg1 instruction\<close>
    and \<open>r2 \<equiv> get_reg2 instruction\<close>
    and \<open>r3 \<equiv> get_reg3 instruction\<close>
    and \<open>imm \<equiv> get_immediate instruction\<close>
  assumes
    not_RET: \<open>get_opcode (fetch_instruction state) \<noteq> RETURN_opcode\<close>
    and not_CALL: \<open>get_opcode (fetch_instruction state) \<noteq> CALL_opcode\<close>
  shows
    \<open>read_register call_frame_pointer_ref (execute_next_instruction state) 
    = read_register call_frame_pointer_ref state\<close>
proof (cases \<open>get_halt state = 1 \<or> get_error state = 1\<close>)
  case True
  then show ?thesis
    unfolding execute_next_instruction_def
    by(simp_all)
next
  case False
  also have 
    \<open>get_opcode instruction \<le> 255\<close>
    apply(uint_arith)
    apply(auto)
    done
  ultimately show ?thesis
    using not_CALL not_RET
    unfolding execute_next_instruction_def
    apply(simp add: flag_normalisation)
    unfolding fetch_instruction_def decode_instruction_def
    apply(fold instruction_def)
    apply(fold r1_def r2_def r3_def imm_def)
    apply(simp add: Let_def)
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: execute_instruction.simps)
    apply(simp_all (no_asm) add: instruction_impl_defs)
    apply(simp_all add: state_manipulation_simps Let_def)
    done
qed

lemma (in Ironbark_world) pointer_carry:
  assumes
    not_RET: 
      \<open>\<forall>i \<le> n . 
        get_opcode (fetch_instruction (execute_multiple_instructions state i)) 
          \<noteq> RETURN_opcode\<close>
  and
    not_CALL: 
      \<open>\<forall>i \<le> n . 
        get_opcode (fetch_instruction (execute_multiple_instructions state i)) 
          \<noteq> CALL_opcode\<close>
  shows
    \<open>read_register call_frame_pointer_ref (execute_multiple_instructions state n) 
      = read_register call_frame_pointer_ref state\<close>
proof -
  have
    \<open>i \<le> n \<longrightarrow> 
    (
      read_register call_frame_pointer_ref (execute_multiple_instructions state i)
      = read_register call_frame_pointer_ref state
    )\<close>
  (is "?P i")
  for i
  proof (induct \<open>i\<close>)
    show 
      \<open>?P 0\<close>
      by(simp)
  next
    fix i
    assume \<open>?P i\<close>
    then show 
      \<open>?P (Suc i)\<close>
      apply(intro impI)
      apply(simp)
      apply(subst call_frame_pointer_mostly_immutable)
      apply(simp_all add: not_CALL not_RET)
      done
  qed
  then show ?thesis
    by simp
qed

subsubsection \<open>Register Read and Write Guards\<close>

text \<open>The following two lemmas show that our check\_read\_permission and 
check\_write\_permission work as expected. These lemmas have been shown earlier, and 
reproduced here as we consider it a security property that can be relied upon.\<close>

lemma (in Ironbark_world) check_read_permission_guard:
  fixes 
    a :: \<open>8 word\<close>
  assumes
    \<open>check_read_permission a\<close>
  shows
    \<open>a \<in> readable_registers\<close>
  using assms
  by(simp add: check_read_permission_def)

lemma (in Ironbark_world) check_write_permission_guard:
  assumes
    \<open>check_write_permission a\<close>
  shows
    \<open>a \<in> writeable_registers\<close>
  using assms
  by(simp add: check_write_permission_def)

subsubsection \<open>ROP Prevention\<close>

text \<open>We provide two proofs for the base case for ROP protection. The following lemmas only shows 
the `base' case, rather than the general case, which comes after this. 
Specifically, they show that if a function has no calls or returns in it, then when it 
returns, it will return to the point where it was called from.\<close>

lemma (in Ironbark_world) base_ROP_avoidance:
  fixes
    state1 state2 :: \<open>sequential_state\<close>
    and addr :: \<open>64 word\<close>
    and n :: "nat"
  assumes
    two_after_one: 
      \<open>state2 = execute_next_instruction state1\<close>
    and three_after_two: 
      \<open>state3 = execute_multiple_instructions state2 n\<close>
    and four_after_three: 
      \<open>state4 = execute_next_instruction state3\<close>

    and first_instruction: 
      \<open>execute_instruction (decode_instruction (fetch_instruction state1)) state1 
      = CALL addr state1\<close>
    and end_function: 
      \<open>execute_instruction (decode_instruction (fetch_instruction state3)) state3 
      = RETURN state3\<close>

    and non_RET: 
      \<open>\<forall>i \<le> n . 
        get_opcode (fetch_instruction (execute_multiple_instructions state2 i)) 
        \<noteq> RETURN_opcode\<close>
    and non_CALL: 
      \<open>\<forall>i \<le> n . 
        get_opcode (fetch_instruction (execute_multiple_instructions state2 i)) 
        \<noteq> CALL_opcode\<close>

    and flags1: \<open>typical_flags state1\<close>
    and flags3: \<open>typical_flags state3\<close>
  shows
    \<open>read_register instruction_pointer_ref state4 
    = (read_register instruction_pointer_ref state1) + 1\<close>
proof -
  have
    \<open>execute_next_instruction state3 = RETURN state3\<close>
    unfolding execute_next_instruction_def
    using flags3
    by(simp add: end_function)
  moreover have 
    \<open>execute_next_instruction state1 = CALL addr state1\<close>
    unfolding execute_next_instruction_def
    using flags1
    by(simp add: first_instruction)
  moreover have 
    \<open>read_call_memory 
      (read_register call_frame_pointer_ref state1) 
      (CALL addr state1) 
    = read_register instruction_pointer_ref state1\<close>
    apply(simp add: instruction_decomp_manipulation flags1)
    apply(simp add: state_manipulation_simps)
    apply(simp add: state_manipulation_decomp)
    done
  moreover have
    \<open>call_memory state3 = call_memory state2\<close>
    using three_after_two non_CALL
    apply(simp)
    apply(subst call_memory_mostly_immutable')
    apply(simp_all add: fetch_instruction_def)
    done
  moreover from this have
    \<open>\<forall> addr2 . read_call_memory addr2 state3 = read_call_memory addr2 state2\<close>
    unfolding read_call_memory_def
    by(simp)
  moreover have 
    \<open>read_register call_frame_pointer_ref state3 
    = read_register call_frame_pointer_ref state2\<close>
    using three_after_two non_CALL non_RET
    by(simp add: pointer_carry)
  ultimately show ?thesis
    using assms
    by(simp add: instruction_simps)
qed

lemma (in Ironbark_world) base_ROP_avoidance':
  fixes
    state1 state2 state3 state4 :: \<open>sequential_state\<close>
    and n :: "nat"
    and addr :: \<open>64 word\<close>
  assumes
    two_after_one: 
      \<open>state2 = execute_next_instruction state1\<close>
    and three_after_two: 
      \<open>state3 = execute_multiple_instructions state2 n\<close>
    and four_after_three: 
      \<open>state4 = execute_next_instruction state3\<close>

    and first_instruction: 
      \<open>get_opcode (fetch_instruction state1) = CALL_opcode\<close>
      \<open>get_immediate (fetch_instruction state1) = addr\<close>
    and end_function: 
      \<open>get_opcode (fetch_instruction state3) = RETURN_opcode\<close>

    and non_RET: 
      \<open>\<forall>i \<le> n . 
        get_opcode (fetch_instruction (execute_multiple_instructions state2 i)) 
        \<noteq> RETURN_opcode\<close>
    and non_CALL: 
      \<open>\<forall>i \<le> n . 
        get_opcode (fetch_instruction (execute_multiple_instructions state2 i)) 
        \<noteq> CALL_opcode\<close>

    and flags1: \<open>typical_flags state1\<close>
    and flags3: \<open>typical_flags state3\<close>
  shows
    \<open>read_register instruction_pointer_ref state4 
    = (read_register instruction_pointer_ref state1) + 1\<close>
proof-
  have Ra1: 
    \<open>state2 = CALL addr state1\<close>
    apply(simp add: two_after_one)
    apply(simp add: execute_next_instruction_def)
    apply(simp add: flags1)
    apply(simp add: decode_instruction_def)
    apply(simp add: first_instruction)
    apply(simp add: execute_instruction_simps)
    done
  have
    \<open>state4 = RETURN state3\<close>
    apply(simp add: four_after_three)
    apply(simp add: execute_next_instruction_def)
    apply(simp add: flags3)
    apply(simp add: decode_instruction_def)
    apply(simp add: end_function)
    apply(simp add: execute_instruction_simps)
    done
  with flags3 have
    \<open>read_register instruction_pointer_ref state4 
      = read_call_memory (read_register call_frame_pointer_ref state3 - 67) state3 + 1\<close>
    by (simp add: instruction_simps)
  also have
    \<open>...
      = read_call_memory (read_register call_frame_pointer_ref state2 - 67) state3 + 1\<close>
    using pointer_carry [OF non_RET non_CALL, folded three_after_two] 
    by simp
  also have
    \<open>...
      = read_call_memory (read_register call_frame_pointer_ref state2 - 67) state2 + 1\<close>
    using same_memory_same_addr(2) [OF call_memory_mostly_immutable' 
                  [folded fetch_instruction_def, OF non_CALL, folded three_after_two]]
    by simp
  also have
    \<open>...
      = read_call_memory (read_register call_frame_pointer_ref state1) state2 + 1\<close>
    using flags1
    by (simp add: Ra1 instruction_simps)
  also have
    \<open>...
      = read_register instruction_pointer_ref state1 + 1\<close>
    unfolding Ra1
    apply(simp add: CALL_decomp_manipulation flags1)
    apply(simp add: state_manipulation_simps) 
    apply(simp add: state_manipulation_decomp)
    done
  finally show ?thesis .
qed

text \<open>In working towards the general case, we rely on some auxiliary results about the operation
of the call\_frame\_pointer, which are derived below.\<close>

lemma (in Ironbark_world) call_memory_preserved_step:
  fixes
    state1 state2 :: sequential_state
    and addr :: \<open>64 word\<close>
  defines
    \<open>instruction1 \<equiv> fetch_instruction state1\<close>
  defines
    \<open>opcode1 \<equiv> get_opcode instruction1\<close>
  defines
    \<open>call_memory1 \<equiv> read_call_memory addr state1\<close>
    and \<open>call_memory2 \<equiv> read_call_memory addr state2\<close>
  assumes
    two_after_one: 
      \<open>state2 = execute_next_instruction state1\<close>
    and address_below_call_frame:
      \<open>addr < (read_register call_frame_pointer_ref state1)\<close>
    and no_overflow:
      \<open>(read_register call_frame_pointer_ref state1) < (2^64 - 66)\<close>
  shows
    \<open>read_call_memory addr state1 = read_call_memory addr state2\<close>
  by (simp add: call_memory_evolution [OF two_after_one]
            read_call_memory_backup_registers_before_call [OF address_below_call_frame no_overflow])

lemma (in Ironbark_world) call_memory_preserved_multi_stepJ [THEN mp, OF _ _ _ order_refl]:
  assumes
    start_small:
      \<open>addr \<le> (2^64 - 67)\<close>
    and not_terminated: 
      \<open>\<forall> i \<le> n . 
        addr + 66
        < read_register call_frame_pointer_ref (execute_multiple_instructions state i)\<close>
    and no_overflow: 
      \<open>\<forall>i \<le> n . 
        read_register call_frame_pointer_ref (execute_multiple_instructions state i)  \<le> (2^64 - 67)\<close>
  shows
    \<open>i \<le> n \<longrightarrow> 
      read_call_memory addr (execute_multiple_instructions state i) 
      = read_call_memory addr state\<close>
  apply (induct i, auto)
  apply (rule call_memory_preserved_step [symmetric, THEN trans])
  apply (rule refl, simp_all)
  apply (rule order_less_trans [OF _ not_terminated [rule_format]], simp_all)
  using start_small
  apply (simp add: unat_arith_simps)
  apply (rule order_le_less_trans [OF no_overflow [rule_format]], simp_all)
  done

text \<open>Following from this, we show an argument for ROP protection. Note that the assumption ``depth\_1''
follows from call\_frame\_pointer\_backsubstitute, which shows that the call\_frame\_pointer can only
change by exactly 67, and only increases by 67 in a call, and only decreases by 67 in a return.
Thus, the assumption can be read in English as ``assume we are at a matching return''.\<close>

lemma (in Ironbark_world) ROP_avoidance:
  fixes
    state1 state2 state3 state4 :: \<open>sequential_state\<close>
    and n :: "nat"
    and addr :: \<open>64 word\<close>
  assumes
    two_after_one: 
      \<open>state2 = CALL addr state1\<close> 
    and three_after_two: 
      \<open>state3 = execute_multiple_instructions state2 n\<close>
    and four_after_three: 
      \<open>state4 = RETURN state3\<close> 

    and first_instruction: 
      \<open>get_opcode (fetch_instruction state1) = CALL_opcode\<close>
      \<open>get_immediate (fetch_instruction state1) = addr\<close>  
    and end_function: 
      \<open>get_opcode (fetch_instruction state3) = RETURN_opcode\<close>  
    and depth_1:
      \<open>read_register call_frame_pointer_ref state3 = read_register call_frame_pointer_ref state1 + 67\<close>
    and start_small:
      \<open>read_register call_frame_pointer_ref state1 \<le> (2^64 - 67)\<close>
    and not_terminated: 
      \<open>\<forall> i \<le> n . 
        read_register call_frame_pointer_ref state1 + 66
        < read_register call_frame_pointer_ref (execute_multiple_instructions state2 i)\<close>
    and no_overflow: 
      \<open>\<forall>i \<le> n . 
        read_register call_frame_pointer_ref (execute_multiple_instructions state2 i)  \<le> (2^64 - 67)\<close>

    and flags1: \<open>typical_flags state1\<close>
    and flags3: \<open>typical_flags state3\<close>
  shows
    \<open>read_register instruction_pointer_ref state4 
    = (read_register instruction_pointer_ref state1) + 1\<close>
proof-
  from four_after_three flags3 have
    \<open>read_register instruction_pointer_ref state4 
      = read_call_memory (read_register call_frame_pointer_ref state3 - 67) state3 + 1\<close>
    by (simp add: instruction_simps)
  also have
    \<open>...
      = read_call_memory (read_register call_frame_pointer_ref state1) state3 + 1\<close>
    using depth_1 
    by simp
  also have
    \<open>...
      = read_call_memory (read_register call_frame_pointer_ref state1) state2 + 1\<close>
    unfolding three_after_two
    by (subst call_memory_preserved_multi_stepJ [OF start_small not_terminated no_overflow],
        rule refl)
  also have
    \<open>...
      = read_register instruction_pointer_ref state1 + 1\<close>
    unfolding two_after_one
    apply (simp add: CALL_decomp_manipulation flags1) 
    apply (simp add: state_manipulation_simps) 
    apply (simp add: state_manipulation_decomp)
    done
  finally show ?thesis .
qed


end