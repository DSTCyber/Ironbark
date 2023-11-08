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

subsection \<open>Properties of Sequential Execution Definitions\<close>

theory execution_auxiliary

imports
  "Ironbark_instruction.instruction_top"
  execution_implementations

begin

text \<open>We collect up the various definitions relating to the decode operation for easy 
reference later. These are used to decompose a decode operation into the parameters of 
the execute instruction function.\<close>

lemmas decode_decomp =
  decode_instruction_def
  get_opcode_def
  get_reg1_def
  get_reg2_def
  get_reg3_def
  get_immediate_def
  slice_def
  slice1_def

text \<open>The execute multiple instructions is defined with execute next single instruction 
being applied to the state after the remaining multiple instructions. We show here that 
this is the same as having the next instruction single instruction done first instead.\<close>

lemma (in Ironbark_world) emi_Suc:
  \<open>execute_multiple_instructions state (Suc num_instructions) 
  = execute_multiple_instructions (execute_next_instruction state) num_instructions\<close>
proof(induct \<open>num_instructions\<close> arbitrary: \<open>state\<close>)
  case 0
  then show ?case 
    by(auto)
next
  case (Suc num_instructions)
  then show ?case 
    by(auto)
qed

text \<open>For convenience of future proofs, we provide the following lemma for converting 
the opcode to instruction to be executed.\<close>

lemma (in Ironbark_world) execute_instruction_simps:
  \<open>execute_instruction (0x00, reg1, reg2, reg3, immediate) state 
  = ERROR0 state\<close>

  \<open>execute_instruction (0x01, reg1, reg2, reg3, immediate) state
  = NOP state\<close>

  \<open>execute_instruction (0x02, reg1, reg2, reg3, immediate) state
  = LOAD_IMMEDIATE reg1 immediate state\<close>

  \<open>execute_instruction (0x03, reg1, reg2, reg3, immediate) state
  = LOAD_STATIC_DATA reg1 reg2 state\<close>

  \<open>execute_instruction (0x04, reg1, reg2, reg3, immediate) state
  = STORE_STATIC_DATA reg1 reg2 state\<close>

  \<open>execute_instruction (0x05, reg1, reg2, reg3, immediate) state
  = LOAD_DYNAMIC_DATA reg1 reg2 state\<close>

  \<open>execute_instruction (0x06, reg1, reg2, reg3, immediate) state
  = STORE_DYNAMIC_DATA reg1 reg2 state\<close>

  \<open>execute_instruction (0x07, reg1, reg2, reg3, immediate) state
  = LOAD_INPUT_DATA reg1 reg2 state\<close>

  \<open>execute_instruction (0x08, reg1, reg2, reg3, immediate) state
  = STORE_OUTPUT_DATA reg1 reg2 state\<close>

  \<open>execute_instruction (0x09, reg1, reg2, reg3, immediate) state
  = COPY reg1 reg2 state\<close>

  \<open>execute_instruction (0x0A, reg1, reg2, reg3, immediate) state
  = ADD reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x0B, reg1, reg2, reg3, immediate) state
  = SUBTRACT reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x0C, reg1, reg2, reg3, immediate) state
  = SHIFT_LEFT reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x0D, reg1, reg2, reg3, immediate) state
  = SHIFT_RIGHT reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x0E, reg1, reg2, reg3, immediate) state
  = BITWISE_AND reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x0F, reg1, reg2, reg3, immediate) state
  = BITWISE_OR reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x10, reg1, reg2, reg3, immediate) state
  = BITWISE_XOR reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x11, reg1, reg2, reg3, immediate) state
  = BITWISE_NAND reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x12, reg1, reg2, reg3, immediate) state
  = BITWISE_NOT reg1 reg2 state\<close>

  \<open>execute_instruction (0x13, reg1, reg2, reg3, immediate) state
  = LESS_THAN reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x14, reg1, reg2, reg3, immediate) state
  = GREATER_THAN reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x15, reg1, reg2, reg3, immediate) state
  = EQUALS reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x16, reg1, reg2, reg3, immediate) state
  = NOT_EQUALS reg1 reg2 reg3 state\<close>

  \<open>execute_instruction (0x17, reg1, reg2, reg3, immediate) state
  = RANDOMISE reg1 state\<close>

  \<open>execute_instruction (0x18, reg1, reg2, reg3, immediate) state
  = END_JUMP immediate state\<close>

  \<open>execute_instruction (0x19, reg1, reg2, reg3, immediate) state
  = END_JUMP_STRICT immediate state\<close>

  \<open>execute_instruction (0x1A, reg1, reg2, reg3, immediate) state
  = JUMP immediate state\<close>

  \<open>execute_instruction (0x1B, reg1, reg2, reg3, immediate) state
  = CONDITIONAL_JUMP reg1 immediate state\<close>

  \<open>execute_instruction (0x1C, reg1, reg2, reg3, immediate) state
  = END_CALL state\<close>

  \<open>execute_instruction (0x1D, reg1, reg2, reg3, immediate) state
  = CALL immediate state\<close>

  \<open>execute_instruction (0x1E, reg1, reg2, reg3, immediate) state
  = END_RETURN immediate state\<close>

  \<open>execute_instruction (0x1F, reg1, reg2, reg3, immediate) state
  = RETURN state\<close>

  \<open>execute_instruction (0x20, reg1, reg2, reg3, immediate) state
  = HALT state\<close>

  \<open>execute_instruction (0xFF, reg1, reg2, reg3, immediate) state
  = ERROR1 state\<close>
  by(simp_all add: execute_instruction.simps)

text \<open>The following two lemmas use different methods of showing which opcodes are 
illegal.\<close>

lemma (in Ironbark_world) execute_instruction_ILLEGAL:
  fixes 
    opcode :: \<open>8 word\<close>
  assumes 
    \<open>opcode > 0x20\<close> 
    \<open>opcode < 0xFF\<close>
  shows
    \<open>execute_instruction (opcode, reg1, reg2, reg3, immediate) state = ILLEGAL state\<close>
proof -
  have 
    \<open>opcode \<notin> {
      0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 0xFF
    }\<close>
    using assms 
    by(auto)
  then show ?thesis
    by(simp add: execute_instruction.simps)
qed

lemma (in Ironbark_world) execute_instruction_ILLEGAL':
  fixes 
    opcode :: \<open>8 word\<close>
  assumes 
    \<open>opcode \<notin> {
      0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 13, 14, 15, 16, 
      17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 0xFF
    }\<close>
  shows
    \<open>execute_instruction (opcode, reg1, reg2, reg3, immediate) state \<equiv> ILLEGAL state\<close>
  using assms 
  by(auto simp add: execute_instruction.simps)

text \<open>The following lemmas are for understanding control flow in Ironbark, and the import of the
flags for control flow instructions.\<close>

lemma decodeE:
  assumes
    \<open>get_opcode (fetch_instruction state) = opcode\<close>
  obtains reg1 reg2 reg3 immediate where 
    \<open>decode_instruction (fetch_instruction state) = (opcode, reg1, reg2, reg3, immediate)\<close>
  using assms
  by(simp add: decode_instruction_def)

lemma (in Ironbark_world) typical_flags_backsubstitute:
  fixes
    state1 state2 :: \<open>sequential_state\<close>
  defines
    \<open>instruction \<equiv> fetch_instruction state1\<close>
  defines
    \<open>opcode \<equiv> get_opcode instruction\<close>
    and \<open>addr \<equiv> get_immediate instruction\<close>
  assumes
    two_after_one: \<open>state2 = execute_next_instruction state1\<close>
    and flags2: \<open>typical_flags state2\<close>
  shows
    \<open> if opcode = END_JUMP_opcode \<and> get_end_jump state1 = 1 then
        end_jump_flags state1 \<and>
        read_register last_instruction_pointer_ref state1 = addr 
      else if opcode = END_JUMP_STRICT_opcode then
        end_jump_flags state1 \<and>
        read_register last_instruction_pointer_ref state1 = addr
      else if opcode = END_CALL_opcode then
        end_call_flags state1 \<and>
        get_end_jump state1 = 0
      else if opcode = END_RETURN_opcode then
        end_return_flags state1 \<and>
        read_register last_instruction_pointer_ref state1 = addr
      else
        typical_flags state1\<close>
proof(cases \<open>get_halt state1 = 1 \<or> get_error state1 = 1\<close>)
  case True
  then show ?thesis 
    using two_after_one flags2 
    unfolding execute_next_instruction_def
    by(simp add: flag_normalisation)
next
  case False
  then show ?thesis
  proof(cases \<open>opcode = 24\<close>)
    case True
    moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
    ultimately show ?thesis
    using two_after_one flags2 
    unfolding execute_next_instruction_def
    apply(simp add: flag_normalisation)
    unfolding opcode_def instruction_def addr_def
    apply(elim decodeE)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_impl_defs)
    apply(simp split: if_splits)
    apply(simp_all add: state_manipulation_simps)
    apply(intro impI)
    apply(simp)
    apply(simp add: decode_instruction_def)
    done
  next
    case False
    moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
    ultimately show ?thesis
    proof(cases \<open>opcode = 25\<close>)
      case True
      moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
      ultimately show ?thesis 
        using two_after_one flags2 
        unfolding execute_next_instruction_def
        apply(simp add: flag_normalisation)
        unfolding opcode_def instruction_def addr_def
        apply(elim decodeE)
        apply(simp add: execute_instruction_simps)
        apply(simp add: instruction_impl_defs)
        apply(simp split: if_splits)
        apply(simp_all add: state_manipulation_simps)
        apply(simp add: decode_instruction_def)
        done
    next
      case False
      moreover assume \<open>opcode \<noteq> 24\<close>
      moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
      ultimately show ?thesis 
      proof(cases \<open>opcode = 28\<close>)
        case True
        moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
        ultimately show ?thesis 
          using two_after_one flags2 
          unfolding execute_next_instruction_def
          apply(simp add: flag_normalisation)
          unfolding opcode_def instruction_def addr_def
          apply(elim decodeE)
          apply(simp add: execute_instruction_simps)
          apply(simp add: instruction_impl_defs)
          apply(simp split: if_splits)
          apply(simp_all add: state_manipulation_simps)
          done
      next
        case False
        moreover assume \<open>opcode \<noteq> 24\<close>
        moreover assume \<open>opcode \<noteq> 25\<close>
        moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
        ultimately show ?thesis
        proof(cases \<open>opcode = 30\<close>)
          case True
          moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
          ultimately show ?thesis 
            using two_after_one flags2 
            unfolding execute_next_instruction_def
            apply(simp add: flag_normalisation)
            unfolding opcode_def instruction_def addr_def
            apply(elim decodeE)
            apply(simp add: execute_instruction_simps)
            apply(simp add: instruction_impl_defs)
            apply(simp split: if_splits)
            apply(simp_all add: state_manipulation_simps)
            apply(simp add: decode_instruction_def)
            done
        next
          case False
          moreover assume \<open>opcode \<noteq> 24\<close>
          moreover assume \<open>opcode \<noteq> 25\<close>
          moreover assume \<open>opcode \<noteq> 28\<close>
          moreover assume \<open>\<not> (get_halt state1 = 1 \<or> get_error state1 = 1)\<close>
          ultimately show ?thesis
            using two_after_one flags2 
            apply(simp)
            unfolding execute_next_instruction_def
            apply(simp add: flag_normalisation)
            using opcode_bound [of \<open>fetch_instruction state1\<close>]
            unfolding opcode_def instruction_def
            apply(simp add: word_le_decr)
            apply(elim disjE)
            apply(simp_all add: decode_instruction_def)
            apply(simp_all add: execute_instruction_simps execute_instruction_ILLEGAL)
            apply(simp_all add: instruction_simps)
            apply(simp_all add: instruction_impl_defs)
            apply(simp_all split: if_splits)
            apply(simp_all add: state_manipulation_simps)
            done
        qed
      qed
    qed
  qed
qed

lemma (in Ironbark_world) endjump_set_backsubstitute:
  fixes
    state1 state2 :: \<open>sequential_state\<close>
  defines
    \<open>instruction \<equiv> fetch_instruction state1\<close>
  defines
    \<open>opcode \<equiv> get_opcode instruction\<close> 
  defines
    \<open>addr \<equiv> get_immediate instruction\<close>
  assumes
    two_after_one: \<open>state2 = execute_next_instruction state1\<close>
  assumes
    flags2: \<open>end_jump_flags state2\<close>
  shows
    \<open> (opcode = JUMP_opcode \<or> opcode = CONDITIONAL_JUMP_opcode) \<and>
      typical_flags state1\<close>
proof(cases \<open>get_halt state1 = 1 \<or> get_error state1 = 1\<close>)
  case True
  then show ?thesis
    using two_after_one flags2
    unfolding execute_next_instruction_def
    by (simp)
next
  case False
  then show ?thesis 
    using two_after_one flags2 
    unfolding execute_next_instruction_def opcode_def instruction_def
    apply(simp add: flag_normalisation)
    using opcode_bound [of \<open>fetch_instruction state1\<close>]
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: decode_instruction_def)
    apply(simp_all add: execute_instruction_simps execute_instruction_ILLEGAL)
    apply(simp_all add: instruction_simps)
    apply(simp_all add: instruction_impl_defs)
    apply(simp_all split: if_splits)
    apply(simp_all add: state_manipulation_simps)
    done
qed

lemma (in Ironbark_world) endcall_set_backsubstitute:
  fixes
    state1 state2 :: \<open>sequential_state\<close>
  defines
    \<open>instruction \<equiv> fetch_instruction state1\<close>
  defines
    \<open>opcode \<equiv> get_opcode instruction\<close>
  defines
    \<open>addr \<equiv> get_immediate instruction\<close>
  assumes
    two_after_one: \<open>state2 = execute_next_instruction state1\<close>
  assumes
      flags2: \<open>end_call_flags state2\<close>
  shows
    \<open> (opcode = CALL_opcode) \<and>
      typical_flags state1\<close>
proof(cases \<open>get_halt state1 = 1 \<or> get_error state1 = 1\<close>)
  case True
  then show ?thesis
    using two_after_one flags2
    unfolding execute_next_instruction_def
    by (simp)
next
  case False
  then show ?thesis 
    using two_after_one flags2 
    unfolding execute_next_instruction_def opcode_def instruction_def
    apply(simp add: flag_normalisation)
    using opcode_bound [of \<open>fetch_instruction state1\<close>]
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: decode_instruction_def)
    apply(simp_all add: execute_instruction_simps execute_instruction_ILLEGAL)
    apply(simp_all add: instruction_simps)
    apply(simp_all add: instruction_impl_defs)
    apply(simp_all split: if_splits)
    apply(simp_all add: state_manipulation_simps)
    done
qed

lemma (in Ironbark_world) endreturn_set_backsubstitute:
  fixes
    state1 state2 :: \<open>sequential_state\<close>
  defines
    \<open>instruction \<equiv> fetch_instruction state1\<close>
  defines
    \<open>opcode \<equiv> get_opcode instruction\<close>
  defines
    \<open>addr \<equiv> get_immediate instruction\<close>
  assumes
    two_after_one: \<open>state2 = execute_next_instruction state1\<close>
  assumes 
    flags2: \<open>end_return_flags state2\<close>
  shows
    \<open> (opcode = RETURN_opcode) \<and>
      typical_flags state1\<close>
proof(cases \<open>get_halt state1 = 1 \<or> get_error state1 = 1\<close>)
  case True
  then show ?thesis
    using two_after_one flags2
    unfolding execute_next_instruction_def
    by (simp)
next
  case False
  then show ?thesis 
    using two_after_one flags2 
    unfolding execute_next_instruction_def opcode_def instruction_def
    apply(simp add: flag_normalisation)
    using opcode_bound [of \<open>fetch_instruction state1\<close>]
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: decode_instruction_def)
    apply(simp_all add: execute_instruction_simps execute_instruction_ILLEGAL)
    apply(simp_all add: instruction_simps)
    apply(simp_all add: instruction_impl_defs)
    apply(simp_all split: if_splits)
    apply(simp_all add: state_manipulation_simps)
    done
qed

lemma (in Ironbark_world) call_frame_pointer_evolution:
  fixes
    state :: sequential_state
  defines
    \<open>instruction \<equiv> fetch_instruction state\<close>
  defines
    \<open>opcode \<equiv> get_opcode instruction\<close>
  shows
    \<open>read_register call_frame_pointer_ref (execute_next_instruction state) 
    = (
        if typical_flags state \<and> opcode = CALL_opcode then
          read_register call_frame_pointer_ref state + 67
        else if typical_flags state \<and> opcode = RETURN_opcode then
          read_register call_frame_pointer_ref state - 67
        else 
          read_register call_frame_pointer_ref state 
      )\<close>
proof(cases \<open>typical_flags state\<close>)
  case True
  then show ?thesis 
    apply(simp add: execute_next_instruction_def opcode_def instruction_def)
    apply(intro conjI impI)
    apply(elim decodeE, simp add: execute_instruction.simps)
    apply(simp (no_asm) add: instruction_impl_defs)
    apply(simp add: state_manipulation_simps Let_def)
    apply(elim decodeE, simp add: execute_instruction.simps)
    apply(simp (no_asm) add: instruction_impl_defs)
    apply(simp add: state_manipulation_simps Let_def)
    using opcode_bound [of \<open>instruction\<close>]
    apply(fold instruction_def)
    unfolding fetch_instruction_def decode_instruction_def
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: execute_instruction_simps execute_instruction_ILLEGAL)
    apply(simp_all add: instruction_simps)
    apply(simp_all add: instruction_impl_defs)
    apply(simp_all add: state_manipulation_simps Let_def)
    done
next
  case False
  moreover from this have 
    \<open>\<not> (typical_flags state \<and> opcode = 29)\<close>
    \<open>\<not> (typical_flags state \<and> opcode = 31)\<close>
    by(safe)
  ultimately show ?thesis 
    apply(simp only: if_splits)
    apply(simp add: flag_normalisation)
    apply(cases \<open>get_halt state = 1 \<or> get_error state = 1\<close>)
    apply(simp_all add: execute_next_instruction_def)
    apply(simp add: flag_normalisation)
    apply(fold instruction_def)
    unfolding fetch_instruction_def decode_instruction_def
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: execute_instruction.simps)
    apply(simp_all add: instruction_simps)
    apply(safe)
    apply(simp_all add: instruction_simps)
    apply(simp_all (no_asm) add: instruction_impl_defs)
    apply(simp_all add: state_manipulation_simps)
    done
qed

lemma (in Ironbark_world) call_frame_pointer_backsubstitute:
  fixes
    state1 state2 :: sequential_state
  defines
    \<open>instruction1 \<equiv> fetch_instruction state1\<close>
  defines
    \<open>opcode1 \<equiv> get_opcode instruction1\<close>
  defines
    \<open>call_frame_pointer1 \<equiv> read_register call_frame_pointer_ref state1\<close>
    and \<open>call_frame_pointer2 \<equiv> read_register call_frame_pointer_ref state2\<close>
  assumes
    two_after_one: 
      \<open>state2 = execute_next_instruction state1\<close>
  shows
    \<open>read_register call_frame_pointer_ref state1 
    = (
        if typical_flags state1 \<and> opcode1 = CALL_opcode then
          call_frame_pointer2 - 67
        else if typical_flags state1 \<and> opcode1 = RETURN_opcode then
          call_frame_pointer2 + 67
        else 
          call_frame_pointer2 
      )\<close>
  unfolding call_frame_pointer2_def two_after_one call_frame_pointer_evolution
  apply(fold instruction1_def opcode1_def call_frame_pointer1_def)
  apply(simp only: split: if_splits)
  apply(intro impI conjI)
  apply(simp_all)
  done

lemma (in Ironbark_world) call_memory_evolution:
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
  shows
    \<open>call_memory2 
      = ( 
          if typical_flags state1 \<and> opcode1 = CALL_opcode then
            read_call_memory addr (backup_registers_before_call state1)
          else
            call_memory1
        )\<close>
proof(cases \<open>get_halt state1 = 1 \<or> get_error state1 = 1\<close>)
  case True
  then show ?thesis 
    unfolding call_memory2_def two_after_one
    apply(simp add: execute_next_instruction_def call_memory1_def)
    apply(auto)
    done
next
  case False
  then show ?thesis 
    unfolding call_memory2_def two_after_one
    apply(simp add: execute_next_instruction_def call_memory1_def)
    using opcode_bound [of \<open>instruction1\<close>]
    apply(fold instruction1_def)
    unfolding fetch_instruction_def decode_instruction_def
    apply(fold opcode1_def)
    apply(simp add: word_le_decr)
    apply(elim disjE)
    apply(simp_all add: execute_instruction.simps)
    apply(simp_all (no_asm) add: instruction_impl_defs)
    apply(simp_all add: state_manipulation_simps)
    apply(simp_all add: state_manipulation_reorder)
    apply(simp_all add: state_manipulation_simps)
    done
qed

text \<open>The last thing we show here is some trivial properties of our definition of 
finish\_function\_trace. Namely, we show that a trace is not empty, the start of the 
trace is the starting state, and the starting state is in the trace.\<close>
 
lemma (in Ironbark_world) trace_rules:
  \<open>finish_function_trace [x] y \<noteq> []\<close>
  \<open>hd (finish_function_trace [x] y) = x\<close>
  \<open>x \<in> set (finish_function_trace [x] y)\<close>
proof (induct \<open>y\<close>)
  case 0
  then show
   \<open>finish_function_trace [x] 0 \<noteq> []\<close>
   \<open>hd (finish_function_trace [x] 0) = x\<close>
   \<open>x \<in> set (finish_function_trace [x] 0)\<close>
   by(simp_all)
next
  case (Suc y)
  then show 
    \<open>finish_function_trace [x] (Suc y) \<noteq> []\<close>
    \<open>hd (finish_function_trace [x] (Suc y)) = x\<close>
    \<open>x \<in> set (finish_function_trace [x] (Suc y))\<close>
    by(simp_all add: Let_def)
qed

end
