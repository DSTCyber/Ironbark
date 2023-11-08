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

subsection \<open>Pieacemeal Correctness of Fibonacci as a Program\<close>

theory fibonacci_invariant_piecemeal

imports
  "Ironbark_execution.execution_top"

begin

text \<open>This file contains a proof of correctness of a function which calculates 
Fibonacci numbers. Specifically, this proof is done as a series of individual smaller 
proofs, rather than a single large proof with many subcomponents.\<close>

text \<open>We start by defining the Fibonacci function from a pure mathematical point of 
view, which we will later show is equivalent to the return value of our function 
(modulo $2^{64}$).\<close>

function fib :: \<open>nat \<Rightarrow> nat\<close>
  where
  \<open>fib 0 = 1\<close>
| \<open>fib 1 = 1\<close>
| \<open>fib (n+2) = fib n + fib (n+1)\<close>
  apply(atomize_elim)
  apply(arith)
  apply(auto)
  done
termination by lexicographic_order

text \<open>The following lemma tries to exhaust the various ways in which Suc can appear
with the fib function and rewrite it in terms of +. This is done because we we prefer 
to work with the + operator.\<close>

lemma fib_stuff:
  \<open>fib (n+3) = fib (n+1) + fib (n+2)\<close>
  \<open>fib (Suc (Suc n)) = fib n + fib (n+1)\<close>
  \<open>fib (Suc (Suc (Suc n))) = fib (n+1) + fib (n+2)\<close>
  \<open>fib (Suc 0) = 1\<close>
  \<open>fib (Suc (Suc n)) = fib (n+2)\<close>
  \<open>fib (Suc n) = fib (n+1)\<close>
  \<open>fib (Suc (n+1)) = fib (n+2)\<close>
  \<open>fib ((Suc n)+1) = fib (n+2)\<close>
  \<open>fib (Suc (n+2)) = fib (n+3)\<close>
  \<open>fib (n+1+2) = fib (n+3)\<close>
  \<open>fib (Suc (Suc 0)) = 2\<close>
  \<open>fib (n+0) = fib n\<close>
  \<open>fib (0+n) = fib n\<close>
  \<open>fib (Suc (Suc (Suc n))) = fib (n+3)\<close>
  using fib.simps 
  by(simp_all add: numeral_3_eq_3)

text \<open>We found it is sometimes useful to be able to lookup the answers for early 
Fibonacci numbers, so we collect a few of the early answers for convenience.\<close>

lemma fib_answers:
  \<open>fib (Suc 0) = 1\<close>
  \<open>fib 2 = 2\<close>
  \<open>fib (Suc 1) = 2\<close>
  \<open>fib (Suc (Suc 0)) = 2\<close>
  \<open>fib 3 = 3\<close>
  \<open>fib 4 = 5\<close>
  using fib.simps by(simp_all add: numeral_3_eq_3 numeral_Bit0)

text \<open>We now define the program, which we will show correctly implements the Fibonacci 
function.\<close>

definition program :: \<open>64 word \<Rightarrow> 96 word option\<close>
  where
    \<open>program \<equiv> Map.empty 
    (
        0   \<mapsto> 0x022100000000000000000001, \<comment>\<open>c01 = 0x1\<close>
        1   \<mapsto> 0x020300000000000000000000, \<comment>\<open>r03 = 0x0\<close>
        2   \<mapsto> 0x020000000000000000000001, \<comment>\<open>r00 = 0x1\<close>
        3   \<mapsto> 0x020100000000000000000001, \<comment>\<open>r01 = 0x1\<close>
        4   \<mapsto> 0x020200000000000000000002, \<comment>\<open>r02 = 0x2\<close>
        5   \<mapsto> 0x18000000000000000000000C, \<comment>\<open>end\_jump 0xC\<close>
        6   \<mapsto> 0x150403300000000000000000, \<comment>\<open>r04 = r03 == arg00\<close>
        7   \<mapsto> 0x1B040000000000000000000d, \<comment>\<open>if (r04) jump 0x000000000000000d\<close>
        8   \<mapsto> 0x090001000000000000000000, \<comment>\<open>r00 = r01\<close>
        9   \<mapsto> 0x090102000000000000000000, \<comment>\<open>r01 = r02\<close>
        10  \<mapsto> 0x0A0200010000000000000000, \<comment>\<open>r02 = r00 + r01\<close>
        11  \<mapsto> 0x0A0303210000000000000000, \<comment>\<open>r03 = r03 + c01\<close>
        12  \<mapsto> 0x1A0000000000000000000005, \<comment>\<open>jump 0x0000000000000005\<close>
        13  \<mapsto> 0x180000000000000000000007, \<comment>\<open>end\_jump 0x7\<close>
        14  \<mapsto> 0x094000000000000000000000, \<comment>\<open>ret00 = r00\<close>
        15  \<mapsto> 0x200000000000000000000000  \<comment>\<open>halt\<close>
    )\<close>

text \<open>We also define what it means for our program to be `correct'. Because we use an 
inductive process with the following as our invariant, the approach we have taken is 
to state what we expect to be true at every step of the program. We've annotated this 
with the assembly being executed at each step, and what we really mean by correctness 
is what we show in the halt step (at the end of the definition), and the rest of these 
are intermediate results useful for the inductive process.\<close>

definition
  invariant :: \<open>sequential_state \<Rightarrow> bool\<close>
  where
    \<open>invariant state \<equiv>
      \<comment>\<open>c01 = 0x1\<close>
      (read_register instruction_pointer_ref state = 0 
        \<longrightarrow> typical_flags state)

      \<comment>\<open>r03 = 0    //counter\<close>
      \<and> (read_register instruction_pointer_ref state = 1 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
      ))

      \<comment>\<open>r00 = 1    //fib(counter)\<close>
      \<and> (read_register instruction_pointer_ref state = 2 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state = 0
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
      ))

      \<comment>\<open>r01 = 1    //fib(counter+1)\<close>
      \<and> (read_register instruction_pointer_ref state = 3 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state = 0
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
      ))

      \<comment>\<open>r02 = 2    //fib(counter+2))\<close>
      \<and> (read_register instruction_pointer_ref state = 4 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state = 0
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
      ))

      \<comment>\<open>end jump\<close>
      \<and> (read_register instruction_pointer_ref state = 5 \<longrightarrow>
      (
        (typical_flags state \<or> end_jump_flags state)
        \<and> (typical_flags state
          \<longrightarrow> (read_register last_instruction_pointer_ref state = 4))
        \<and> (end_jump_flags state
          \<longrightarrow> (read_register last_instruction_pointer_ref state = 12))
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
      ))

      \<comment>\<open>r04 = r03 == arg00\<close>
      \<and> (read_register instruction_pointer_ref state = 6 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
      ))

      \<comment>\<open>if (r04) jump finish   //if (counter == n) {finish}\<close>
      \<and> (read_register instruction_pointer_ref state = 7 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
        \<and> ((read_register r03_ref state = read_register arg00_ref state)
          \<longleftrightarrow> (read_register r04_ref state = 1))
        \<and> ((read_register r03_ref state \<noteq> read_register arg00_ref state) 
          \<longleftrightarrow> (read_register r04_ref state = 0))
        \<and> (read_register r04_ref state = 1 \<or> read_register r04_ref state = 0)
      ))

      \<comment>\<open>r00 = r01   //fib(counter)   <- fib(counter+1)\<close>
      \<and> (read_register instruction_pointer_ref state = 8 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state < read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
      ))

      \<comment>\<open>r01 = r02   //fib(counter+1) <- fib(counter+2)\<close>
      \<and> (read_register instruction_pointer_ref state = 9 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state < read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
      ))

      \<comment>\<open>r02 = r00 + r01  //fib(counter+2) <- fib(counter+3)\<close>
      \<and> (read_register instruction_pointer_ref state = 10 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state < read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
      ))

      \<comment>\<open>r03 = r03 + c01  //counter++\<close>
      \<and> (read_register instruction_pointer_ref state = 11 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state < read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 3))
      ))

      \<comment>\<open>jump main loop\<close>
      \<and> (read_register instruction_pointer_ref state = 12 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register c01_ref state = 1
        \<and> read_register r03_ref state \<le> read_register arg00_ref state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
      ))

      \<comment>\<open> end jump \<close>
      \<and> (read_register instruction_pointer_ref state = 13 \<longrightarrow>
      (
        end_jump_flags state
        \<and> read_register last_instruction_pointer_ref state = 7
        \<and> read_register c01_ref state = 1
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r01_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 1))
        \<and> read_register r02_ref state 
          = of_nat (fib (unat (read_register r03_ref state) + 2))
        \<and> read_register r03_ref state = read_register arg00_ref state
      ))

      \<comment>\<open>ret0 = r0\<close>
      \<and> (read_register instruction_pointer_ref state = 14 \<longrightarrow> 
      (
        typical_flags state
        \<and> read_register r00_ref state 
          = of_nat (fib (unat (read_register r03_ref state)))
        \<and> read_register r03_ref state = read_register arg00_ref state
      ))

      \<comment>\<open>halt\<close>
      \<and> (read_register instruction_pointer_ref state = 15 \<longrightarrow> 
      (
        get_end_return state = 0
        \<and> get_end_call state = 0
        \<and> get_end_jump state = 0
        \<and> get_error state = 0
        \<and> read_register r03_ref state = read_register arg00_ref state
        \<and> read_register ret00_ref state 
          = of_nat (fib (unat (read_register arg00_ref state)))
      ))\<close>

text \<open>The next series of lemmas show that the invariant holds after the next 
instruction has been executed, assuming the invariant was true at the start. We do 
this for each step in the program. The structure of each of these proofs is to first 
show how the instruction will change the state, and then show that the state change 
will satisfy the invariant conditions.

Showing the invariant was true at the start will be done later.\<close>

lemma (in Ironbark_world) fib_equivalence_invariant_step0:
  fixes 
    current_state :: sequential_state
  defines
    \<open>last_step_invariant \<equiv> \<lambda> state .
      typical_flags state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> next_state .
      typical_flags next_state \<and>
      read_register c01_ref next_state = 1 \<and>
      read_register instruction_pointer_ref next_state = 1\<close>
  assumes
    previous_step_invariant:
      \<open>last_step_invariant current_state\<close>
      \<open>read_register instruction_pointer_ref current_state = 0\<close>
      \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant (execute_next_instruction current_state)\<close>
proof -
  have 
    \<open>execute_next_instruction current_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            c01_ref 
              \<mapsto> 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 0,
            instruction_pointer_ref 
              \<mapsto> 1
          )
      \<rparr>\<close>
    using previous_step_invariant
    apply(simp add: last_step_invariant_def)
    apply(unfold execute_next_instruction_def)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_register_decomp read_program_memory_def)
    apply(simp (no_asm) add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: state_manipulation_decomp)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref (execute_next_instruction current_state) = 1\<close>
    \<open>typical_flags (execute_next_instruction current_state)\<close>
    \<open>read_register c01_ref (execute_next_instruction current_state) = 1\<close>
    using previous_step_invariant
    by(simp_all add: last_step_invariant_def state_manipulation_decomp)
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step1:
  fixes 
    current_state :: sequential_state
  defines
    \<open>last_step_invariant \<equiv> \<lambda> state .
      typical_flags state \<and>
      read_register c01_ref state = 1\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> next_state .
      typical_flags next_state \<and>
      read_register c01_ref next_state = 1 \<and>
      read_register instruction_pointer_ref next_state = 2 \<and>
      read_register r03_ref next_state = 0 \<and>
      read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  assumes
    previous_step_invariant:
      \<open>last_step_invariant current_state\<close>
      \<open>read_register instruction_pointer_ref current_state = 1\<close>
      \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant (execute_next_instruction current_state)\<close>
proof -
  have 
    \<open>typical_flags current_state\<close>
    \<open>read_register c01_ref current_state = 1\<close>
    using previous_step_invariant
    by(simp_all add: last_step_invariant_def)
  moreover have 
    \<open>execute_next_instruction current_state = LOAD_IMMEDIATE 3 0 current_state\<close>
  proof -
    have 
      \<open>decode_instruction (fetch_instruction current_state) = (2, 3, 0, 0, 0)\<close>
      using previous_step_invariant
      unfolding fetch_instruction_def
      apply(simp add: read_program_memory_def)
      apply(simp (no_asm) add: program_def)
      apply(simp add: decode_decomp)
      done
    then show 
      \<open>execute_next_instruction current_state = LOAD_IMMEDIATE 3 0 current_state\<close>
      using previous_step_invariant
      unfolding last_step_invariant_def
      unfolding execute_next_instruction_def
      by(simp add: execute_instruction_simps)
  qed
  ultimately have
    \<open>execute_next_instruction current_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r03_ref 
              \<mapsto> 0,
            last_instruction_pointer_ref 
              \<mapsto> 1,
            instruction_pointer_ref 
              \<mapsto> 2,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration
          )
      \<rparr>\<close>
    using previous_step_invariant
    by(simp add: instruction_decomp_mixed)
  then have
    \<open>read_register instruction_pointer_ref (execute_next_instruction current_state) 
    = 2\<close>

    \<open>typical_flags (execute_next_instruction current_state)\<close>
    \<open>read_register c01_ref (execute_next_instruction current_state) = 1\<close>
    \<open>read_register r03_ref (execute_next_instruction current_state) = 0\<close>

    \<open>read_register r03_ref (execute_next_instruction current_state) 
    \<le> read_register arg00_ref (execute_next_instruction current_state)\<close>
    using previous_step_invariant
    by(simp_all add: last_step_invariant_def state_manipulation_decomp)
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step2:
  fixes 
    current_state :: sequential_state
  defines
    \<open>last_step_invariant \<equiv> \<lambda> state .
      typical_flags state \<and>
      read_register c01_ref state = 1 \<and>
      read_register r03_ref state = 0 \<and>
      read_register r03_ref state \<le> read_register arg00_ref state\<close>
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state \<and>
      read_register c01_ref state = 1 \<and>
      read_register instruction_pointer_ref state = 3 \<and>
      read_register r03_ref state = 0 \<and>
      read_register r03_ref state \<le> read_register arg00_ref state \<and>
      read_register r00_ref state = of_nat (fib (unat (read_register r03_ref state)))\<close>
  assumes
    previous_step_invariant: \<open>last_step_invariant current_state\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 2\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r00_ref 
              \<mapsto> 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 2,
            instruction_pointer_ref 
              \<mapsto> 3
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp add: last_step_invariant_def)
    apply(elim conjE)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 3\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state = 0\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r00_ref next_state = 1\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
    using previous_step_invariant program_state
    by(simp_all add: last_step_invariant_def state_manipulation_decomp)
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step3:
  fixes 
    current_state :: sequential_state
  defines
    \<open>last_step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register r03_ref state = 0 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state)))\<close>
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 4 
      \<and> read_register r03_ref state = 0 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state))) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1))\<close>
  assumes
    previous_step_invariant: \<open>last_step_invariant current_state\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 3\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r01_ref 
              \<mapsto> 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 3,
            instruction_pointer_ref 
              \<mapsto> 4
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp add: last_step_invariant_def)
    apply(elim conjE)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have 
    \<open>read_register instruction_pointer_ref next_state = 4\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state = 0\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r00_ref next_state = 1\<close>
    \<open>read_register r01_ref next_state = 1\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
    
    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
    using previous_step_invariant program_state
    by(simp_all add: last_step_invariant_def state_manipulation_decomp fib_answers)
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step4:
  fixes 
    current_state :: sequential_state
  defines
    \<open>last_step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register r03_ref state = 0 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state))) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1))\<close>
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 5 
      \<and> read_register last_instruction_pointer_ref state = 4 
      \<and> read_register r03_ref state = 0 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state))) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))\<close>
  assumes
    previous_step_invariant: \<open>last_step_invariant current_state\<close>
    and previous_step: \<open>read_register instruction_pointer_ref current_state = 4\<close>
    and program_state: \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r02_ref 
              \<mapsto> 2,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 4,
            instruction_pointer_ref 
              \<mapsto> 5
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp add: last_step_invariant_def)
    apply(elim conjE)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have 
    \<open>read_register instruction_pointer_ref next_state = 5\<close>
    \<open>read_register last_instruction_pointer_ref next_state = 4\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state = 0\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r00_ref next_state = 1\<close>
    \<open>read_register r01_ref next_state = 1\<close>
    \<open>read_register r02_ref next_state = 2\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    using previous_step_invariant program_state
    by(simp_all add: last_step_invariant_def state_manipulation_decomp fib_answers
        del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step5:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 6 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state))) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state \<or> end_jump_flags current_state\<close>

      \<open>end_jump_flags current_state 
      \<longrightarrow> (read_register last_instruction_pointer_ref current_state = 12)\<close>

      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state \<le> read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>

    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 5\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        flag_state := (flag_state current_state)\<lparr>end_jump := 0\<rparr>,
        register_state := 
          (register_state current_state)
          (
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 5,
            instruction_pointer_ref 
              \<mapsto> 6
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp add: step_invariant_def)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_impl_defs)
    apply(cases \<open>get_end_jump current_state = 0\<close>)
    apply(simp_all add: flag_normalisation)
    apply(simp_all add: state_manipulation_decomp)
    apply(simp_all add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 6\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    using previous_step_invariant program_state
    by(auto simp add: read_register_decomp read_flag_decomp)
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step6:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state
      \<and> read_register c01_ref state = 1
      \<and> read_register instruction_pointer_ref state = 7
      \<and> read_register r03_ref state \<le> read_register arg00_ref state
      \<and> (read_register r04_ref state = 1 \<or> read_register r04_ref state = 0)
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state)))
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1))
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))

      \<and> ((read_register r03_ref state = read_register arg00_ref state) 
        \<longleftrightarrow> (read_register r04_ref state = 1))

      \<and> ((read_register r03_ref state \<noteq> read_register arg00_ref state) 
        \<longleftrightarrow> (read_register r04_ref state = 0))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state \<le> read_register arg00_ref current_state\<close>
      \<open>read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>

      \<open>read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
    and previous_step: \<open>read_register instruction_pointer_ref current_state = 6\<close>
    and program_state: \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have 
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := (register_state current_state)
        (
          r04_ref \<mapsto> 
            if 
              read_register arg00_ref current_state 
              = read_register r03_ref current_state
            then 
              1 
            else 
              0,
          cycles_register_ref 
            \<mapsto> (read_register cycles_register_ref current_state) 
              + common_instruction_duration,
          last_instruction_pointer_ref 
            \<mapsto> 6,
          instruction_pointer_ref 
            \<mapsto> 7
        )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 7\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r04_ref next_state = 1 \<or> read_register r04_ref next_state = 0\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>

    \<open>(read_register r03_ref next_state = read_register arg00_ref next_state) 
    \<longleftrightarrow> (read_register r04_ref next_state = 1)\<close>

    \<open>(read_register r03_ref next_state \<noteq> read_register arg00_ref next_state) 
    \<longleftrightarrow> (read_register r04_ref next_state = 0)\<close>

    \<open>(read_register arg00_ref next_state \<noteq> read_register r03_ref next_state) 
    \<longleftrightarrow> (read_register r03_ref next_state < read_register arg00_ref next_state)\<close>
    using previous_step_invariant program_state
    apply(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
    apply(auto)
    done
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step7:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      (read_register r04_ref state = 1 \<or> read_register r04_ref state = 0)
      \<and> (read_register r04_ref state = 0 \<longrightarrow> typical_flags state)
      \<and> (read_register r04_ref state = 1 \<longrightarrow> end_jump_flags state)
      \<and> read_register c01_ref state = 1
      \<and> read_register r03_ref state \<le> read_register arg00_ref state

      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state)))

      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1))

      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))

      \<and> read_register last_instruction_pointer_ref state = 7

      \<and> (read_register instruction_pointer_ref state = 8 
          \<or> read_register instruction_pointer_ref state = 13)

      \<and> ((read_register r03_ref state = read_register arg00_ref state) 
          \<longleftrightarrow> (read_register r04_ref state = 1))

      \<and> ((read_register r03_ref state \<noteq> read_register arg00_ref state) 
          \<longleftrightarrow> (read_register r04_ref state = 0))

      \<and> ((read_register r04_ref state = 0) 
          \<longleftrightarrow> (read_register instruction_pointer_ref state = 8))

      \<and> ((read_register r04_ref state = 1) 
          \<longleftrightarrow> (read_register instruction_pointer_ref state = 13))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state \<le> read_register arg00_ref current_state\<close>
      \<open>read_register r04_ref current_state = 1 \<or> read_register r04_ref current_state = 0\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>

      \<open>(read_register r03_ref current_state = read_register arg00_ref current_state) 
      \<longleftrightarrow> (read_register r04_ref current_state = 1)\<close>

      \<open>(read_register r03_ref current_state \<noteq> read_register arg00_ref current_state) 
      \<longleftrightarrow> (read_register r04_ref current_state = 0)\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 7\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>if read_register r04_ref current_state = 0 then
      next_state = 
        current_state
        \<lparr>
          register_state := 
            (register_state current_state)
            (
              cycles_register_ref 
                \<mapsto> (read_register cycles_register_ref current_state) 
                  + common_instruction_duration,
              last_instruction_pointer_ref 
                \<mapsto> 7,
              instruction_pointer_ref 
                \<mapsto> 8
            )
        \<rparr>
    else
      next_state = 
        current_state
        \<lparr>
          flag_state := flag_state current_state\<lparr>
            end_jump := 1
          \<rparr>,
          register_state := 
            (register_state current_state)
            (
              last_instruction_pointer_ref 
                \<mapsto> 7,
              instruction_pointer_ref 
                \<mapsto> 13,
              cycles_register_ref 
                \<mapsto> (read_register cycles_register_ref current_state) 
                  + common_instruction_duration
            )
        \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(cases \<open>read_register 4 current_state = 0\<close>)
    apply(simp_all)
    apply(unfold execute_next_instruction_def)
    apply(simp_all)
    apply(unfold fetch_instruction_def)
    apply(simp_all add: read_program_memory_def)
    apply(simp_all add: program_state)
    apply(simp_all add: program_def)
    apply(simp_all add: decode_decomp)
    apply(simp_all add: execute_instruction_simps)
    apply(simp_all add: instruction_decomp_mixed)
    apply(simp_all add: fun_upd_twist)
    apply(simp_all add: state_manipulation_decomp)
    done
  then have h1:
    \<open>read_register last_instruction_pointer_ref next_state = 7\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r04_ref next_state = 0 \<longrightarrow> typical_flags next_state\<close>

    \<open>(read_register arg00_ref next_state = read_register r03_ref next_state) 
    \<longleftrightarrow> (read_register r04_ref next_state = 1)\<close>

    \<open>(read_register r04_ref next_state = 0) 
    \<longleftrightarrow> (read_register instruction_pointer_ref next_state = 8)\<close>

    \<open>(read_register r04_ref next_state = 1) 
    \<longleftrightarrow> (read_register instruction_pointer_ref next_state = 13)\<close>

    \<open>read_register r04_ref next_state = 1 \<longrightarrow> end_jump_flags next_state\<close>

    \<open>(typical_flags next_state \<or> end_jump_flags next_state)\<close>

    \<open>read_register instruction_pointer_ref next_state = 8 
    \<or> (read_register instruction_pointer_ref next_state = 13)\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    using previous_step_invariant program_state
    apply(simp_all add: read_register_decomp read_flag_decomp
          del: One_nat_def add_2_eq_Suc')
    apply(auto)
    done
  show ?thesis
    apply(simp add: step_invariant_def h1)
    apply(safe)
    using h1 
    apply(simp_all)
    done
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step8:
  fixes
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 9 
      \<and> read_register r03_ref state < read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state < read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 8\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r00_ref 
              \<mapsto> read_register r01_ref current_state,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 8,
            instruction_pointer_ref 
              \<mapsto> 9
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 9\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    using previous_step_invariant program_state
    by(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step9:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 10 
      \<and> read_register r03_ref state < read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2)) 
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state < read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 9\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r01_ref 
              \<mapsto> read_register r02_ref current_state,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 9,
            instruction_pointer_ref 
              \<mapsto> 10
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 10\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    using previous_step_invariant program_state
    by(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step10:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 11 
      \<and> read_register r03_ref state < read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2)) 
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 3))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state < read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 10\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r02_ref 
              \<mapsto> (read_register r00_ref current_state) 
                + (read_register r01_ref current_state),
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 10,
            instruction_pointer_ref 
              \<mapsto> 11
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 11\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 3))\<close>
    using previous_step_invariant program_state
    apply(simp_all add: read_register_decomp read_flag_decomp)
    using fib.simps 
    apply(simp)
    apply(simp only: fib_stuff)
    apply(simp)
    done
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step11:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 12 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state))) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1))
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state < read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 3))\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 11\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            r03_ref 
              \<mapsto> (read_register r03_ref current_state) + 1,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 11,
            instruction_pointer_ref 
              \<mapsto> 12
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 12\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    apply(simp_all del: One_nat_def add_2_eq_Suc')
    using previous_step_invariant program_state
    apply(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
    apply(simp_all add: add_with_less_than)
    apply(simp_all only: fib_stuff fib.simps(3))
    apply(simp_all)
    apply(simp add: inc_le)
    done
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step12:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      end_jump_flags state 
      \<and> read_register c01_ref state = 1 
      \<and> read_register instruction_pointer_ref state = 5 
      \<and> read_register last_instruction_pointer_ref state = 12 
      \<and> read_register r03_ref state \<le> read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state))) 
      \<and> read_register r01_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 1)) 
      \<and> read_register r02_ref state 
        = of_nat (fib (unat (read_register r03_ref state) + 2))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register c01_ref current_state = 1\<close>
      \<open>read_register r03_ref current_state \<le> read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>

      \<open>read_register r01_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>

      \<open>read_register r02_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 12\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        flag_state := flag_state current_state\<lparr>end_jump := 1\<rparr>,
        register_state := 
          (register_state current_state)
          (
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 12,
            instruction_pointer_ref 
              \<mapsto> 5
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    apply(simp add: state_manipulation_decomp)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 5\<close>
    \<open>read_register last_instruction_pointer_ref next_state = 12\<close>
    \<open>end_jump_flags next_state\<close>
    \<open>read_register c01_ref next_state = 1\<close>
    \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register r01_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

    \<open>read_register r02_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    using previous_step_invariant program_state
    by(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step13:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> read_register instruction_pointer_ref state = 14 
      \<and> read_register r03_ref state = read_register arg00_ref state 
      \<and> read_register r00_ref state 
        = of_nat (fib (unat (read_register r03_ref state)))\<close>
  assumes
    previous_step_invariant:
      \<open>end_jump_flags current_state\<close>
      \<open>read_register last_instruction_pointer_ref current_state = 7\<close>
      \<open>read_register r03_ref current_state = read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
    and previous_step: \<open>read_register instruction_pointer_ref current_state = 13\<close>
    and program_state: \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        flag_state := (flag_state current_state)\<lparr>end_jump := 0\<rparr>,
        register_state := 
          (register_state current_state)
          (
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 13,
            instruction_pointer_ref
              \<mapsto> 14
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    apply(simp add: state_manipulation_decomp)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 14\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register r03_ref next_state = read_register arg00_ref next_state\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
    using previous_step_invariant program_state
    by(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step14:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      typical_flags state 
      \<and> get_end_return state = 0 
      \<and> get_end_call state = 0 
      \<and> get_end_jump state = 0 
      \<and> get_error state = 0 
      \<and> read_register instruction_pointer_ref state = 15 
      \<and> read_register r03_ref state = read_register arg00_ref state 
      \<and> read_register ret00_ref state 
        = of_nat (fib (unat (read_register r03_ref state)))\<close>
  assumes
    previous_step_invariant:
      \<open>typical_flags current_state\<close>
      \<open>read_register r03_ref current_state = read_register arg00_ref current_state\<close>

      \<open>read_register r00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
    and previous_step:  \<open>read_register instruction_pointer_ref current_state = 14\<close>
    and program_state:  \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        register_state := 
          (register_state current_state)
          (
            ret00_ref 
              \<mapsto> read_register r00_ref current_state,
            cycles_register_ref 
              \<mapsto> (read_register cycles_register_ref current_state) 
                + common_instruction_duration,
            last_instruction_pointer_ref 
              \<mapsto> 14,
            instruction_pointer_ref 
              \<mapsto> 15
          )
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(simp)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(simp add: instruction_decomp_mixed)
    apply(simp add: fun_upd_twist)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 15\<close>
    \<open>typical_flags next_state\<close>
    \<open>read_register r03_ref next_state = read_register arg00_ref next_state\<close>

    \<open>read_register r00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

    \<open>read_register ret00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
    using previous_step_invariant program_state
    by(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

lemma (in Ironbark_world) fib_equivalence_invariant_step15:
  fixes 
    current_state :: sequential_state
  defines
    \<open>next_state \<equiv> execute_next_instruction current_state\<close>
  defines
    \<open>step_invariant \<equiv> \<lambda> state .
      halt_flags state 
      \<and> get_end_return state = 0 
      \<and> get_end_call state = 0 
      \<and> get_end_jump state = 0 
      \<and> get_error state = 0 
      \<and> read_register instruction_pointer_ref state = 15 
      \<and> read_register r03_ref state = read_register arg00_ref state 
      \<and> read_register ret00_ref state 
        = of_nat (fib (unat (read_register r03_ref state)))\<close>
  assumes
    previous_step_invariant:
      \<open>get_end_return current_state = 0\<close>
      \<open>get_end_call current_state = 0\<close>
      \<open>get_end_jump current_state = 0\<close>
      \<open>get_error current_state = 0\<close>
      \<open>read_register r03_ref current_state = read_register arg00_ref current_state\<close>

      \<open>read_register ret00_ref current_state 
      = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
    and previous_step: \<open>read_register instruction_pointer_ref current_state = 15\<close>
    and program_state: \<open>program_memory current_state = program\<close>
  shows
    \<open>step_invariant next_state\<close>
proof -
  have
    \<open>next_state = 
      current_state
      \<lparr>
        flag_state := flag_state current_state\<lparr>halt := 1\<rparr>
      \<rparr>\<close>
    unfolding next_state_def
    using previous_step_invariant previous_step
    apply(simp)
    apply(unfold execute_next_instruction_def)
    apply(unfold fetch_instruction_def)
    apply(simp add: read_program_memory_def)
    apply(simp add: program_state)
    apply(simp add: program_def)
    apply(simp add: decode_decomp)
    apply(simp add: execute_instruction_simps)
    apply(cases \<open>get_halt current_state = 1\<close>)
    apply(simp_all add: instruction_decomp_manipulation)
    apply(simp_all add: instruction_impl_defs)
    apply(simp_all add: state_manipulation_decomp)
    apply(simp_all add: flag_normalisation)
    done
  then have
    \<open>read_register instruction_pointer_ref next_state = 15\<close>
    \<open>halt_flags next_state\<close>
    \<open>read_register r03_ref next_state = read_register arg00_ref next_state\<close>

    \<open>read_register ret00_ref next_state 
    = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
    using previous_step_invariant program_state previous_step
    by(simp_all add: read_register_decomp read_flag_decomp
            del: One_nat_def add_2_eq_Suc')
  then show ?thesis
    by(simp add: step_invariant_def)
qed

text \<open>Finally, we combine all of the proofs for each step to show that the program is 
correct. The structure of this proof is to start with some preliminary transformation, 
and then show the invariant conditions are met at all steps of the program by 
application of the previous lemmas.\<close>

lemma (in Ironbark_world) fib_equivalence_invariant:
  shows
    \<open>invariant 
      (execute_multiple_instructions 
        (initial_state\<lparr>program_memory := program\<rparr>) 
        num_instructions)\<close>
proof -
  have 
    \<open>read_register instruction_pointer_ref (initial_state\<lparr>program_memory := program\<rparr>) 
    = 0\<close>
    by(simp add: program_def initial_state_def read_register_decomp)
  moreover have 
    \<open>0 \<in> dom program\<close>
    by(simp add: program_def)
  ultimately show ?thesis
    apply(subst inv_satI)
    apply(simp_all)

  proof -
    assume 
      \<open>read_register instruction_pointer_ref (initial_state\<lparr>program_memory := program\<rparr>) 
      = 0\<close>
    then show 
      \<open>invariant (initial_state\<lparr>program_memory := program\<rparr>)\<close>
      apply(simp add: invariant_def)
      apply(simp add: initial_state_simps)
      done

    fix state :: \<open>sequential_state\<close>
    assume 
      \<open>read_register instruction_pointer_ref state \<in> dom program\<close>
      \<open>invariant state\<close>
      \<open>program_memory state = program\<close>
    then show
      \<open>invariant (execute_next_instruction state)\<close>
      \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
      \<in> dom program\<close>
      apply(all \<open>subst (asm) program_def\<close>)
      apply(simp)
      apply(elim disjE)

      prefer 17

      apply(simp)
      apply(elim disjE)

    proof -
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 0\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step0)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 1\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step1)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 2\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step2)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 3\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step3)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 4\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step4)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 5\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step5)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 6\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        using fib_equivalence_invariant_step6
        apply(simp_all add: invariant_def)
        apply(simp_all add: fib_equivalence_invariant_step6)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 7\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        using fib_equivalence_invariant_step7[of \<open>state\<close>]
        apply(simp_all add: invariant_def)
        apply(elim conjE)
        apply(simp)
        apply(elim conjE disjE)
        apply(simp_all)
        apply(elim conjE)
        apply(simp)
        apply(elim conjE disjE)
        apply(simp_all add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 8\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step8)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 9\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step9)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 10\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def fib_equivalence_invariant_step10)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 11\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def)
        apply(simp_all add: fib_equivalence_invariant_step11)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 12\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def)
        apply(simp_all add: fib_equivalence_invariant_step12)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 13\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def)
        apply(simp_all add: fib_equivalence_invariant_step13)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 14\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def)
        apply(simp_all add: fib_equivalence_invariant_step14)
        apply(simp add: program_def)
        done
  
    next
  
      fix state :: sequential_state
      assume 
        \<open>invariant state\<close>
        \<open>program_memory state = program\<close>
        \<open>read_register instruction_pointer_ref state = 15\<close>
      then show 
        \<open>invariant (execute_next_instruction state)\<close>

        \<open>read_register instruction_pointer_ref (execute_next_instruction state) 
        \<in> dom program\<close>
        apply(simp_all add: invariant_def)
        apply(simp_all add: fib_equivalence_invariant_step15)
        apply(simp add: program_def)
        done
    qed
  qed
qed
end