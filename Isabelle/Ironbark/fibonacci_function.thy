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

subsection \<open>Correctness of Fibonacci as a Function\<close>

theory fibonacci_function

imports
  "Ironbark_execution.execution_top"

begin

text \<open>This file contains a proof of correctness of a function which calculates 
Fibonacci numbers. Specifically, this proof is done on a function which can be freely 
relocated, unlike the versions seen in the fibonacci\_invariant theory or 
fibonacci\_invariant\_piecemeal theory.\<close>

text \<open>We start by defining the Fibonacci function from a pure mathematical point of 
view, which we will later show is equivalent to the return value of our function 
(modulo $2^{64}$).\<close>

function 
  fib :: \<open>nat \<Rightarrow> nat\<close>
  where
  \<open>fib 0 = 1\<close>
| \<open>fib 1 = 1\<close>
| \<open>fib (n+2) = fib n + fib (n+1)\<close>
  apply atomize_elim
  apply arith
  apply auto
  done
termination by lexicographic_order

text \<open>Next, we derive a variety of rewriting. This is largely done to remove Suc from 
the proof state, as we prefer to operate on +, instead of Suc.\<close>

lemma fib_stuff:
  \<open>fib (n+3) = fib (n+1) + fib (n+2)\<close>
  \<open>fib (Suc (Suc n)) = fib n + fib (n+1)\<close>
  \<open>fib (Suc (Suc (Suc n))) = fib (n+1) + fib (n+2)\<close>
  \<open>fib (Suc 0) = 1\<close>
  \<open>fib (Suc (Suc n)) = fib (n+2)\<close>
  \<open>fib (Suc n) = fib (n+1)\<close>
  \<open>fib (Suc (n+1)) = fib (n+2)\<close>
  \<open>fib (Suc (n+2)) = fib (n+3)\<close>
  \<open>fib (Suc (Suc 0)) = 2\<close>
  \<open>fib (n+0) = fib n\<close>
  \<open>fib (0+n) = fib n\<close>
  \<open>fib (Suc (Suc (Suc n))) = fib (n+3)\<close>
  using fib.simps 
  by(simp_all add: numeral_Bit1(1))

text \<open>We found it is sometimes useful to be able to lookup the answers for early 
Fibonacci numbers, so we collect a few of the early answers for convenience in the 
following lemma.\<close>

lemma fib_answers:
  \<open>fib 0 = 1\<close>
  \<open>fib 1 = 1\<close>
  \<open>fib (Suc 0) = 1\<close>
  \<open>fib 2 = 2\<close>
  \<open>fib (Suc 1) = 2\<close>
  \<open>fib (Suc (Suc 0)) = 2\<close>
  \<open>fib 3 = 3\<close>
  \<open>fib 4 = 5\<close>
  using fib.simps 
  by(simp_all add: numeral_3_eq_3 numeral_Bit0)

text \<open>In order to support relocation of the function, we create a locale where we 
assume the branches and end branches have been appropriately setup for the location. 
The proof is done in the context of this locale.\<close>

locale fib_routine = 
  fixes 
    n :: \<open>64 word\<close>
    and hack_v1 hack_v2 hack_v3 hack_v4 :: \<open>96 word\<close>
  assumes
    decode_hacks:
      \<open>decode_instruction(hack_v1) = (0x1B, 0x04, 0x00, 0x00, n + 0xe)\<close>
      \<open>decode_instruction(hack_v2) = (0x1A, 0x00, 0x00, 0x00, n + 0x6)\<close>
      \<open>decode_instruction(hack_v3) = (0x18, 0x00, 0x00, 0x00, n + 13)\<close>
      \<open>decode_instruction(hack_v4) = (0x18, 0x00, 0x00, 0x00, n + 8)\<close>
begin
end

sublocale fib_routine \<subseteq> Ironbark_world
  done

text \<open>We now define the program, which we will show correctly implements the Fibonacci 
function.\<close>

definition (in fib_routine)
  program :: \<open>(64 word, 96 word) map\<close>
  where
    \<open>program \<equiv> 
      Map.empty 
      (
        n    \<mapsto> 0x1C0000000000000000000000,  \<comment>\<open>end\_call\<close>
        n+1  \<mapsto> 0x022100000000000000000001,  \<comment>\<open>c01 = 0x1\<close>
        n+2  \<mapsto> 0x020300000000000000000000,  \<comment>\<open>r03 = 0x0\<close>
        n+3  \<mapsto> 0x020000000000000000000001,  \<comment>\<open>r00 = 0x1\<close>
        n+4  \<mapsto> 0x020100000000000000000001,  \<comment>\<open>r01 = 0x1\<close>
        n+5  \<mapsto> 0x020200000000000000000002,  \<comment>\<open>r02 = 0x2\<close>
        n+6  \<mapsto> hack_v3,                     \<comment>\<open>end\_jump (n + 13)\<close>
        n+7  \<mapsto> 0x150403300000000000000000,  \<comment>\<open>r04 = r03 == arg00\<close>
        n+8  \<mapsto> hack_v1,                     \<comment>\<open>if (r04) jump (n + 14)\<close>
        n+9  \<mapsto> 0x090001000000000000000000,  \<comment>\<open>r00 = r01\<close>
        n+10 \<mapsto> 0x090102000000000000000000,  \<comment>\<open>r01 = r02\<close>
        n+11 \<mapsto> 0x0A0200010000000000000000,  \<comment>\<open>r02 = r00 + r01\<close>
        n+12 \<mapsto> 0x0A0303210000000000000000,  \<comment>\<open>r03 = r03 + c01\<close>
        n+13 \<mapsto> hack_v2,                     \<comment>\<open>jump (n + 6)\<close>
        n+14 \<mapsto> hack_v4,                     \<comment>\<open>end\_jump (n + 8)\<close>
        n+15 \<mapsto> 0x094000000000000000000000,  \<comment>\<open>ret00 = r00\<close>
        n+16 \<mapsto> 0x1F0000000000000000000000   \<comment>\<open>return\<close>
      )\<close>

text \<open>We also define what it means for our program to be `correct'. Because we use an 
inductive process with this as our invariant, the approach we have taken is to state 
what we expect to be true at every step of the program. We've annotated this with the 
assembly being executed at each step, and what we really mean by correctness is what 
we show in the return step (at the end of the definition), and the rest of these are 
intermediate results useful for the inductive process.\<close>

definition (in fib_routine)
  check_trace :: \<open>(sequential_state list) \<Rightarrow> bool\<close>
  where
    \<open>check_trace trace \<equiv>
      trace \<noteq> [] \<and>
      ((read_register instruction_pointer_ref (hd trace) = n) \<longrightarrow>
      (list_all 
        (\<lambda> step .
          (read_register instruction_pointer_ref step \<in> dom program)
  
          \<comment>\<open>end\_call\<close>
          \<and> (read_register instruction_pointer_ref step = n 
              \<longrightarrow> end_call_flags step)
  
          \<comment>\<open>c01 = 0x1\<close>
          \<and> (read_register instruction_pointer_ref step = n+1 
              \<longrightarrow> typical_flags step)
  
          \<comment>\<open>r03 = 0    //counter\<close>
          \<and> (read_register instruction_pointer_ref step = n+2 \<longrightarrow>
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
          ))
  
          \<comment>\<open>r00 = 1    //fib(counter)\<close>
          \<and> (read_register instruction_pointer_ref step = n+3 \<longrightarrow>
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step = 0
            \<and> read_register r03_ref step \<le> read_register arg00_ref step
          ))
  
          \<comment>\<open>r01 = 1    //fib(counter+1)\<close>
          \<and> (read_register instruction_pointer_ref step = n+4 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step = 0
            \<and> read_register r03_ref step \<le> read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step)))
          ))
  
          \<comment>\<open>r02 = 2    //fib(counter+2))\<close>
          \<and> (read_register instruction_pointer_ref step = n+5 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step = 0
            \<and> read_register r03_ref step \<le> read_register arg00_ref step
            \<and> read_register r00_ref step
              = of_nat (fib (unat (read_register r03_ref step)))
            \<and> read_register r01_ref step
              = of_nat (fib (unat (read_register r03_ref step) + 1))
          ))
  
          \<comment>\<open>end\_jump\<close>
          \<and> (read_register instruction_pointer_ref step = n+6 \<longrightarrow> 
          (
            (typical_flags step \<or> end_jump_flags step)
          \<and> (typical_flags step 
            \<longrightarrow> (read_register last_instruction_pointer_ref step = n+5))
          \<and> (end_jump_flags step 
            \<longrightarrow> (read_register last_instruction_pointer_ref step = n+13))
          \<and> read_register c01_ref step = 1
          \<and> read_register r03_ref step \<le> read_register arg00_ref step
          \<and> read_register r00_ref step 
            = of_nat (fib (unat (read_register r03_ref step)))
          \<and> read_register r01_ref step 
            = of_nat (fib (unat (read_register r03_ref step) + 1))
          \<and> read_register r02_ref step 
            = of_nat (fib (unat (read_register r03_ref step) + 2))
          ))
  
          \<comment>\<open>r04 = r03 == arg00\<close>
          \<and> (read_register instruction_pointer_ref step = n+7 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step \<le> read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step)))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
          ))
  
          \<comment>\<open>if (r04) jump finish   //if (counter == n) {finish}\<close>
          \<and> (read_register instruction_pointer_ref step = n+8 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step \<le> read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step)))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
            \<and> (read_register r03_ref step = read_register arg00_ref step
              \<longrightarrow> (read_register r04_ref step = 1))
            \<and> (read_register r03_ref step \<noteq> read_register arg00_ref step
              \<longrightarrow> (read_register r04_ref step = 0))
            \<and> (read_register r04_ref step = 1 \<or> read_register r04_ref step = 0)
          ))
  
          \<comment>\<open>r00 = r01   //fib(counter)   <- fib(counter+1)\<close>
          \<and> (read_register instruction_pointer_ref step = n+9 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step < read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step)))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
          ))
  
          \<comment>\<open>r01 = r02   //fib(counter+1) <- fib(counter+2)\<close>
          \<and> (read_register instruction_pointer_ref step = n+10 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step < read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
          ))
  
          \<comment>\<open>r02 = r00 + r01  //fib(counter+2) <- fib(counter+3)\<close>
          \<and> (read_register instruction_pointer_ref step = n+11 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step < read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
          ))
  
          \<comment>\<open>r03 = r03 + c01  //counter++\<close>
          \<and> (read_register instruction_pointer_ref step = n+12 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step < read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 3))
          ))
  
          \<comment>\<open>jump main\_loop\<close>
          \<and> (read_register instruction_pointer_ref step = n+13 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register c01_ref step = 1
            \<and> read_register r03_ref step \<le> read_register arg00_ref step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register r03_ref step)))
            \<and> read_register r01_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 1))
            \<and> read_register r02_ref step 
              = of_nat (fib (unat (read_register r03_ref step) + 2))
          ))
  
          \<comment>\<open>end\_jump\<close>
          \<and> (read_register instruction_pointer_ref step = n+14 \<longrightarrow> 
          (
            end_jump_flags step
            \<and> read_register last_instruction_pointer_ref step = n+8
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register arg00_ref step)))
          ))
  
          \<comment>\<open>ret00 = r00\<close>
          \<and> (read_register instruction_pointer_ref step = n+15 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register r00_ref step 
              = of_nat (fib (unat (read_register arg00_ref step)))
          ))
  
          \<comment>\<open>return\<close>
          \<and> (read_register instruction_pointer_ref step = n+16 \<longrightarrow> 
          (
            typical_flags step
            \<and> read_register ret00_ref step 
              = of_nat (fib (unat (read_register arg00_ref step)))
          ))
        ) trace
      ))\<close>

text \<open>Finally, we present a proof that our program is correct. We note that the body 
of the proof is very large, with many subproofs. The structure of this proof is to 
start with some preliminary transformation, then decompose the check\_trace into the 
goals for each instruction (see have goals named check\_trace\_decomposition\_n*), 
then establish what instruction will be executed in each step (see have goal named 
current\_instruction), before showing that the properties claimed in check\_trace will 
be held after executing the next instruction (see have goals named n*\_h5). After 
showing all those subgoals, we combine them to show the original goal.\<close>

lemma (in fib_routine) check_fib:
  assumes
    function_start: \<open>read_register instruction_pointer_ref starting_state = n\<close>
    and starting_flags: \<open>end_call_flags starting_state\<close>
    and program_loaded: \<open>program_memory starting_state = program\<close>
  shows
    \<open>check_trace (finish_function_trace [starting_state] x)\<close>
proof (induct \<open>x\<close>)
  case 0
  then show ?case 
    apply(simp)
    apply(simp add: check_trace_def)
    apply(simp add: program_def starting_flags)
    done
next
  case (Suc x)
  then show ?case 
    apply(simp add: Let_def)
    apply(intro impI)

  proof -
      fix x :: nat
      define current_state 
        where 
          \<open>current_state = last (finish_function_trace [starting_state] x)\<close>
      define next_state 
        where 
          \<open>next_state = execute_next_instruction current_state\<close>
    assume a1: \<open>check_trace (finish_function_trace [starting_state] x)\<close>
    assume a2: \<open>get_opcode (fetch_instruction current_state) \<noteq> 31\<close>
  
    have trace_program_memory3: 
      \<open>\<forall> addr . 
        read_program_memory addr current_state 
        = read_program_memory addr starting_state\<close>
      by(simp add: current_state_def trace_read_program_memory)
  
    have trace_program_memory4: 
      \<open>program_memory current_state = program_memory starting_state\<close>
      by(simp add: current_state_def trace_program_memory)
  
    have state_in_trace:
      \<open>current_state \<in> set (finish_function_trace [starting_state] x)\<close>
      by(simp add: current_state_def trace_rules)
  
    have check_trace_decomposition_n0:
      \<open>read_register instruction_pointer_ref current_state = n 
      \<Longrightarrow> end_call_flags current_state\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n1:
      \<open>read_register instruction_pointer_ref current_state = n + 1 
      \<Longrightarrow> typical_flags current_state\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n2:
      \<open>read_register instruction_pointer_ref current_state = n + 2 
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 2 
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n3:
      \<open>read_register instruction_pointer_ref current_state = n + 3
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 3
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 3
      \<Longrightarrow> read_register r03_ref current_state = 0\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 3
      \<Longrightarrow> read_register r03_ref current_state 
        \<le> read_register arg00_ref current_state\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n4:
      \<open>read_register instruction_pointer_ref current_state = n + 4
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 4
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 4
      \<Longrightarrow> read_register r03_ref current_state = 0\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 4
      \<Longrightarrow> read_register r03_ref current_state 
        \<le> read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 4
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n5:
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> read_register r03_ref current_state = 0\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> read_register r03_ref current_state \<le> read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n6:
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> (typical_flags current_state \<or> end_jump_flags current_state)\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> (typical_flags current_state 
        \<longrightarrow> read_register last_instruction_pointer_ref current_state = n + 5)\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> (end_jump_flags current_state 
        \<longrightarrow> read_register last_instruction_pointer_ref current_state = n + 13)\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> read_register r03_ref current_state 
        \<le> read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n7:
      \<open>read_register instruction_pointer_ref current_state = n + 7
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 7
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 7
      \<Longrightarrow> read_register r03_ref current_state 
        \<le> read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 7
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 7
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 7
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n8:
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> read_register r03_ref current_state 
        \<le> read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8 
      \<Longrightarrow> (read_register r03_ref current_state = read_register arg00_ref current_state)
        \<longrightarrow> (read_register r04_ref current_state = 1)\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8 
      \<Longrightarrow> (read_register r03_ref current_state \<noteq> read_register arg00_ref current_state) 
        \<longrightarrow> (read_register r04_ref current_state = 0)\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8 
      \<Longrightarrow> (read_register r04_ref current_state = 1 
        \<or> read_register r04_ref current_state = 0)\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n9:
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> read_register r03_ref current_state 
        < read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n10:
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> read_register r03_ref current_state 
        < read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n11:
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> read_register r03_ref current_state 
        < read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n12:
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> read_register r03_ref current_state 
        < read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 3))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n13:
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> read_register c01_ref current_state = 1\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> read_register r03_ref current_state 
        \<le> read_register arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state)))\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> read_register r01_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 1))\<close>
 
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> read_register r02_ref current_state 
        = of_nat (fib (unat (read_register r03_ref current_state) + 2))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n14:
      \<open>read_register instruction_pointer_ref current_state = n + 14
      \<Longrightarrow> end_jump_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 14
      \<Longrightarrow> read_register last_instruction_pointer_ref current_state = n+8\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 14
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register arg00_ref current_state)))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n15:
      \<open>read_register instruction_pointer_ref current_state = n + 15
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 15
      \<Longrightarrow> read_register r00_ref current_state 
        = of_nat (fib (unat (read_register arg00_ref current_state)))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have check_trace_decomposition_n16:
      \<open>read_register instruction_pointer_ref current_state = n + 16
      \<Longrightarrow> typical_flags current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 16
      \<Longrightarrow> read_register ret00_ref current_state 
        = of_nat (fib (unat (read_register arg00_ref current_state)))\<close>
      using a1 trace_rules function_start
      by(simp_all add: check_trace_def list_all_def Ball_def state_in_trace)
  
    have current_instruction:
      \<open>read_register instruction_pointer_ref current_state = n
      \<Longrightarrow> next_state = END_CALL current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 1
      \<Longrightarrow> next_state = LOAD_IMMEDIATE c01_ref 1 current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 2
      \<Longrightarrow> next_state = LOAD_IMMEDIATE r03_ref 0 current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 3
      \<Longrightarrow> next_state = LOAD_IMMEDIATE r00_ref 1 current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 4
      \<Longrightarrow> next_state = LOAD_IMMEDIATE r01_ref 1 current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 5
      \<Longrightarrow> next_state = LOAD_IMMEDIATE r02_ref 2 current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 6
      \<Longrightarrow> next_state = END_JUMP (n+13) current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 7 
      \<Longrightarrow> next_state = EQUALS r04_ref r03_ref arg00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 8
      \<Longrightarrow> next_state = CONDITIONAL_JUMP r04_ref (n+14) current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 9
      \<Longrightarrow> next_state = COPY r00_ref r01_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 10
      \<Longrightarrow> next_state = COPY r01_ref r02_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 11
      \<Longrightarrow> next_state = ADD r02_ref r00_ref r01_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 12
      \<Longrightarrow> next_state = ADD r03_ref r03_ref c01_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 13
      \<Longrightarrow> next_state = JUMP (n+6) current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 14
      \<Longrightarrow> next_state = END_JUMP (n+8) current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 15
      \<Longrightarrow> next_state = COPY ret00_ref r00_ref current_state\<close>
  
      \<open>read_register instruction_pointer_ref current_state = n + 16
      \<Longrightarrow> next_state = RETURN current_state\<close>
      using 
        check_trace_decomposition_n0(1) 
        check_trace_decomposition_n1(1) 
        check_trace_decomposition_n2(1)
        check_trace_decomposition_n3(1) 
        check_trace_decomposition_n4(1) 
        check_trace_decomposition_n5(1)
        check_trace_decomposition_n6(1) 
        check_trace_decomposition_n7(1) 
        check_trace_decomposition_n8(1)
        check_trace_decomposition_n9(1) 
        check_trace_decomposition_n10(1) 
        check_trace_decomposition_n11(1)
        check_trace_decomposition_n12(1) 
        check_trace_decomposition_n13(1) 
        check_trace_decomposition_n14(1)
        check_trace_decomposition_n15(1) 
        check_trace_decomposition_n16(1)
      apply(simp_all add: next_state_def)
      unfolding execute_next_instruction_def
      apply(simp_all)
      unfolding fetch_instruction_def
      apply(simp_all add: trace_program_memory3)
      apply(simp_all add: read_program_memory_def program_loaded program_def)
      apply(simp_all add: decode_hacks)
      apply(simp_all add: decode_decomp)
      apply(simp_all add: execute_instruction_simps)
      apply(elim disjE)
      apply(simp_all)
      done
  
    have n0:
      \<open>read_register instruction_pointer_ref next_state = n + 1\<close>
      \<open>typical_flags next_state\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n\<close>
    proof -
      have current_instruction: 
        \<open>read_register instruction_pointer_ref current_state = n 
        \<Longrightarrow> next_state = END_CALL current_state\<close>
        using check_trace_decomposition_n0(1)
        apply(simp add: next_state_def)
        apply(simp add: execute_next_instruction_def)
        apply(simp add: fetch_instruction_def)
        apply(simp_all add: trace_program_memory3)
        apply(simp_all add: read_program_memory_def program_loaded program_def)
        apply(simp_all add: decode_decomp)
        apply(simp_all add: execute_instruction_simps)
        done
      show 
        \<open>read_register instruction_pointer_ref next_state = n + 1\<close>
        \<open>typical_flags next_state\<close>
        using a0 current_instruction check_trace_decomposition_n0
        by(simp_all add: END_CALL_simps)
    qed
  
    have n1:
      \<open>read_register instruction_pointer_ref next_state = n + 2\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 1\<close>
      using 
        a0 
        current_instruction(2) 
        check_trace_decomposition_n1 
        check_write_permission_set
      by(simp_all add: LOAD_IMMEDIATE_simps)
  
    have n2:
      \<open>read_register instruction_pointer_ref next_state = n + 3\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state = 0\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 2\<close>
      using 
        a0 
        current_instruction(3) 
        check_trace_decomposition_n2 
        check_write_permission_set
      by(simp_all add: LOAD_IMMEDIATE_simps)
  
    have n3:
      \<open>read_register instruction_pointer_ref next_state = n + 4\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state = 0\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>

      \<open>read_register r00_ref next_state
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 3\<close>
      using 
        a0 
        current_instruction(4) 
        check_trace_decomposition_n3 
        check_write_permission_set
      by(simp_all add: LOAD_IMMEDIATE_simps)
  
    have n4:
      \<open>read_register instruction_pointer_ref next_state = n + 5\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state = 0\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 4\<close>
      using 
        a0 
        current_instruction(5) 
        check_trace_decomposition_n4 
        check_write_permission_set
      by(simp_all add: LOAD_IMMEDIATE_simps fib_answers)
  
    have n5:
      \<open>read_register instruction_pointer_ref next_state = n + 6\<close>
      \<open>typical_flags next_state\<close>
      \<open>get_end_jump next_state = 0\<close>
      \<open>read_register last_instruction_pointer_ref next_state = n + 5\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state = 0\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 5\<close>
      using a0 current_instruction(6) check_trace_decomposition_n5 check_write_permission_set
      by(simp_all add: LOAD_IMMEDIATE_simps fib_answers)
  
    have n6:
      \<open>read_register instruction_pointer_ref next_state = n + 7\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 6\<close>
    proof (all \<open>cases \<open>typical_flags current_state\<close>\<close>)
      assume \<open>typical_flags current_state\<close>
      then show     
        \<open>read_register instruction_pointer_ref next_state = n + 7\<close>
        \<open>typical_flags next_state\<close>
        \<open>read_register c01_ref next_state = 1\<close>
        \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
        using a0 current_instruction(7) check_trace_decomposition_n6
        by(simp_all add: END_JUMP_simps)
    next
      assume \<open>\<not> typical_flags current_state\<close>
      then have \<open>end_jump_flags current_state\<close>
        using a0 check_trace_decomposition_n6(1)
        by(linarith)
      then show
        \<open>read_register instruction_pointer_ref next_state = n + 7\<close>
        \<open>typical_flags next_state\<close>
        \<open>read_register c01_ref next_state = 1\<close>
        \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
        using a0 current_instruction(7) check_trace_decomposition_n6
        by(simp_all add: END_JUMP_simps)
    qed
  
    have n7:
      \<open>read_register instruction_pointer_ref next_state = n + 8\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
  
      \<open>(read_register r03_ref next_state = read_register arg00_ref next_state)
      \<longrightarrow> (read_register r04_ref next_state = 1)\<close>
  
      \<open>(read_register r03_ref next_state \<noteq> read_register arg00_ref next_state)
      \<longrightarrow> (read_register r04_ref next_state = 0)\<close>
  
      \<open>read_register r04_ref next_state = 1 \<or> read_register r04_ref next_state = 0\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 7\<close>
      using 
        a0 
        current_instruction(8) 
        check_trace_decomposition_n7 
        check_write_permission_set
        check_read_permission_set
      by(simp_all add: EQUALS_simps)
  
      have n8:
        \<open>read_register r04_ref current_state = 0 
        \<longrightarrow> (read_register instruction_pointer_ref next_state = n + 9)\<close>
  
        \<open>read_register r04_ref current_state = 1 
        \<longrightarrow> (read_register instruction_pointer_ref next_state = n + 14)\<close>
  
        \<open>read_register r04_ref current_state = 0
        \<longrightarrow> typical_flags next_state\<close>
  
        \<open>read_register r04_ref current_state = 1
        \<longrightarrow> end_jump_flags next_state\<close>
  
        \<open>read_register r04_ref current_state = 1
        \<longrightarrow> (read_register last_instruction_pointer_ref next_state = n + 8)\<close>
  
        \<open>read_register c01_ref next_state = 1\<close>
  
        \<open>read_register r04_ref current_state = 0
        \<longrightarrow> (read_register r03_ref next_state < read_register arg00_ref next_state)\<close>
  
        \<open>read_register r04_ref current_state = 1
        \<longrightarrow> (read_register r03_ref next_state = read_register arg00_ref next_state)\<close>
  
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 8\<close>
      proof (all \<open>cases \<open>read_register r04_ref current_state = 0\<close>\<close>)
        have h1: 
          \<open>check_read_permission r04_ref\<close>
          by(simp add: check_read_permission_set)
        {
          assume \<open>read_register 4 current_state = 0\<close>
          then show 
            \<open>(read_register r04_ref current_state = 0)
            \<longrightarrow> (read_register instruction_pointer_ref next_state = n + 9)\<close>
  
            \<open>(read_register r04_ref current_state = 1)
            \<longrightarrow> (read_register instruction_pointer_ref next_state = n + 14)\<close>
  
            \<open>(read_register r04_ref current_state = 0)
            \<longrightarrow> typical_flags next_state\<close>
  
            \<open>(read_register r04_ref current_state = 1)
            \<longrightarrow> end_jump_flags next_state\<close>
  
            \<open>(read_register r04_ref current_state = 1)
            \<longrightarrow> (read_register last_instruction_pointer_ref next_state = n + 8)\<close>
  
            \<open>read_register c01_ref next_state = 1\<close>
  
            \<open>(read_register r04_ref current_state = 0)
            \<longrightarrow> (read_register r03_ref next_state < read_register arg00_ref next_state)\<close>
  
            \<open>read_register r04_ref current_state = 1
            \<longrightarrow> (read_register r03_ref next_state = read_register arg00_ref next_state)\<close>
  
            \<open>read_register r00_ref next_state 
            = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
            \<open>read_register r01_ref next_state 
            = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
            \<open>read_register r02_ref next_state 
            = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
            using a0 h1 current_instruction(9) check_trace_decomposition_n8
            by(simp_all add: CONDITIONAL_JUMP_simps)
        next
          assume \<open>read_register 4 current_state \<noteq> 0\<close>
          then show 
            \<open>read_register r04_ref current_state = 0
            \<longrightarrow> (read_register instruction_pointer_ref next_state = n + 9)\<close>
  
            \<open>read_register r04_ref current_state = 1
            \<longrightarrow> (read_register instruction_pointer_ref next_state = n + 14)\<close>
  
            \<open>read_register r04_ref current_state = 0
            \<longrightarrow> typical_flags next_state\<close>
  
            \<open>read_register r04_ref current_state = 1
            \<longrightarrow> end_jump_flags next_state\<close>
  
            \<open>read_register r04_ref current_state = 1
            \<longrightarrow> (read_register last_instruction_pointer_ref next_state = n + 8)\<close>
  
            \<open>read_register c01_ref next_state = 1\<close>
  
            \<open>read_register r04_ref current_state = 0
            \<longrightarrow> (read_register r03_ref next_state < read_register arg00_ref next_state)\<close>
  
            \<open>read_register r04_ref current_state = 1
            \<longrightarrow> (read_register r03_ref next_state = read_register arg00_ref next_state)\<close>
  
            \<open>read_register r00_ref next_state 
            = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
            \<open>read_register r01_ref next_state 
            = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
            \<open>read_register r02_ref next_state 
            = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
            using a0 h1 current_instruction(9) check_trace_decomposition_n8
            by(simp_all add: CONDITIONAL_JUMP_simps)
        }
      qed
  
    have n9:
      \<open>read_register instruction_pointer_ref next_state = n + 10\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 9\<close>
    proof -
      have
        \<open>check_write_permission r00_ref\<close>
        \<open>check_read_permission r01_ref\<close>
        by(simp_all add: permission_simps)
      then show 
        \<open>read_register instruction_pointer_ref next_state = n + 10\<close>
        \<open>typical_flags next_state\<close>
        \<open>read_register c01_ref next_state = 1\<close>
        \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>
    
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
    
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
    
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
        using a0 current_instruction(10) check_trace_decomposition_n9
        by(simp_all add: COPY_simps)
    qed
  
    have n10:
      \<open>read_register instruction_pointer_ref next_state = n + 11\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 10\<close>
     proof -
      have
        \<open>check_write_permission r01_ref\<close>
        \<open>check_read_permission r02_ref\<close>
        by(simp_all add: permission_simps)
      then show
        \<open>read_register instruction_pointer_ref next_state = n + 11\<close>
        \<open>typical_flags next_state\<close>
        \<open>read_register c01_ref next_state = 1\<close>
        \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>
    
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
    
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
        using a0 current_instruction(11) check_trace_decomposition_n10
        by(simp_all add: COPY_simps)
    qed
  
    have n11:
      \<open>read_register instruction_pointer_ref next_state = n + 12\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 3))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 11\<close>
    proof -
      have
        \<open>check_write_permission r02_ref\<close>
        \<open>check_read_permission r00_ref\<close>
        \<open>check_read_permission r01_ref\<close>
        by(simp_all add: permission_simps)
      then show 
        \<open>read_register instruction_pointer_ref next_state = n + 12\<close>
        \<open>typical_flags next_state\<close>
        \<open>read_register c01_ref next_state = 1\<close>
        \<open>read_register r03_ref next_state < read_register arg00_ref next_state\<close>
    
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
    
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
    
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 3))\<close>
        using a0 current_instruction(12) check_trace_decomposition_n11
        by(simp_all add: ADD_simps fib_stuff(1))
    qed
  
    have n12:
      \<open>read_register instruction_pointer_ref next_state = n + 13\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
  
      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
  
      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 12\<close>
    proof -
      have
        \<open>check_write_permission r03_ref\<close>
        \<open>check_read_permission r03_ref\<close>
        \<open>check_read_permission c01_ref\<close>
        by(simp_all add: permission_simps)
      then show 
        \<open>read_register instruction_pointer_ref next_state = n + 13\<close>
        \<open>typical_flags next_state\<close>
        \<open>read_register c01_ref next_state = 1\<close>
        \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
    
        \<open>read_register r00_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state)))\<close>
    
        \<open>read_register r01_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>
    
        \<open>read_register r02_ref next_state 
        = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
        using a0 current_instruction(13) check_trace_decomposition_n12
        by(simp_all add: ADD_simps fib_stuff(12) add_with_less_than inc_le)
    qed
  
    have n13:
      \<open>read_register instruction_pointer_ref next_state = n + 6\<close>
      \<open>end_jump_flags next_state\<close>
      \<open>get_end_jump next_state = 1\<close>
      \<open>read_register c01_ref next_state = 1\<close>
      \<open>read_register last_instruction_pointer_ref next_state = n + 13\<close>
      \<open>read_register r03_ref next_state \<le> read_register arg00_ref next_state\<close>
  
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state)))\<close>

      \<open>read_register r01_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 1))\<close>

      \<open>read_register r02_ref next_state 
      = of_nat (fib (unat (read_register r03_ref next_state) + 2))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 13\<close>
      using a0 current_instruction(14) check_trace_decomposition_n13
      by(simp_all add: JUMP_simps)
  
    have n14:
      \<open>read_register instruction_pointer_ref next_state = n + 15\<close>
      \<open>typical_flags next_state\<close>
      \<open>read_register r00_ref next_state 
      = of_nat (fib (unat (read_register arg00_ref next_state)))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 14\<close>
      using a0 current_instruction(15) check_trace_decomposition_n14
      by(simp_all add: END_JUMP_simps)
  
    have n15:
      \<open>read_register instruction_pointer_ref next_state = n + 16\<close>
      \<open>typical_flags next_state\<close>

      \<open>read_register ret00_ref next_state 
      = of_nat (fib (unat(read_register arg00_ref next_state)))\<close>
      if a0: \<open>read_register instruction_pointer_ref current_state = n + 15\<close>
    proof -
      have
        \<open>check_write_permission ret00_ref\<close>
        \<open>check_read_permission r00_ref\<close>
        by(simp_all add: permission_simps)
      then show 
        \<open>read_register instruction_pointer_ref next_state = n + 16\<close>
        \<open>typical_flags next_state\<close>

        \<open>read_register ret00_ref next_state 
        = of_nat (fib (unat (read_register arg00_ref next_state)))\<close>
        using a0 current_instruction(16) check_trace_decomposition_n15
        by(simp_all add: COPY_simps)
    qed
  
    have n16:
      \<open>read_register instruction_pointer_ref current_state = n + 16 
      \<Longrightarrow> get_opcode (fetch_instruction current_state) = 31\<close>
      apply(simp add: fetch_instruction_def)
      apply(simp add: trace_program_memory3)
      apply(simp add: read_program_memory_def)
      apply(simp add: program_loaded program_def)
      apply(simp add: get_opcode_def slice_def slice1_def)
      done

    show 
      \<open>check_trace (finish_function_trace [starting_state] x 
        @ [next_state])\<close>
      using a1 a2
      apply(subst check_trace_def)
      apply(simp)
      apply(subst (asm) check_trace_def)
      using function_start 
      apply(simp)
      using trace_rules 
      apply(simp)
  
      apply(simp add: list_all_def Ball_def)
      apply(elim allE [where x=\<open>current_state\<close>])
      apply(simp add: state_in_trace)
      apply(erule conjE)
      apply(simp add: program_def)
      apply(elim disjE)
      apply(simp_all)
  
      apply(simp add: n16)
      apply(simp add: n15 program_def)
      apply(simp add: n14)
      apply(simp add: n13)
      apply(simp add: n12)
      apply(simp add: n11)
      apply(simp add: n10)
      apply(simp add: n9)
  
      apply(cases \<open>read_register r04_ref current_state = 0\<close>)
      apply(simp add: n8)
      apply(simp add: n8)
  
      apply(simp add: n7)
      apply(simp add: n6)
      apply(simp add: n5)
      apply(simp add: n4)
      apply(simp add: n3)
      apply(simp add: n2)
      apply(simp add: n1)
      apply(simp add: n0)
      done
  qed
qed

end