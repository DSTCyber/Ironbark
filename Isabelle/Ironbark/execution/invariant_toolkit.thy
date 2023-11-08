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

subsection \<open>Our Invariant `Toolkit'\<close>

theory invariant_toolkit

imports
  security_properties

begin

text \<open>This file is for developing our invariant toolkit. The primary lemma is 
presented first, which shows that an invariant holds over a program if:
\begin{itemize}
  \item the instruction pointer is in the program
  \item assuming the instruction pointer is in the program, the program hasn't changed, 
and the invariant was true in the previous state, then:
  \begin{itemize}
    \item the instruction pointer stays in the program
    \item the program won't change
    \item the invariant is true in the next state
  \end{itemize}
\end{itemize}\<close>

text \<open>Note that the condition of the program not changing can be trivially shown from 
the security properties, but the other conditions require understanding the behaviour 
of the program and invariant being shown.\<close>

lemma (in Ironbark_world) inv_satI:
  fixes starting_state :: sequential_state
  assumes
      a0: 
        \<open>read_register 
          instruction_pointer_ref 
          (starting_state\<lparr>program_memory := program\<rparr>) 
        \<in> dom program\<close>
    and 
      a1: 
        \<open>predicates (starting_state \<lparr> program_memory := program \<rparr>)\<close>
    and 
      a2: 
        \<open>\<And> state. 
        \<lbrakk> 
          (read_register instruction_pointer_ref state) \<in> dom program;
          program_memory state = program; predicates state 
        \<rbrakk> 
        \<Longrightarrow> predicates (execute_next_instruction state)\<close>
    and 
      a3: 
        \<open>\<And> state. 
        \<lbrakk> 
          (read_register instruction_pointer_ref state) \<in> dom program; 
          program_memory state = program; 
          predicates state 
        \<rbrakk> 
        \<Longrightarrow> (read_register instruction_pointer_ref (execute_next_instruction state)) 
          \<in> dom program\<close>
  shows
    \<open>predicates
      (execute_multiple_instructions 
        (starting_state\<lparr>program_memory := program\<rparr>)
        num_instructions)\<close>

    \<open>read_register
      instruction_pointer_ref
      (execute_multiple_instructions 
        (starting_state\<lparr>program_memory := program\<rparr>)
        num_instructions)
    \<in> dom program\<close>
proof (induct \<open>num_instructions\<close>)
  case 0
  then show 
    \<open>predicates 
      (execute_multiple_instructions (starting_state\<lparr>program_memory := program\<rparr>) 0)\<close>

    \<open>read_register 
      instruction_pointer_ref 
      (execute_multiple_instructions (starting_state\<lparr>program_memory := program\<rparr>) 0)
    \<in> dom program\<close>
    using a0 a1
    by(simp_all)
next
  case (Suc num_instructions)
  then show 
    \<open>predicates 
      (execute_multiple_instructions 
        (starting_state\<lparr>program_memory := program\<rparr>) 
        (Suc num_instructions))\<close> 
    apply(simp)
    apply(subst a2)
    apply(simp_all add: program_memory_immutable')
    done
next
  case (Suc num_instructions)
  then show 
    \<open>read_register
      instruction_pointer_ref
      (execute_multiple_instructions
        (starting_state\<lparr>program_memory := program\<rparr>)
        (Suc num_instructions))
    \<in> dom program\<close>
    apply(simp)
    apply(subst a3)
    apply(simp_all add: program_memory_immutable')
    done
qed

end