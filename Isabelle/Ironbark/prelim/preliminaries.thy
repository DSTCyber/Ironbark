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

theory preliminaries

imports
  Main
  "HOL-Library.Word"
  "HOL-Eisbach.Eisbach"

begin

text \<open>This file collects various technical lemmas that extend the HOL/Word base but 
aren't specifically about Ironbark. This is also the entry point into Ironbark, so 
these lemmas are available to all subsequent theories. Also, it's useful to collect 
them to see if they can be rationalised, generalised, or removed.\<close>

text \<open>The following lemmas is used to exhaust the possible values of a word when it 
has been bounded by a less than or equal to operation.\<close>

lemma word_le_decr:
  fixes
    z :: \<open>('a :: len) word\<close>
  assumes 
    \<open>w > 0\<close>
  shows
    \<open>z \<le> w \<longleftrightarrow> z \<le> w - 1 \<or> z = w\<close>
  using assms
  by(uint_arith)

text \<open>We found that the following lemma is useful when trying to show equivalence 
between a term of word type, and a term nat type. The particular case shown here is 
one that we encounter in our Fibonacci proofs, but we expect that other applications 
will require other variations.\<close>

lemma add_with_less_than:
  fixes 
    a b :: \<open>64 word\<close>
  assumes 
    \<open>a < b\<close>
  shows 
    \<open>unat(a + 1) = unat(a) + 1\<close>
proof -
  have 
    \<open>a < a+1\<close>
    using assms
    by(uint_arith)
  then show ?thesis
    apply(subst unat_1[symmetric])
    apply(subst unat_plus_simple[symmetric])
    apply(simp)
    done
qed

text \<open>The following lemma is used to standardise the way we represent single bit 
words (``flags''). We do this mostly to save us writing lemmas for each of the various 
ways that flags can end up being represented.\<close>

lemma flag_normalisation:
  fixes 
    a :: \<open>1 word\<close>
  shows
    \<open>a \<in> {0, 1}\<close>
    \<open>\<not>(bit (a :: 1 word) 0) \<longleftrightarrow> a = 0\<close>
    \<open>even (a :: 1 word) \<longleftrightarrow> a = 0\<close>
    \<open>(bit (a :: 1 word) 0) \<longleftrightarrow> a = 1\<close>
    \<open>odd (a :: 1 word) \<longleftrightarrow> a = 1\<close>
    \<open>a \<noteq> 1 \<longleftrightarrow> a = 0\<close>
    \<open>a \<noteq> 0 \<longleftrightarrow> a = 1\<close>
  by(cases \<open>a\<close>, auto simp add: less_2_cases_iff)+

end