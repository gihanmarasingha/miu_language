/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/


/-

We give a sufficient condition for a string to be derivable in the MIU language.

Let icount x and ucount x denote the number of 'I's (respectively 'U's) in the MIU string x.

We'll show that an MIU string is derivable if it has the form Mx where x is a string of 'I's and 'U's where icount x is congruent to 1 or 2 modulo 3.

To prove this, it suffices to be able to show that one can derive an MIU string My where y is a string consisting only of 'I's and where the number of 'I's in y is a+3b where a = icount x and b = ucount x. This suffices because Rule 3 permits us to change any string of three consecutive 'I's into a 'U'.

Note icount y = (icount x) + 3(ucount x) ≡ icount x (mod 3). Thus, it suffices to show we can generate any string Mz where z is a string of 'I's such that icount z is congruent to 1 or 2 modulo 3.

Let z be such a string and let c denote icount z, so c ≡ 1 or 2 (mod 3).
To derive such a string, it suffices to derive a string Mw, where again w is a string of only 'I's with the additional conditions that icount w is a power of 2, that icount w ≥ c and that icount w ≡ c (mod 3).

To see that this suffices, note that we can remove triples of 'I's from the end of Mw, creating 'U's as we go along. Once the number of 'I's equals m, we just remove 'U's two at a time until we have no 'U's. The only issue is that we may not have an even number of 'U's! Writing d = icount w, we see that this happens if and only if (d-c)/3 is odd.
To forestall this eventuality, we apply Rule 1 to z in this case, prior to removing triples of 'I's. By applying Rule 1, we add an additional 'U' so the final number of 'U's will be even.

-/

import decision_nec
import tactic.linarith
import arithmetic

namespace miu

open miu_atom
open list
open nat

/- An auxiliary result -/

lemma doublerep {x : miu_atom} (m : ℕ) : repeat x m ++ repeat x m = repeat x (m*2) :=
by simp [repeat_add, mul_two]


/-
  We start by showing that a string Mw can be created, where w consists only of 'I's and such that icount w is a power of 2.
-/


lemma pow2str (n : ℕ) : derivable (M::(repeat I (2^n))) :=
begin
  induction n with k hk, {
    constructor, /- base case -/
  }, { /- Start of induction step -/
    apply derivable.r2, { /- We'll use rule 2 -/
      exact hk, /- hk : M followed by 2^k I's is derivable -/
    }, {
      constructor, /- decompose the disjunction -/
      rw doublerep, /- Replace two identical I strings with one twice as long -/
      split; 
        refl,
    }
  }
end


/-
  We need a more precise result. For any given natural number c ≡ 1 or 2 (mod 3), we need to show that can derive a string Mw where w consists only of 'I's,  where d = icount w is a power of 2, where d ≥ c and where d ≡ c (mod 3).

  Given the above lemmas, the desired result reduces to an arithmetic result, given in the file arithmetic.lean.
-/

/-
  We'll use this result to show we can derive a string of the form Mz where z is a string consisting only of 'I's such that icount z ≡ 1 or 2 (mod 3).

  As an intermediate step, we show that derive z from zt, where t is a string consisting of an even number of 'U's and z is any string.
-/

/-
  Before that, we prove that we can remove "UU" from the end of a derivable string to produce another derivable string.
-/

/- First some auxiliary lemmas related to rule4' -/

lemma take_lenUU (z : miustr) : take (length z) (z ++ [U,U]) = z := by simp

lemma drop_lenUU (z : miustr) : drop (length z + 2) (z ++ [U,U]) = [] :=
begin
  induction z with _ _ hsx,
    simp, /- base case -/
    apply hsx, /- inductive step -/
end

lemma removeUUat_end (z : miustr) (h : derivable (z ++ [U,U])) :
  derivable z :=
begin
  apply derivable.r4,
  exact h,
  constructor, /- Decompose disjunction in rule4 -/
  swap,
  exact (length z),
  rw rule4',
  simp [take_lenUU,drop_lenUU],
end

lemma remove_UUs (z : miustr) (m : ℕ) (h : derivable (z ++ repeat U (m*2)))
  : derivable z :=
begin
  induction m with k hk, { /- base case for induction on m -/
    revert h,
    simp [list.repeat],
  }, { /- inductive step -/
    apply hk,
    apply removeUUat_end,
    revert h,
    simp [succ_mul,repeat_add],
  }
end

/- 
  In application of the following lemma, xs will either be [] or [U].
-/


lemma i_to_u (c d : ℕ) (hc : c % 3 = 1 ∨ c % 3 = 2) (hcd : c ≡ d [MOD 3]) 
  (xs : miustr) (hder : derivable (M ::(repeat I d) ++ xs)) :
    derivable (M::(repeat I c ++ repeat U ((d-c)/3)) ++ xs) :=
  sorry

/- Heavy use of library_search helped with the following proof :) -/
lemma add_mod2 (a : ℕ) : ∃ t, a + a % 2 = t*2 :=
begin 
  suffices :  ∃ t, a + a % 2 = 2*t, {
    cases this with t ht,
    rw mul_comm at ht,
    use t, exact ht
  },
  have : (a + a%2) % 2 = 0,
    rw [add_mod,mod_mod,←two_mul,mul_mod_right],
  apply dvd_of_mod_eq_zero,
  rw this,
end

lemma i_freedom  (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
  derivable (M::(repeat I c)) :=
begin
  /- We start by showing that string Mw described in the introduction can be derived. First derive m, where 2^m is the number of 'I's in this string. -/
  have hm : ∃ m : ℕ, c ≤ (2^m) ∧ (2^m) % 3 = c % 3
    := mod12pow c h,
  cases hm with m hm,
  /- Now derive the string Mw. -/
  have hw : derivable (M::(repeat I (2^m))) := pow2str m,
  have hw₂ : derivable (M::(repeat I (2^m)) ++ repeat U ((2^m -c)/3 % 2)),
    cases mod_two_eq_zero_or_one ((2^m -c)/3) with h_zero h_one, {
      rw h_zero,  /- Case where (2^m - c)/3 ≡ 0 [MOD 2]-/
      simp [hw] }, 
      rw h_one,  /- Case where (2^m - c)/3 ≡ 1 [MOD 2]-/
      apply derivable.r1,
      exact hw,
      simp [rule1], /- Finished proof of hw₂ -/
  have hw₃ : derivable (M::(repeat I c) ++ repeat U ((2^m-c)/3) ++
    repeat U ((2^m-c)/3 % 2)),
    apply i_to_u,
      exact h, /- c is 1 or 2 (mod 3) -/
      apply (hm.2).symm, /- c ≡ 2^m (mod 3) -/
      exact hw₂,
  have : repeat U ((2^m-c)/3) ++ repeat U ((2^m-c)/3 % 2) = repeat U ((2^m-c)/3 + (2^m -c)/3  % 2),
    simp [repeat_add],
  simp [this] at hw₃,
  cases add_mod2 ((2^m-c)/3) with t ht,
  rw [ht,←cons_append] at hw₃,
  revert hw₃,
  apply remove_UUs,
end

end miu