/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/


/-

We give a sufficient condition for a string to be derivable in the MIU
language.

Let icount x and ucount x denote the number of 'I's (respectively
'U's) in the MIU string x.

We'll show that an MIU string is derivable if it has the
form Mx where x is a string of 'I's and 'U's where icount x is
congruent to 1 or 2 modulo 3.

To prove this, it suffices to be able to show that one can derive an MIU
string My where y is a string consisting only of 'I's and where the number
of 'I's in y is a+3b where a = icount x and b = ucount x. This suffices because Rule 3
permits us to change any string of three consecutive 'I's into a 'U'.

Note icount y = (icount x) + 3(ucount x) ≡ icount x (mod 3). Thus, it suffices to
show we can generate any string Mz where z is a string of 'I's such that 
icount z is congruent to 1 or 2 modulo 3.

Let z be such a string and let c denote icount z, so c ≡ 1 or 2 (mod 3).
To derive such a string, it suffices to derive a string Mw, where again w is a string of
only 'I's with the additional conditions that icount w is a power of 2, that 
icount w ≥ c and that icount w ≡ c (mod 3).

To see that this suffices, note that we can remove triples of 'I's from the end of Mw,
creating 'U's as we go along. Once the number of 'I's equals m, we just remove 'U's two
at a time until we have no 'U's. The only issue is that we may not have an even number of
'U's! Writing d = icount w, we see that this happens if and only if (d-c)/3 is odd.
To forestal this eventuality, we apply Rule 1 to z in this case, prior to removing triples
of 'I's. By applying Rule 1, we add an additional 'U' so the final number of 'U's will
be even.

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
  We start by showing that a string Mw can be created, where w consists only of 'I's
  and such that icount w is a power of 2.
-/


lemma pow2str (n : ℕ) : derivable (M::(repeat I (pow 2 n))) :=
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
  We need a more precise result. For any given natural number c ≡ 1 or 2 (mod 3), 
  we need to show that can derive a string Mw where w consists only of 'I's,
  where d = icount w is a power of 2, where d ≥ c and where d ≡ c (mod 3).

  Given the above lemmas, the desired result concenrs only arithmetic.
  The desired arithmetic result is given in the file arithmetic.lean.
-/

/-
  We'll use this result to show we can derive a string of the form Mz
  where z is a string consisting only of 'I's such that icount z ≡ 1 or 2 (mod 3).

  As an intermediate step, we show that derive z from zt, where
  t is a string consisting of an even number of 'U's and z is any string.
-/

/-
  Before that, we prove that we can remove "UU" from the end of a derivable
  string to produce another derivable string.
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


lemma i_freedom (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
  derivable (M::(repeat I c)) :=
begin
  have hd : ∃ d : ℕ, c ≤ (pow 2 d) ∧ (pow 2 d) % 3 = c % 3
    := mod12pow c h,
  rcases hd with ⟨d, hd⟩,
  have hw : derivable (M::(repeat I (pow 2 d))) := pow2str d,
  sorry
end

end miu