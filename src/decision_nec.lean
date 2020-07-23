/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/



/- We develop a decision procedure for the MIU language.  In this file, we'll give a condition decstr and show that if a string en is derivable, then decstr en holds.

Using this, we give a negation answer to the question: is "MU" derivable?

In another file, we show that the decstr en is sufficient for derivability of en.
-/



import basic
import data.nat.modeq
import tactic.ring

namespace miu

open miu_atom

/- The icount is the number of 'I's in an miustr -/

def icount : miustr → ℕ
| [] := 0
| (I::cs) := 1 + icount cs
| (_::cs) := icount cs

/- We show that icount is additive with respect to append -/
lemma icountappend (a b : miustr) :
  icount (a ++ b) = icount a + icount b :=
begin
  induction a with x hx hxs, -- treat a as x :: xs in the inductive step
    simp [icount], -- trivial base case
    cases x; -- the same proof applies whether x = 'M', 'I', or 'U'
      simp [icount, hxs, add_assoc],
end

/- We define the property of having the same or double icount mod 3-/

open nat

def nice_abmod3 (a b : ℕ) : Prop :=
  b ≡ a [MOD 3] ∨ b ≡ 2*a [MOD 3]

def nice_imod3 (st en : miustr) : Prop :=
  nice_abmod3 (icount st) (icount en)

example : nice_imod3 "II" "MIUI" :=
begin
  left, refl, -- icount "MIUI" ≡ icount "II" [MOD 3]
end

example : nice_imod3 "IUIM" "MI" :=
begin
  right, refl, --icount "MI" ≡ 2*(icount "IUIUM") [MOD 3]
end


/- We show the icount, mod 3, stays the same or is multiplied by 2 under the rules of inference -/


lemma nice_imod3rule1 (st en : miustr) (h : rule1 st en) :
  nice_imod3 st en :=
begin
  left, -- Rule 1 should not affect the number of 'I's.
  rw rule1 at h,
  simp [h,nice_imod3,icountappend],
  refl,
end

lemma nice_imod3rule2  (st en : miustr) (h : rule2 st en) :
  nice_imod3 st en :=
begin
  right,
  rcases h with ⟨xs, h1, h2⟩,
  simp [h1,h2,icount,icountappend],
  ring,
end

lemma nice_imod3rule3 (st en : miustr) (h : rule3 st en):
  nice_imod3 st en :=
begin
  left,
  rcases h with ⟨as,bs,⟨hst,hen⟩⟩,
  rw [hst,hen],
  simp [icountappend,icount,refl],
  ring,
end

lemma nice_imod3rule4 (st en : miustr) (h : rule4 st en):
  nice_imod3 st en :=
begin
  left,
  rcases h with ⟨as,bs,⟨hst,hen⟩⟩,
  rw [hst,hen],
  simp [icountappend,icount,refl],
end


open nat

/- Now we show that the icount of a derivable string is 1 or 2 modulo 3-/

-- We start with a general result about natural numbers.

lemma inheritmod3 (a b : ℕ) (h1 : a % 3 = 1 ∨ a % 3 = 2)
  (h2 : b % 3 = a % 3 ∨  b % 3 = (2 * a % 3)) :
    b % 3 = 1 ∨ b % 3 = 2 :=
begin
  cases h2, {
    rw h2, 
    exact h1,
  }, {
    cases h1, {
      right,
      simp [h2,mul_mod,h1],
      refl,
    }, {
      left,
      simp [h2,mul_mod,h1],
      refl,
    }
  }
end


/- The theorem below shows any derivable string must have an icount that is 1 or 2 modulo 3.
-/
theorem icntder (en : miustr): derivable en → 
  (icount en) % 3 = 1 ∨ (icount en) % 3 = 2:= 
begin
  intro h,
  induction h,
    left,
    apply mod_def,
  any_goals {apply inheritmod3 (icount h_st) _ h_ih},
  apply nice_imod3rule1, assumption,
  apply nice_imod3rule2, assumption,
  apply nice_imod3rule3, assumption,
  apply nice_imod3rule4, assumption,
end

/- Using the above theorem, we solve the MU puzzle, showing that MU is not derivable. -/

theorem notmu : ¬(derivable "MU") :=
begin
  intro h,
  cases (icntder _ h);
    contradiction,
end


/-
That solves the MU puzzle, but we'll proceed by demonstrating the other necessary condition for a string to be derivable, namely that the string must start with an M and contain no M in its tail.
-/


/-
goodm xs holds if the string xs begins with M and contains no M in its tail.
-/

def goodm (xs : miustr) : Prop :=
  ∃ ys : miustr, xs = (M::ys) ∧ ¬(M ∈ ys)

/- Example usage :-/

lemma goodmi : goodm [M,I] :=
begin
  split,
    swap,
  exact [I],
  simp,
end

lemma goodmrule1 (st en : miustr) (h₁ : rule1 st en) 
  (h₂ : goodm st) : goodm en :=
begin
  rcases h₂ with ⟨ys, k₁, k₂⟩,
  rw rule1 at h₁,
  split,
    swap,
    exact (ys ++ [U]),
  simp [h₁, k₁, k₂],
end


lemma goodmrule2 (st en : miustr) (h₁ : rule2 st en) 
  (h₂ : goodm st) : goodm en :=
begin
  rw rule2 at h₁,
  rcases h₁ with ⟨xs, hst, hen⟩,
  rcases h₂ with ⟨ys, k₁, k₂⟩,
  use (xs ++ xs),
  rw hst at k₁,
  cases k₁,
  simp [k₂,hen],
end


open list

lemma goodmrule3  (st en : miustr) (h₁ : rule3 st en) 
  (h₂ : goodm st) : goodm en :=
begin
  rcases h₂ with ⟨ys, p₁, p₂⟩,
  rcases h₁ with ⟨as,bs,⟨hst,hen⟩⟩,
  rw p₁ at hst,
  have h : ∃ zs, as = M :: zs,
    induction as with x xs hxs, { -- base case
      exfalso, 
      have : M = I,
        rw head_eq_of_cons_eq hst,
      contradiction,
    }, { -- induction step
      use xs,
      have : M = x,
        rw head_eq_of_cons_eq hst,
      rw ←this,
    },
  cases h with zs h,
  use (zs++[U]++bs),
  split, {
    simp [hen,h],
  }, {
    simp [h,cons_inj] at hst,
    revert p₂,
    simp [hst],
  }
end


-- The proof of the next lemma is very similar to the previous proof!

lemma goodmrule4 (st en : miustr) (h₁ : rule4 st en) 
  (h₂ : goodm st) : goodm en :=
begin
  rcases h₂ with ⟨ys, p₁, p₂⟩,
  rcases h₁ with ⟨as,bs,⟨hst,hen⟩⟩,
  rw p₁ at hst,
  have h : ∃ zs, as = M :: zs,
    induction as with x xs hxs, { -- base case
      exfalso, 
      have : M = U,
        rw head_eq_of_cons_eq hst,
      contradiction,
    }, {
      use xs,
      have : M = x,
        rw head_eq_of_cons_eq hst,
      rw ←this,
    },
  cases h with zs h,
  use (zs++bs),
  split, {
    simp [hen,h],
  }, {
    simp [h,cons_inj] at hst,
    revert p₂,
    simp [hst],
  }
end


/- The theorem below shows any derivable string must begin with M and contain no M in its tail.
-/
theorem goodmder (en : miustr): derivable en → 
  goodm en:= 
begin
  intro h,
  induction h,
    exact goodmi,
  apply goodmrule1; assumption,
  apply goodmrule2; assumption,
  apply goodmrule3; assumption,
  apply goodmrule4; assumption,
end

/-
We put togther our two conditions to give one condition decstr. Once we've proved sufficiency of this condition, we'll have proved that checking the condition is a decision procedure.
-/

def decstr (en : miustr) :=
  goodm en ∧ ((icount en) % 3 = 1 ∨ (icount en) % 3 = 2)

/-
Combining the previous theorems, we show a derivable string en must satsify condition decstr en.
-/

theorem dec_nec (en : miustr) : derivable en → decstr en:=
begin
  intro h,
  split,
    exact goodmder en h,
    exact icntder en h
end

end miu
 