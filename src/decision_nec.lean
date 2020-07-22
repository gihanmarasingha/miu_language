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
  induction a with ha hax haxs,
    simp [icount],
    cases ha;
      simp [icount, haxs, add_assoc],
end

/- We define a property of having the same or double icount mod 3-/

open nat

def nice_abmod3 (a b : ℕ) : Prop :=
  b ≡ a [MOD 3] ∨ b ≡ 2*a [MOD 3]

def nice_imod3 (st en : miustr) : Prop :=
  nice_abmod3 (icount st) (icount en)

example : nice_imod3 "II" "MII" :=
begin
  left, constructor
end


/- We show the icount, mod 3, stays the same or is multiplied by 2 under the rules of inference -/


lemma nice_imod3rule1 (st en : miustr) (h : rule1 st en) :
  nice_imod3 st en :=
begin
  left,
  rw rule1 at h,
  simp [h,nice_imod3,icountappend],
  refl,
end

lemma nice_imod3rule2  (st en : miustr) (h : rule2 st en) :
  nice_imod3 st en :=
begin
  right,
  rw rule2 at h,
  rcases h with ⟨xs, h1, h2⟩,
  simp [h1,h2,icount,icountappend],
  ring,
end


lemma nice_imod3rule3 (st en : miustr) (h : rule3 st en):
  nice_imod3 st en :=
begin
  left,
  rcases h with ⟨n, h1, h2⟩,
  have k : icount st = 3 + icount en, {
    rw [h1,h2],
    repeat {rw icountappend},
    simp [icount],
    ring,
  },
  rw k,
  ring,
end

lemma nice_imod3rule4 (st en : miustr) (h : rule4 st en):
  nice_imod3 st en :=
begin
  left,
  rcases h with ⟨n, h1, h2⟩,
  have k : icount st = icount en, {
    rw [h1,h2],
    repeat {rw icountappend},
    have : icount [U,U] = 0 := by constructor,
    rw this,
    ring,
  },
  rw k,
end

open nat

/- Now we show that the icount of a derivable string is 1 or 2 modulo 3-/

/- We start with a general result about natural numbers.
-/

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


/-
We need some auxiliary lemmata
-/

open list

private lemma m_in_drop (n : ℕ) (ys : miustr) (h : M ∈ drop n ys) :
  M ∈ ys :=
begin
  revert ys,
  induction n with k hk, {
    tauto, 
  }, {
    intro xs,
    induction xs with z zs hzs, {
      tauto,
    }, {
      specialize hk zs,
      rw [drop,mem_cons_iff],
      exact λ w, or.inr (hk w)
    }
  }
end


private lemma m_in_take (n : ℕ) (ys : miustr) (h : M ∈ take n ys) :
  M ∈ ys :=
begin
  revert ys,
  induction n with k hk, {
    tauto,
  }, {
    intro xs,
    induction xs with z zs hzs, {
      tauto,
    }, {
      specialize hk zs,
      simp [take,mem_cons_iff],
      exact or.imp_right hk,
    }
  }
end


lemma goodmrule3 (st en : miustr) (h₁ : rule3 st en) 
  (h₂ : goodm st) : goodm en :=
begin
  rcases h₂ with ⟨ys, p₁, p₂⟩,
  rcases h₁ with ⟨n, k₁, k₂⟩,
  cases n, { /- 'induction' on n-/
    rw p₁ at k₁,
    cases k₁, /- end of base case-/
  }, {
    split, split, { 
      rw k₂, /- Show en starts with M -/
      have : take (succ n) st = M::_,
        rw p₁, refl,
      rwa this, simp,
    }, { /- Show en has no M in its tail-/
      simp [p₂],
      push_neg,
      split, { /- The 'take' part -/
        intro h,
        exact p₂ (m_in_take n ys h),
      }, {  /- The 'drop' part -/
        intro h, 
        rw [p₁,drop] at h,
        exact p₂ (m_in_drop _ ys h),
      }
    }
  }
end


/-
The proof of the next lemma looks identical to the previous proof, but different instances of metavariables are instantiated.
-/

lemma goodmrule4 (st en : miustr) (h₁ : rule4 st en) 
  (h₂ : goodm st) : goodm en :=
begin
  rcases h₂ with ⟨ys, p₁, p₂⟩,
  rcases h₁ with ⟨n, k₁, k₂⟩,
  cases n, { /- 'induction' on n-/
    rw p₁ at k₁,
    cases k₁, /- end of base case-/
  }, {
    split, split, { 
      rw k₂, /- Show en starts with M -/
      have : take (succ n) st = M::_,
        rw p₁, refl,
      rwa this, simp,
    }, { /- Show en has no M in its tail-/
      simp [p₂],
      push_neg,
      split, { /- The 'take' part -/
        intro h,
        exact p₂ (m_in_take n ys h),
      }, {  /- The 'drop' part -/
        intro h, 
        rw [p₁,drop] at h,
        exact p₂ (m_in_drop _ ys h),
      }
    }
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
 