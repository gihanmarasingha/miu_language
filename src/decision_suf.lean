/-

We give a sufficient condition for a string to be derivable in the MIU
language

-/

import decision_nec
import tactic.linarith
import data.nat.modeq

namespace miu

open miu_atom
open list

/- An auxiliary result -/

lemma doublerep (m : ℕ) : repeat I m ++ repeat I m = repeat I (m*2) :=
by simp [repeat_add, mul_two]

/- We show we can derive a string M::xs where xs is just 2^n copies of I -/


lemma pow2str (n : ℕ)  : derivable (M::(repeat I (nat.pow 2 n))) :=
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


open nat

lemma four_eq_one_mod_3 : 4 ≡ 1 [MOD 3] := by refl 

lemma mod1pow (x : ℕ) : ∃ m : ℕ, 1 + 3*x ≤ 2^m ∧ 2^m ≡ 1 [MOD 3] :=
begin
  induction x with k hk, { /- base case -/
    use 2,
      split;
        norm_num,
      refl,  /- end of base case-/
  }, {
    cases hk with g hk,
    cases hk with hkg hgmod,
    by_cases hp : (1 + 3*nat.succ k≤ 2^g),
      use g,
      split,
        exact hp,
      exact hgmod,
    use (g+2),
    split,
      sorry,
      /-  Idea - show 1 + 3 * succ k ≤ 2^(g+2) using calc -/
    have : 2^(g+2) = (2^g)*4,
      calc 2^((g+1)+1) = (2^(g+1)) *2 : by rw nat.pow_succ
                   ... = ((2^g)*2)*2 : rfl
                   ... = (2^g)*4 : by linarith,
    rw this,
    have : 2^g * 4 ≡ 2^g * 1 [MOD 3],
      apply modeq.modeq_mul_left _ four_eq_one_mod_3,
    rw mul_one at this,
    transitivity;
      assumption
  }


end

#check nat.pow

lemma mod2pow (x : ℕ) : ∃ m : ℕ, 2+3*x ≤ 2^m ∧ 2^m % 3 = 2 :=
  sorry


lemma mod12pow (y : ℕ) (h : y % 3 = 1 ∨ y % 3 = 2) :
  ∃ m : ℕ, y ≤ (pow 2 m) ∧ (pow 2 m) % 3 = y % 3:=
begin
  have k : (y%3) + 3*(y/3) = y,
    apply nat.mod_add_div,
  cases h; {
    rw h at k,
    rw h,
    rw ←k,
    {exact mod1pow (y/3)} <|> {exact mod2pow (y/3)},
  },
end




/- We can derive a string M::xs where xs is a list of succ m copies of I,
   for any m

lemma i_freedom (m : ℕ) : derivable (M::(repeat I (succ m))) :=

-/

end miu