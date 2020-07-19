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


lemma mod1pow (x : ℕ) : ∃ m : ℕ, 1 + 3*x ≤ 2^m ∧ 2^m ≡ 1 [MOD 3] :=
begin
  induction x with k hk, { 
    use 2, /- base case -/
    split;
      norm_num,
    refl,
  }, { /- Induction step -/
    rcases hk with ⟨g, hkg, hgmod⟩, /- Deconstruct the induction hypothesis -/
    /- The argument splits into two cases now, depending on whether
    1 + 3(k+1) ≤ 2^g or not. If true, we take the new exponent to be g,
    else we take it to be g+2. -/
    by_cases hp : (1 + 3*nat.succ k≤ 2^g), { /- Two possibilities-/   
      use g, cc,
    }, { /- The tricky case is when 2^g < 1 + 3(k+1) -/
      use (g+2), /- We take g+2 for the new exponent and show ... -/
      split,{ /- ... the two desired properties. -/
        calc 1 + 3*(succ k) = (1 + 3*k) + 3 : by ring
                        ... ≤ 2^g + 3 : add_le_add_right hkg 3
                        ... ≤ 2^g + 2^g*3 : by linarith 
                        ... = 2^g*2^2 : by ring 
                        ... = 2^(g+2) : by simp [nat.pow_add]
      }, {
        calc 2^(g+2) = 2^g*2^2 : by simp [nat.pow_add]
                 ... = 2^g*4 : by ring
                 ... ≡ 1*1 [MOD 3] : modeq.modeq_mul hgmod rfl
                 ... ≡ 1 [MOD 3] : rfl 
      }
    }
  }
end

/- The next lemma is a minor variant of the above. -/

lemma mod2pow (x : ℕ) : ∃ m : ℕ, 2+3*x ≤ 2^m ∧ 2^m % 3 = 2 :=
begin
  induction x with k hk, { 
    use 3, /- base case -/
    split,
      norm_num,
    refl,
  }, { /- Induction step -/
    rcases hk with ⟨g, hkg, hgmod⟩, /- Deconstruct the induction hypothesis -/
    /- The argument splits into two cases now, depending on whether
    1 + 3(k+1) ≤ 2^g or not. If true, we take the new exponent to be g,
    else we take it to be g+2. -/
    by_cases hp : (2 + 3*nat.succ k≤ 2^g), { /- Two possibilities-/   
      use g, cc,
    }, { /- The tricky case is when 2^g < 1 + 3(k+1) -/
      use (g+2), /- We take g+2 for the new exponent and show ... -/
      split,{ /- ... the two desired properties. -/
        calc 2 + 3*(succ k) = (2 + 3*k) + 3 : by ring
                        ... ≤ 2^g + 3 : add_le_add_right hkg 3
                        ... ≤ 2^g + 2^g*3 : by linarith 
                        ... = 2^g*2^2 : by ring 
                        ... = 2^(g+2) : by simp [nat.pow_add]
      }, {
        calc 2^(g+2) = 2^g*2^2 : by simp [nat.pow_add]
                 ... = 2^g*4 : by ring
                 ... ≡ 2*1 [MOD 3] : modeq.modeq_mul hgmod rfl
                 ... ≡ 2 [MOD 3] : rfl 
      }
    }
  }
end


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