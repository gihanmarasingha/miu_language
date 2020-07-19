/- Some basic arithmetic results needed for the MIU proof. 
   Probably amenable to significant refactoring! -/

import data.nat.modeq
import tactic.linarith

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
      split, { /- ... the two desired properties. -/
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

/- The next lemma is a minor variant of the above. Maybe there's a
clever way to avoid repeating essentially the same proof. -/

lemma mod2pow (x : ℕ) : ∃ m : ℕ, 2+3*x ≤ 2^m ∧ 2^m ≡ 2 [MOD 3]  :=
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
      split, { /- ... the two desired properties. -/
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

/- We combine the above two results to give the desired result. -/

lemma mod12pow (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2) :
  ∃ m : ℕ, c ≤ (pow 2 m) ∧ (pow 2 m) % 3 = c % 3:=
begin
  have k : (c%3) + 3*(c/3) = c,
    apply nat.mod_add_div,
  cases h; {
    rw h at k,
    rw h,
    rw ←k,
    {exact mod1pow (c/3)} <|> {exact mod2pow (c/3)},
  },
end
