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
import data.nat.modeq

namespace miu

open miu_atom
open list

/- An auxiliary result -/

lemma doublerep {x : miu_atom} (m : ℕ) : repeat x m ++ repeat x m = repeat x (m*2) :=
by simp [repeat_add, mul_two]


/-
  We start by showing that a string Mw can be created, where w consists only of 'I's
  and such that icount w is a power of 2.
-/


lemma pow2str (n : ℕ) : derivable (M::(repeat I (nat.pow 2 n))) :=
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

  Of course, the result is purely arithmetic.
-/

/- We need two auxiliary lemmata. -/

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

/-
  We'll use the above results to show we can derive a string of the form Mz
  where z is a string consisting only of 'I's such that icount z ≡ 1 or 2 (mod 3).

  As an intermediate step, we show that derive z from zt, where
  t is a string consisting of an even number of 'U's and z is any string.
-/

lemma removeUUat_end (z : miustr) (h : derivable (z ++ [U,U])) :
  derivable z :=
begin
  apply derivable.r4,
  exact h,
  constructor, constructor,
  induction z with s sx hsx, { /- base case leads to a contradiction. -/
    have : ∃ ys : miustr, [U,U] = (M::ys) ∧ ¬(M ∈ ys),
      exact goodmder [U,U] h, 
    cases this with ys hys,
    cc,
  }, { /- Inducton step. -/
    sorry
  },
  sorry,
  sorry 
end


lemma remove_UUs (z : miustr) (m : ℕ) (h : derivable (z ++ repeat U (m*2)))
  : derivable z :=
begin
  induction m with k hk, {
    have : z ++ repeat U (0*2) = z, 
      calc z ++ repeat U (0*2) = z ++ [] : rfl
                           ... = z : append_nil z,
    rw this at h,
    exact h,
  }, {
    apply hk,
    have : z ++ repeat U ((succ k)*2) = (z ++ repeat U (k*2)) ++ [U,U],
      sorry,
    apply removeUUat_end,
    rw ←this,
    exact h,
  }
end


/-

lemma remove_UUs (z : miustr) (m : ℕ) (h : derivable (z ++ repeat U (m*2)))
  : derivable z :=
begin
  induction m with k hk, {
    have : z ++ repeat U (0*2) = z, 
      calc z ++ repeat U (0*2) = z ++ [] : rfl
                           ... = z : append_nil z,
    rw this at h,
    exact h,
  }, {
    apply hk,
    have : z ++ repeat U ((succ k)*2) = z ++ (repeat U (k*2)) ++ [U,U],
      sorry,
    rw this at h,
    apply derivable.r4,
    exact h,
    constructor,
      swap,
      exact (length z + k*2),
    constructor,
    induction z with s hs, {
      rw nil_append,
      sorry 
    }, {
      sorry
    }
      
  }
end

-/


/-
lemma i_freedom (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
  derivable (M::(repeat I c)) :=
  sorry 
-/

end miu