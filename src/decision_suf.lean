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

/- First some auxiliary lemmas related to rule4 -/

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

/- A minor result. -/

lemma drop_lenIII (z w : miustr) : drop (length z + 3) (z ++ [I,I,I] ++ w) = w :=
begin
  induction z with _ _ hsx,
    simp, /- base case -/
    apply hsx, /- inductive step -/
end

/- An important auxliary result: -/

lemma three_i_to_one_u {as bs : miustr} (h : derivable (as ++ [I,I,I] ++ bs))  : derivable (as ++ [U] ++ bs) :=
begin
  apply derivable.r3,
  exact h,
  unfold rule3,
  use (length as),
  have h₁ :(take (length as) (as ++ [I, I, I] ++ bs)) = as :=
    by simp,
  have h₂ : (drop (length as + 3) (as ++ [I, I, I] ++ bs)) = bs:=
    drop_lenIII as bs,
  constructor;
  rw [h₁,h₂],
end


/- 
  In application of the following lemma, xs will either be [] or [U].
-/
lemma i_to_u (c k : ℕ) (hc : c % 3 = 1 ∨ c % 3 = 2)
  (xs : miustr) (hder : derivable (M ::(repeat I (c+3*k)) ++ xs)) :
    derivable (M::(repeat I c ++ repeat U k) ++ xs) :=
begin
  revert xs,
  induction k with a ha, {
    simp,
  }, {
    intro xs,
    specialize ha ([U]++xs),
    have h₃ : repeat U a ++ [U] = repeat U (a.succ),
    calc repeat U a ++ [U] = repeat U a ++ repeat U 1 : rfl
                       ... = repeat U (a + 1) : by simp [repeat_add],
    have h₄ : M ::(repeat I c ++ repeat U a) ++ ([U] ++ xs) = M:: repeat I c ++ (repeat U a ++ [U]) ++ xs,
      simp,
    rw [h₄,h₃,←append_assoc] at ha,
    intro h,
    have h₂ : M:: repeat I (c + 3*a.succ) = M :: repeat I (c + 3*a) ++ [I,I,I] ,
      calc M:: repeat I (c + 3*a.succ)  
         = M :: repeat I (c + 3*a + 3) : by simp [mul_succ,add_assoc]
     ... = M :: repeat I (c + 3*a) ++ repeat I 3 : by simp [repeat_add]
     ... = M :: repeat I (c + 3*a) ++ [I,I,I]: rfl,
    rw h₂ at h,
    have : derivable (M:: repeat I (c + 3*a) ++ [U] ++ xs), 
      exact three_i_to_one_u h,
    exact ha this,
  }
end


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

/- lemma i_freedom is significant. It shows we can derive My where y is any string consisiting just of 'I's, where icount y is 1 or 2 modulo 3. We start with a small result needed in the larger result
-/

lemma rep_pow_minus_append  (m : ℕ) : M:: repeat I (2^m -1) ++ [I]= M::(repeat I (2^m)) :=
begin
  calc
    M:: repeat I (2^m-1) ++ [I] = M::repeat I (2^m-1) ++ repeat I 1 : by simp
                        ... = M::repeat I ( (2^m-1) + 1) : by simp [repeat_add]
                        ... = M::repeat I (2^m) : by rw nat.sub_add_cancel (one_le_pow' m 1)
end

lemma i_freedom (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
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
      simp [rule1], 
      rw ←rep_pow_minus_append,
      use (M:: repeat I (2^m-1)), /- Finished proof of hw₂ -/
  have hw₃ : derivable (M::(repeat I c) ++ repeat U ((2^m-c)/3) ++ repeat U ((2^m-c)/3 % 2)),
    apply i_to_u c ((2^m-c)/3),
      exact h, /- c is 1 or 2 (mod 3) -/
      have : c + 3 * ((2^m-c)/3) = 2^m, {
        rw nat.mul_div_cancel',
        exact add_sub_of_le hm.1,
        exact (modeq.modeq_iff_dvd' hm.1).mp hm.2.symm, },
      rw this,
      exact hw₂,
  have : repeat U ((2^m-c)/3) ++ repeat U ((2^m-c)/3 % 2) = repeat U ((2^m-c)/3 + (2^m -c)/3  % 2),
    simp [repeat_add],
  simp [this] at hw₃,
  cases add_mod2 ((2^m-c)/3) with t ht,
  rw [ht,←cons_append] at hw₃,
  revert hw₃,
  apply remove_UUs,
end


/- The ucount is the number of 'U's in an miustr -/

def ucount : miustr → ℕ
| [] := 0
| (U::cs) := 1 + ucount cs
| (_::cs) := ucount cs

/- We show that icount is additive with respect to append -/
lemma ucountappend (a b : miustr) :
  ucount (a ++ b) = ucount a + ucount b :=
begin
  induction a with ha hax haxs,
    simp [ucount],
    cases ha;
      simp [ucount, haxs, add_assoc],
end


/- Finally, we have the big result of this project, that the necessary condition decstr (given in another file) for derivability is also sufficient.
-/

/-
Our proof will proceed by induction on the ucount of a string. 
For the base case, we must show that any string en that satifies decstr and has ucount en = 0 must be a string of the form M::(repeat I c), where c is 1 or 2 modulo 3.

-/


/-
We need auxiliary results: one gives a condition for icount ys ≤ length ys. Two others give conditions for icount ys = length ys.
-/

lemma icount_lt {ys : miustr} : icount ys ≤ length ys :=
begin
  induction ys with x xs hxs, {
    simp [icount],
  }, {
    cases x;
      {simp [icount], linarith}
  }
end

lemma icount_eq  {ys : miustr} (h : icount ys = length ys) :
  ys = repeat I (icount ys) :=
begin
  induction ys with x xs hxs, {
    rw icount,
    simp,
  } , { 
    have : icount xs ≤ length xs := icount_lt,
    cases x, swap, { -- swap bring case x = I to the fore
      rw h,
      have : icount xs = xs.length,
        rw [icount,length,add_comm] at h,
        exact add_right_cancel h,
      rw hxs this,
      simp,
    }, repeat  { /- cases where x = M or x = U -/
      rw [icount,length] at h,
      exfalso,
      linarith,
    }
  }
end


lemma icount_eq_length_of_ucount_zero_and_no_m {ys : miustr} (hu : ucount ys = 0) (hm : M ∉ ys) : icount ys = length ys :=
begin
  induction ys with x xs hxs, {
    simp [icount],
  }, {
    cases x, { /- case x = "M" gives a contradiction -/
      exfalso,
      have : M ∈ M::xs,
        simp,
      exact hm this,
    }, { /- case x = "I" -/
      rw [icount,length,add_comm],
      congr' 1,
      apply hxs, {
          rwa ucount at hu,
      }, {
        revert hm,
        simp, 
      }
    }, { /- case x = "U" gives a (different) contradiction -/
      exfalso,
      rw ucount at hu,
      linarith,
    },

  }
end


/-

The following is the base case of the induction of our main theorem.

-/

lemma base_case_suf (en : miustr) (h : decstr en) (hu : ucount en = 0) : derivable en :=
begin
  cases h with hm hi, /- hm : goodm en, hi : congruence condition in icount -/
  rcases hm with ⟨ys, hys, hnm⟩, /- hys : en = M :: ys, hnm :  M ∉ ys -/
  suffices  : ∃ c, ys = repeat I c ∧ (c % 3 = 1 ∨ c % 3 = 2), {
    rcases this with ⟨c, hysr, hc⟩,
    rw [hys, hysr],
    exact i_freedom c hc,
  },
  have hu0 : ucount ys = 0,
    calc ucount ys = 0 + ucount ys : by rw zero_add
               ... = ucount [M] + ucount ys : rfl
               ... = ucount ([M] ++ ys) : by rw ucountappend 
               ... = ucount en : by simp [hys]
               ... = 0 : by rw hu,
  have h₂ : icount ys = icount en,
    calc icount ys = 0 + icount ys : by rw zero_add
               ... = icount [M] + icount ys : rfl
               ... = icount ([M] ++ ys) : by rw icountappend
               ... = icount en : by simp [hys],
  have h₃ : icount ys = length ys,
    exact icount_eq_length_of_ucount_zero_and_no_m hu0 hnm,
  have h₄ : ys = repeat I (icount ys) :=
    icount_eq h₃,
  rw h₂ at h₄, /- replace icount ys with icount en in h₄ -/
  rw h₄,
  use (icount en),
  cc,
end


/- The following result (list.mem_split) from mathlib may be precisely what I need.-/


lemma in_of_ucount_eq_succ {xs : miustr} {k : ℕ} (h : ucount xs = succ k) : U ∈ xs :=
begin
  induction xs with z zs hzs, {
    exfalso, rw ucount at h, contradiction, -- base case
  }, { -- induction step
    simp [eq_or_ne_mem_of_mem],
    cases z, repeat { -- deal equally with the cases z = M and z = I
      rw ucount at h,
      right,
      exact hzs h,
    }, {  -- the case z = U
      left, refl,
    }
  }
end

lemma split_at_first_U {k : ℕ} {ys : miustr} (hm : goodm ys) (h : ucount ys = succ k) : ∃ (as bs : miustr), (ys = M:: as ++ [U] ++ bs) :=
begin
  rcases hm with ⟨xs, hm, _⟩,
  rw hm,
  simp [cons_inj], -- it suffices to prove xs = as ++ [U] ++ bs
  have : ucount ys = ucount xs,
    rw [hm,ucount],
  rw this at h,
  apply mem_split,
  exact in_of_ucount_eq_succ h,
end 

/- The next result is the inductive step of our main theorem.-/
lemma ind_hyp_suf (k : ℕ) (ys : miustr) (hu : ucount ys = succ k) (hdec : decstr ys) :
∃ (as bs : miustr), (ys = M::as ++ [U] ++ bs) ∧ (ucount (M::as ++ [I,I,I] ++ bs) = k) ∧ decstr (M::as ++ [I,I,I] ++ bs) :=
begin
/-   cases hdec with hm hic,
  rcases hm with ⟨xs, hm, hmne⟩, -/
  rcases hdec with ⟨hm,hic⟩,
  rcases split_at_first_U  hm hu with ⟨as,bs,hab⟩,
  use as, use bs,
  split,
    exact hab,
    split, -- show ucount (M::as ++ [I,I,I] ++ bs) = k
      rw [@nat.add_right_cancel (ucount(M::as ++ [I,I,I]++bs)) 1 k ],
      calc ucount ((M::as) ++ [I,I,I]++bs) +1
        = (ucount ( (M::as) ++ ([I,I,I] ++ bs))) + 1 : by simp
    ... = (ucount(M::as) + (ucount ([I,I,I]) + ucount bs)) + 1 : by rw [ucountappend,ucountappend]
    ... = (ucount (M::as) + 0 + ucount bs) + 1 : by simp [ucount]
    ... = ucount (M::as) + 1 + ucount bs : by ring
    ... = ucount (M::as) + ucount [U] + ucount bs : by simp [ucount]
    ... = ucount (( (M::as) ++ [U]) ++ bs) : by rw [ucountappend,←ucountappend]
    ... = ucount (M::as ++ [U] ++ bs) : by simp
    ... = k.succ : by rw [←hab,hu],
    rcases hm with ⟨zs,hzs,hmnze⟩,
    rw hzs at hab, -- M ::zs = M :: as ++ [U] ++ bs
    simp [cons_inj] at hab, -- zs = as ++ [U] ++ bs
    rw hab at hmnze, -- M ∉ as ++ [U] ++ bs
    simp [not_mem_append] at hmnze,
    push_neg at hmnze, -- we have M ∉ as ∧ M ∉ bs.
    -- split decstr (M::as ++ [I,I,I] ++ bs)
    split, { -- first split goodm (M::as ++ [I,I,I] ++ bs)
      constructor, simp [cons_inj], constructor,
      refl, -- now we prove M ∉ as ++ [I,I,I] ++ bs
      apply not_mem_append, exact hmnze.left,
      simp, exact hmnze.right,
    }, { -- now demonstrate the icount is correct.
      rw hab at hzs,
      rw hzs at hic,
      suffices : icount (M::as ++ [I,I,I] ++ bs) = icount (M::as ++ [U]++bs) + 3, {
        rw this,
        simp [hic],
      }, 
      calc icount ((M::as) ++ [I,I,I]++bs)
            = icount ( (M::as) ++ ([I,I,I] ++ bs)) : by simp
        ... = icount (M::as) + (icount ([I,I,I]) + icount bs) : by rw [icountappend,icountappend]
        ... = icount (M::as) + (3 + icount bs) : by simp [icount]
        ... = (icount (M::as) + 0 + icount bs) + 3 : by ring
        ... = (icount (M::as) + icount ([U]) + icount bs) + 3 : by simp [icount]
        ... = icount (( (M::as) ++ [U]) ++ bs) + 3: by rw [icountappend,←icountappend]
        ... = icount (M::as ++ [U] ++ bs) + 3: by simp
    }

end


theorem miu_suff  (en : miustr) (h : decstr en) : derivable en :=
begin
/- The next three lines have the effect of introducing ucount en as a variable that can be used for induction -/

  have hu : ∃ n, ucount en = n, 
    simp,
  cases hu with n hu,
  revert en, /- Crucially, we need the induction hypothesis to quantify over en -/
  induction n with k hk, {
    apply base_case_suf; assumption
  }, {
  intros ys hdec hus,
  /- Idea: apply the induction hypothesis hk in the case where en is the string that arises by replacing the first 'U' in ys with three 'I's. We should be able to deduce decstr en, whence, by the induction hypothesis, derivable en. Applying three_i_to_one_u, we show derivable ys. -/
  rcases ind_hyp_suf k ys hus hdec with ⟨as,bs,hyab,habuc,hdecab⟩,
  have h₂ : derivable (M::as ++ [I,I,I] ++ bs) :=
    hk (M::as ++ [I,I,I] ++ bs) hdecab habuc,
  rw hyab,
  exact three_i_to_one_u h₂,
}
end



end miu