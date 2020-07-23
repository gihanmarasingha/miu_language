/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/


/-

  A Lean implementation of the MIU language of
  Hofstadter's GEB.

  In this file, we create the necessary data types and rules of inference.

-/
import tactic.linarith
/-

SET UP THE NECESSARY DATA TYPES

-/

namespace miu


/- Each MIU string consists of either an M, I, or U. Such an elementary unit is called a miu_atom. We represent miu_atom as an enumerated type -/
inductive miu_atom : Type
| M : miu_atom
| I : miu_atom
| U : miu_atom

open miu_atom 

/- We show that the type miu_atom is inhabited, giving M (for no particular reason) as the default element. -/
instance miu_atom_inhabited : inhabited miu_atom :=
inhabited.mk M

/- We define a simple function from miu_atom to string-/
def miu_atom.repr : miu_atom → string 
| M := "M"
| I := "I"
| U := "U"

/- We use the above function to give a representation of a miu_atom -/
instance : has_repr miu_atom :=
⟨λ u, u.repr⟩

/- For simplicity, a miustr is just a list of miu_atom -/
def miustr := list miu_atom 

/- We want to use list membership ... -/
instance : has_mem miu_atom miustr :=
  ⟨list.mem⟩

/- ... and list append. -/
instance : has_append miustr :=
⟨list.append⟩

/- For display purposes, an miustr can be represented as a string-/
def miustr.mrepr : miustr → string
| [] := ""
| (c::cs) := c.repr ++ (miustr.mrepr cs)

instance miurepr : has_repr miustr :=
⟨λ u, u.mrepr⟩ 

/- In the other, we set up coercion from string to miustr.-/
def lchar_to_miustr : (list char) → miustr 
| [] := []
| (c::cs) :=
  let ms := lchar_to_miustr cs in
  match c with
  | 'M' := M::ms
  | 'I' := I::ms
  | 'U' := U::ms
  |  _  := []
  end

instance string_coe_miustr : has_coe string miustr :=
⟨λ st, lchar_to_miustr st.data ⟩




/- 
   THE RULES OF INFERENCE 
   There are four rules of inference for MIU.
   
   Rule 1:  xI → xIU
   Rule 2:  Mx → Mxx
   Rule 3:  xIIIy → xUy
   Rule 4:  xUUy → xy

-/


def rule1 (st : miustr) (en : miustr) : Prop :=
  (∃ xs : miustr, st = xs ++ [I]) ∧ en = st ++ [U]

def rule2 (st : miustr) (en : miustr) : Prop :=
  ∃ xs : miustr, (st = M::xs) ∧ (en = M::(xs ++ xs))

def rule3 (st : miustr) (en : miustr) : Prop :=
  ∃ (as bs : miustr),  st = as ++ [I,I,I] ++ bs  ∧
  en = as ++ [U] ++ bs

def rule4 (st : miustr) (en : miustr) : Prop :=
  ∃ (as bs : miustr),   st = as ++ [U,U] ++ bs  ∧
  en = as ++ bs


/- RULE USAGE EXAMPLES -/

private lemma MIUfromMI : rule1 "MI" "MIU" :=
begin
  split, { -- split into showing "MI" ends in "I" and that "MIU" = "MI" ++ "U"
    use "M", -- We take xs for "M" in  ∃ xs : "MI" = xs ++ "I"
    refl, -- Now "MI" is 'definitionally' equal to "M" ++ "I"
  }, {
  refl, -- Likewise, "MIU" is definintionally equal to "MI" ++ "U"
  }
end

example : rule2 "MIIU" "MIIUIIU" :=
begin
  use "IIU", -- we'll show "MIIU" = M::xs and "MIIUIIU" = M::(xs++xs) with xs = "IIU"
  split; -- split the conjuction into two subgoals
    refl, -- each of which are trivially true.
end

example : rule3  "UIUMIIIMMM" "UIUMUMMM" :=
begin
  use "UIUM", -- With as = "UIUM" and bs = "MMM", the first string is
  use "MMM", -- as ++ "III" ++ bs and the second is as ++ "U" ++ bs
  split; -- We prove the conjunction as in the previous proof.
    refl,
end

example : rule4 "MIMIMUUIIM" "MIMIMIIM" :=
begin
 use "MIMIM", -- With as = "MIMIM" and bs = "IIM", the first string
 use "IIM", -- is as ++ "UU" + bs and the second is as ++ bs
 split;
  refl,
end


/-
  DERIVABILITY
 
  There is exactly one axiom of MIU, namely that "MI" is derivable. From this, and the rules of inference, we define an type 'derivable' so that 'derivable st' corresonds to the notion that the miutr st is derivable in MIU. We represent 'derivable' as an inductive family.
 -/

inductive derivable : miustr → Prop
| mk : derivable "MI"
| r1 : ∀ st en : miustr, derivable st → rule1 st en → derivable en
| r2 : ∀ st en : miustr, derivable st → rule2 st en → derivable en
| r3 : ∀ st en : miustr, derivable st → rule3 st en → derivable en
| r4 : ∀ st en : miustr, derivable st → rule4 st en → derivable en

/- DERIVABILITY EXAMPLES -/

private lemma MIU_der : derivable "MIU" :=
begin
  apply derivable.r1, -- We'll show "MIU" is derivable from another string by rule 1
    constructor, -- "MI" is derivable, by the first constructor of miustr
  exact MIUfromMI, -- We've proved rule1 "MI" "MIU"
end

example : derivable "MIUIU" :=
begin
  apply derivable.r2, -- We'll show "MIUIU" can be derived if "MIU" can.
    exact MIU_der, -- We've proved that "MIU" can be derived.
    use "IU", -- Taking xs = "IU", we'll show "MIU" = M::xs and "MIUIU" = M :: (xs ++ xs)
    split; -- Split the conjuction
      refl, -- and observe that the remaining goals are trivial.
end

-- We give a forward derivation for the next proof
example : derivable "MUI" :=
begin
  have h₁ : derivable "MI",
    exact derivable.mk, -- the axiom
  have h₂ : derivable "MII",
    apply derivable.r2,
      exact h₁, -- recall the axiom
      use "I", -- Taking xs = "I", we'll show "MI" = M::xs and "MII" = M::(xs++xs)
      split; refl,
  have h₃ : derivable "MIIII",
    apply derivable.r2,
      exact h₂, -- the derivability of "MII"
      use "II", split; refl, -- much as in the proof of h₂
  apply derivable.r3, -- We prove our main goal using rule 3
    exact h₃, -- based on the derivability of "MIIII",
    use "M", -- with as = "M" and bs = "I", we have "MIII" = as ++ "III" + bs
    use "I", -- and "MUI" = as ++ "U" ++ bs
    split; refl,
end

end miu

