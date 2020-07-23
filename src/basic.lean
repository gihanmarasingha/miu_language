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


def miustr.mrepr : miustr → string
| [] := ""
| (c::cs) := c.repr ++ (miustr.mrepr cs)

instance miurepr : has_repr miustr :=
⟨λ u, u.mrepr⟩ 



/- ... and list append. -/
instance : has_append miustr :=
⟨list.append⟩


/- Finally, we set up coercion from string to miustr.-/
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
  (∃ xs, st = xs ++ [I]) ∧ en = st ++ [U]

def rule2 (st : miustr) (en : miustr) : Prop :=
  ∃ xs, (st = M::xs) ∧ (en = M::(xs ++ xs))

def rule3 (st : miustr) (en : miustr) : Prop :=
  ∃ (n : ℕ),  st = st.take n ++ [I,I,I] ++ st.drop (n+3)  ∧
  en = st.take n ++ [U] ++ st.drop (n+3)

def rule4 (st : miustr) (en : miustr) : Prop :=
  ∃ (n : ℕ),   st = st.take n ++ [U,U] ++ st.drop (n+2)  ∧
  en = st.take n ++ st.drop (n+2)


/- RULE USAGE EXAMPLES -/

private lemma MIUfromMI : rule1 "MI" "MIU" :=
begin
  split,
    use "M",
    split,
  split,
end

example : rule2 "MIIU" "MIIUIIU" :=
begin
  existsi ([I,I,U]),
  split;
    constructor
end

example : rule3  "UIUIIIMMM" "UIUUMMM" :=
begin
  existsi 3,
  split; constructor
end

example : rule4 "MIMIUUIIM" "MIMIIIM" :=
begin
  existsi 4,
  split; constructor
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
  constructor,
    constructor,
  exact MIUfromMI,
end

example : derivable "MIUIU" :=
begin
  apply derivable.r2,
    exact MIU_der,
    existsi ([I,U]),
    split;
      constructor
end

end miu

