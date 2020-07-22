# An MIU Decision Procedure in Lean

The [MIU formal system](https://en.wikipedia.org/wiki/MU_puzzle) was introduced by Douglas Hofstadter in the first chapter of his 1979 book, [Gödel, Escher, Bach](https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach).
The system is defined by four rules of inference, one axiom, and an alphabet of three symbols: `M`, `I`, and `U`.

Hofstadter's central question is: can the string "MU" be derived?

It transpires that there is a simple decision procedure for this system. A string is derivable if and only if it starts with "M", contains no other "M"s, and the number of "I"s in
the string is congruent to 1 or 2 modulo 3.

This project uses the language of the [Lean interactive theorem prover](https://leanprover.github.io/) to express the MIU formal system. We prove that the condition given above 
is both necessary and sufficient for a string to be derivable within MIU.

This is my first proper Lean project (and my first proper Git repository). Comments and suggestions are welcome via Zulip chat.

## The MIU System

An _atom_ is any one of `M`, `I` or `U`. A _string_ is a finite sequence of zero or more symbols. To simplify notation, we write a sequence `[I,U,U,M]`, for example, as `IUUM`.

The four rules of inference are:

1. x`I` → x`IU`,
2. `M`x → `M`xx,
3. x`III`y → x`U`y,
4. x`UU`y → xy,

where the notation α → β is to be interpreted as 'if α is derivable, then β is derivable'.

Additionally, we have an axiom

* `MI` is derivable.

In my implementation, the set of atoms and the set of derivable strings are both represented as inductive types. For the former, we have

```lean
inductive derivable : miustr → Prop
| mk : derivable "MI"
| r1 : ∀ st en : miustr, derivable st → rule1 st en → derivable en
| r2 : ∀ st en : miustr, derivable st → rule2 st en → derivable en
| r3 : ∀ st en : miustr, derivable st → rule3 st en → derivable en
| r4 : ∀ st en : miustr, derivable st → rule4 st en → derivable en
```

where each of `rule1`, ..., `rule4` is a definition corresponding to the rules of inference. For example,
```lean
def rule1 (st : miustr) (en : miustr) : Prop :=
  (∃ xs, st = xs ++ [I]) ∧ en = st ++ [U]
```

The necessary and sufficient condition for a string to be deriable is
```lean
def decstr (en : miustr) :=
  goodm en ∧ ((icount en) % 3 = 1 ∨ (icount en) % 3 = 2)
```
where `goodm` has the definition
```lean
def goodm (xs : miustr) : Prop :=
  ∃ ys : miustr, xs = (M::ys) ∧ ¬(M ∈ ys)
```

The main result, spread over two files, is `derivable en ↔ decstr en`.


