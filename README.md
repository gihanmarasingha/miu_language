# An MIU Decision Procedure in Lean

The [MIU formal system](https://en.wikipedia.org/wiki/MU_puzzle) was introduced by Douglas
Hofstadter in the first chapter of his 1979 book,
[Gödel, Escher, Bach](https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach).
The system is defined by four rules of inference, one axiom, and an alphabet of three symbols:
`M`, `I`, and `U`.

Hofstadter's central question is: can the string `"MU"` be derived?

It transpires that there is a simple decision procedure for this system. A string is derivable if
and only if it starts with `M`, contains no other `M`s, and the number of `I`s in the string is
congruent to 1 or 2 modulo 3.

The principal aim of this project is to give a Lean proof that the derivability of a string is a
decidable predicate.

## The MIU System

In Hofstadter's description, an _atom_ is any one of `M`, `I` or `U`. A _string_ is a finite
sequence of zero or more symbols. To simplify notation, we write a sequence `[I,U,U,M]`,
for example, as `IUUM`.

The four rules of inference are:

1. xI → xIU,
2. Mx → Mxx,
3. xIIIy → xUy,
4. xUUy → xy,

where the notation α → β is to be interpreted as 'if α is derivable, then β is derivable'.

Additionally, he has an axiom:

* `MI` is derivable.

In Lean, it is natural to treat the rules of inference and the axiom on an equal footing via an
inductive data type `derivable` designed so that `derviable x` represents the notion that the string
`x` can be derived from the axiom by the rules of inference. The axiom is represented as a
nonrecursive constructor for `derivable`. This mirrors the translation of Peano's axiom '0 is a
natural number' into the nonrecursive constructor `zero` of the inductive type `nat`.

```lean
inductive derivable : miustr → Prop
| mk : derivable "MI"
| r1 {x} : derivable (x ++ [I]) → derivable (x ++ [I, U])
| r2 {x} : derivable (M :: x) → derivable (M :: x ++ x)
| r3 {x y} : derivable (x ++ [I, I, I] ++ y) → derivable (x ++ U :: y)
| r4 {x y} : derivable (x ++ [U, U] ++ y) → derivable (x ++ y)
```

With the above definition, we can, for example, prove that `"UMIU"` is derivable, assuming `"UMI"` is derivable.
```lean
example (h : derivable "UMI") : derivable "UMIU" :=
begin
  change ("UMIU" : miustr) with [U,M] ++ [I,U],
  exact derivable.r1 h, -- Rule 1
end
```

## References

* Jeremy Avigad, Leonardo de Moura and Soonho Kong, [_Theorem Proving in Lean_](https://leanprover.github.io/theorem_proving_in_lean/).
* Douglas R Hofstadter (1979). _Gödel, Escher, Bach: an eternal golden braid_, New York, Basic Books.