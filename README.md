# An MIU Decision Procedure in Lean

The [MIU formal system](https://en.wikipedia.org/wiki/MU_puzzle) was introduced by Douglas Hofstadter in the first chapter of his 1979 book, [Gödel, Escher, Bach](https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach).
The system is defined by four rules of inference, one axiom, and an alphabet of three symbols: M, I, and U.

Hofstadter's central question is: can the string "MU" be derived?

It transpires that there is a simple decision procedure for this system. A string is derivable if and only if it starts with "M", contains no other "M"s, and the number of "I"s in
the string is congruent to 1 or 2 modulo 3.

This project uses the language of the [Lean interactive theorem prover](https://leanprover.github.io/) to express the MIU formal system. We prove that the condition given above 
is both necessary and sufficient for a string to be derivable within MIU.

This is my first proper Lean project (and my first proper Git repository). Comments and suggestions are welcome via Zulip chat.
