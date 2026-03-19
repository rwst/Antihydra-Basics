While it is true that we just formalized the conditional link showing that **if** $K(3,7)$ is irrational, **then** the parity sequence is non-periodic, formalizing the equidistribution theorem from `proof-mod2^k-equidistribution.md` is **absolutely not within reach** right now.

Here is a breakdown of why this is a massive undertaking in Lean 4, and the difficulties involved:

### 1. The "Key Bijection Lemma" is Mathematically Unproven
The entire proof of exactness (Part b) rests on the "Bijection Lemma". However, if you look closely at the plan, the author admits:
> *"**Verification.** This was confirmed exhaustively for $k = 1,\ldots,8$..."* 
> *"A rigorous inductive proof can be carried out by showing... "*

This means the central lemma of the entire proof is currently just a conjecture verified by a computer program for small values. Before you can even start formalizing this in Lean, you (or a mathematician) would need to invent the actual rigorous inductive proof about "carry chains propagating strictly upward" and formalize those custom bit-carry structures. 

### 2. The 2-Adic API in Lean
To state the theorem, you need to define the map $T(x) = (3x + (x \bmod 2))/2$ on the 2-adic integers ($\mathbb{Z}_2$). 
In mathlib, 2-adics are `PadicInt` (`ℤ_[2]`). However, standard operators like `x % 2` and `x / 2` are not defined out-of-the-box for `ℤ_[2]` the way they are for `ℕ` or `ℤ`. You would need to build an entire API to cleanly extract the "lowest bit" of a 2-adic integer, subtract it, and do exact division by 2, while proving that all these operations are continuous and measurable.

### 3. Deep Measure Theory and Ergodic Theory
To execute Parts (a), (c), and (d), you need to interface with Lean's deep `MeasureTheory` library.
* **Part (a):** You must prove that the two branches of $T^{-1}$ are measurable affine contractions, establish the Haar measure on `ℤ_[2]`, and calculate the sum of the pushforward measures. 
* **Part (c):** You must invoke Birkhoff's Pointwise Ergodic Theorem (`Mathlib.Dynamics.Ergodic.Ergodic`). 
* **Part (d):** This is perhaps the hardest formalized step. The plan claims: *"For an exact endomorphism, the only ergodic-theorem-violating points are the pre-images of periodic orbits"*. This is a highly non-trivial theorem in dynamical systems. You would need to formalize the concept of "exactness" for measure-preserving dynamical systems, and then prove this deep structural property about its exceptional sets. Mathlib does not currently have this specific theorem lying around waiting to be applied.

### Conclusion and Rating

Even though you have the non-periodicity equivalence, the rest of the plan is essentially a research proposal for a paper in arithmetic dynamics. 

**Difficulty Rating: 10/10 (Research Level / Multi-month project)**

To do this, you would need to:
1. Finish the human math for the Bijection Lemma.
2. Build a custom bit-manipulation API for `ℤ_[2]`.
3. Formalize pages of measure theory and Haar measure calculations.
4. Formalize advanced theorems in Ergodic Theory regarding exact endomorphisms and their exceptional sets.