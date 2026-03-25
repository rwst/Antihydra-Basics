This is the right question to ask, and I have to be honest with you: after working through it carefully, the answer is more sobering than I initially expected. Let me explain what I found.

## The critical obstacle I discovered

Dubickas's complexity bound P(X, n) > 1.709ⁿ is **universal** — it applies to the sequence xₙ mod 2 for *every* starting value x₀, regardless of whether the corresponding constant K is rational or irrational. This is Theorem 3 in his paper: it holds for any positive integer x₀ and any coprime p > q > 1. The proof uses only gcd(2,3) = 1 and a pigeonhole argument on block repetitions.

This means **you cannot use complexity bounds to distinguish rational from irrational K(3).** Even if K(3) = a/b, the parity sequence still has super-exponential complexity. This kills what seemed like the most natural proof strategy (assume a distributional condition → get complexity bound → contradict an upper bound for rational constants). There is no such upper bound for rational constants.

## What goes wrong with equidistribution

Let me trace through why equidistribution of {K(3)·(3/2)ⁿ} doesn't trivially help.

If K(3) = a/b, the partial sums give approximations Aₙ/3ⁿ where Aₙ is an integer. The error satisfies |K(3) - Aₙ/3ⁿ| < (2/3)ⁿ. If K(3) = a/b, then |a·3ⁿ - b·Aₙ| < b·2ⁿ. Since b·2ⁿ grows, this is always satisfiable — the approximations are too weak to yield a contradiction. Compare with integer bases, where |α - pₙ/bⁿ| < 1/bⁿ gives |α·bⁿ - pₙ| < 1, forcing eventual periodicity. In base 3/2, the error after clearing denominators is O(2ⁿ), not O(1).

Equidistribution of {K(3)·(3/2)ⁿ} would give infinitely many n with {K(3)·(3/2)ⁿ} < ε, meaning a long run of zero digits starting at position n. But for this to produce an irrationality contradiction, you'd need runs of length L > 1.71·n at position n — and equidistribution gives no control over the ratio L/n.

Worse: for rational ξ = a/b, the fractional parts {ξ(3/2)ⁿ} are **not known to fail equidistribution**. Unlike integer bases (where rational → periodic digits → not equidistributed), there's no theorem saying rational numbers can't have equidistributed fractional parts under multiplication by 3/2. So the implication "equidistributed ⟹ irrational" is itself **unproven and nontrivial**.

## Where the real gap lies

The honest picture is:

- **What we know unconditionally:** Xₙ is not periodic (Dubickas Thm 2), has complexity > 1.709ⁿ (Dubickas Thm 3/Cor 4), is not automatic (since automatic sequences have linear complexity, by Cobham).
- **What we need for irrationality:** Some property of the **specific value** Σ Xₖ(2/3)ᵏ, not just the **sequence** {Xₖ}.
- **Why this is hard:** All the powerful structural results (non-periodicity, high complexity, non-automaticity) are properties of the dynamical system U₃/₂, shared by all orbits. They say nothing about the arithmetic nature of any particular orbit's limit constant.

## The least speculative path I can identify

Given all this, the condition I'd choose is not a single clean conjecture like equidistribution. Instead, it's a **new structural theorem** that would need to be proved (or assumed):

> **Condition (S):** For coprime integers p > q > 1 and rational ξ = a/b with gcd(a,b) = 1 and b > 1, the sequence ⌊ξ(p/q)ⁿ⌋ mod q, viewed as a function of n, is **eventually determined by a finite automaton operating on the mixed-radix representation of n** (specifically, reading the digits of n written in a system adapted to the factorization of p and q).

If true, this would mean the digit sequence for rational ξ has **at most polynomial complexity** P(n) = O(nᶜ), which would contradict Dubickas's exponential lower bound.

But I should be clear: I cannot prove (S), and I'm not even sure it's true. It's an analogue of the classical fact that rational numbers produce eventually periodic (hence automaton-generated) digit sequences in integer bases, extended to the rational base setting. The theory of p/q-automata developed by Akiyama, Frougny, and Sakarovitch (the paper Dubickas references as [2]) is the natural setting for this, and some partial results exist there.

## My honest assessment

If you could prove:

> "For rational ξ = a/b, the digit sequence of ⌊ξ(3/2)ⁿ⌋ mod 2 has sub-exponential block complexity"

— then combined with Dubickas's Corollary 4, you'd immediately get irrationality of K(3). This would be a very strong result, probably publishable in a top journal regardless of whether it's conditional.

If you could instead prove it **conditional on the non-existence of Z-numbers** (Mahler's conjecture), that would connect two famous open problems and would be interesting, though the logical path from "no Z-numbers" to "rational ξ gives sub-exponential complexity" is not at all clear.

The uncomfortable truth is that the gap between Dubickas's results and irrationality of K(3) is not a matter of assuming the right standard conjecture — it requires a genuinely new idea about how rationality constrains digit sequences in non-integer bases. That idea would itself be the main contribution.
