1. **`probability_not_certain`**: P(gets_out X depth) < 1 for depth > 0
These require deep probability theory infrastructure:
- **SLLN application**: Showing S_n/n → -1/2 a.s. for the integer-valued walk requires setting up `IdentDistrib`, pairwise independence from `iIndepFun`, integrability, and applying `strong_law_ae_real`.
- **First-step bootstrapping**: Deriving P(gets_out X d) ≤ 1/2 + 1/2·P(gets_out X (d+2)) requires the shift invariance of i.i.d. sequences (showing (X₁,X₂,...) has the same law as (X₀,X₁,...)), which needs careful measure-theoretic arguments about product distributions.
- **Exact probability**: Computing P = φ^d requires the Strong Markov property or the optional stopping theorem for the exponential martingale r^{S_n}.
The mathematical proof strategy is documented in detail in the file's module docstring. The subagent made substantial progress on the SLLN-based approach but couldn't complete all the technical lemmas within its budget.

This is a sophisticated formalization project. To prove `probability_not_certain` (that the probability of escape is $< 1$), you are essentially proving the **transience** of a random walk with negative drift.

A direct proof via the Strong Law of Large Numbers (SLLN) is the most robust path in Lean 4. Here is the detailed plan.

---

### Phase 1: Asymptotic Behavior (The "Infinite" end)
The goal of this phase is to show that because the walk drifts to $-\infty$, it eventually becomes very unlikely to ever hit a high threshold.

**Helper Lemmas to source out:**
1.  **`sum_iid_avg_tendsto`**: Specialize `ProbabilityTheory.strong_law_ae_real` to this specific distribution.
    *   *Statement*: $\mathbb{P} \{ \omega \mid \lim_{n \to \infty} \frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega) = -1/2 \} = 1$.
2.  **`tendsto_neg_inf_ae`**: Show that $S_n \to -\infty$ almost surely.
    *   *Logic*: If $S_n/n \to -1/2$, then for sufficiently large $n$, $S_n < -n/4$, which implies $S_n \to -\infty$.
3.  **`exists_depth_prob_lt_one`**: Show there exists *some* $D$ such that $\mathbb{P}(\text{gets\_out } X D) < 1$.
    *   *Logic*: Since $S_n \to -\infty$ a.s., the supremum $M = \sup_n S_n$ is finite a.s. Therefore, $\lim_{d \to \infty} \mathbb{P}(M \ge d) = 0$. By the definition of limit, there exists $d_0$ where $\mathbb{P}(M \ge d_0) < 1$.

**Lean 4 Gaps:**
*   Mathlib’s `strong_law_ae_real` works on `ℝ`. You will need to use `Int.cast` and ensure the `integrable` assumptions are met (trivial for discrete finite support, but requires boilerplate).
*   **Missing bridge**: A lemma showing that $a.s.$ convergence to $-\infty$ implies the measure of the tail of the supremum tends to 0.

---

### Phase 2: First-Step Analysis (The "Local" transition)
This phase connects the probability at depth $d$ to the probabilities at other depths.

**Helper Lemmas to source out:**
1.  **`gets_out_recursive_sub`**: 
    *   *Statement*: `gets_out X d` is equivalent to `(X 0 = 1 ∧ gets_out (shift X) (d-1)) ∨ (X 0 = -2 ∧ gets_out (shift X) (d+2))`.
    *   *Note*: Requires a `shift` operator for sequences of random variables.
2.  **`prob_gets_out_eq`**: Use independence and the fact that `shift X` has the same distribution as `X`.
    *   *Statement*: $\mathbb{P}(\text{gets\_out } d) = \frac{1}{2} \mathbb{P}(\text{gets\_out } (d-1)) + \frac{1}{2} \mathbb{P}(\text{gets\_out } (d+2))$.

**Lean 4 Gaps:**
*   **Stationarity/Shift Invariance**: While Mathlib has i.i.d. definitions, it lacks a high-level "plug-and-play" theorem stating that for an i.i.d. sequence $X$, $P(f(X_0, X_1, \dots)) = P(f(X_1, X_2, \dots))$. You will likely need to invoke `ProbabilityTheory.iIndepFun.identDistrib` and `MeasurePreserving`.

---

### Phase 3: The Bootstrapping Argument
Now you combine the existence of *some* $d_0$ from Phase 1 with the recurrence from Phase 2 to prove it for *any* $d > 0$.

**Step-by-step logic for `probability_not_certain`:**
1.  **Assume for Contradiction**: Suppose $\mathbb{P}(\text{gets\_out } d) = 1$ for some $d > 0$.
2.  **Downward Pressure**: Use the recurrence $1 = \frac{1}{2} \mathbb{P}(d-1) + \frac{1}{2} \mathbb{P}(d+2)$.
    *   Since probabilities are $\le 1$, this forces $\mathbb{P}(d-1) = 1$ and $\mathbb{P}(d+2) = 1$.
3.  **Induction**: By induction, if escape is certain at any depth $d$, it must be certain for *all* depths $d \in \mathbb{N}$.
4.  **Contradiction**: This contradicts `exists_depth_prob_lt_one` from Phase 1, which proved that for very large depths, the probability must be $< 1$.

---

---

### Summary of Gaps to Fill in Lean 4
1.  **The "Supremum of Drift" Lemma**: A proof that $\mathbb{P}(\limsup S_n = -\infty) = 1 \implies \mathbb{P}(\sup S_n \ge d) \to 0$. This involves the continuity of measure.
2.  **IID Shift Map**: Formalize that `gets_out X (d+1)` and `gets_out (shift X) d` have the same measure.

### Recommended Modularization
Put the general random walk transience (SLLN $\to$ $\mathbb{P} < 1$) in `Probability.Transience`.
Keep the specific $+1/-2$ logic in your main file.
