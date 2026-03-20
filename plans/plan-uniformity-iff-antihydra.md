# Proof Plan: Equivalence of Conjectures 1 and 2

## Setup and Definitions

**Recurrence:**  D(0) = 7,  D(n+1) = ⌈3·D(n)/2⌉.

**Parity rule:**
- If D(n) = 2a (even):  D(n+1) = 3a  (exact multiplication by 3/2).
- If D(n) = 2a+1 (odd):  D(n+1) = 3a+2 = (3·D(n)+1)/2  (multiplication by 3/2 plus 1/2).

**Notation:**  For n ≥ 0 let
- O(n) = #{i ∈ {0, …, n−1} : D(i) is odd},  the count of odd values in the first n terms.
- ρ(n) = O(n)/n,  the running odd density.

**Conjecture 1 (Avoidance).**  There is no m ≡ 0 (mod 3) such that D(m) is even, 
D(m) ≥ 5, and O(m) = m/3.

**Conjecture 2 (Density).**  lim_{n→∞} ρ(n) = 1/2.

**Goal:**  Show Conjecture 1 ⟺  Conjecture 2.

---

## Key Structural Observation

Unlike the Collatz map T (which alternates between ×(3/2) for odd inputs and ×(1/2) for even inputs), the map D(n+1) = ⌈3D(n)/2⌉ *always* multiplies by approximately 3/2. Specifically:

    D(k) = (3/2)^k · D(0) + Σ_{i: D(i) odd} (3/2)^{k−1−i} · (1/2)

so D(k) ~ C · (3/2)^k for a constant C > 0. The sequence grows monotonically to infinity. Therefore the original Eliahou–Verger-Gaugry bound—which exploits cancellation between growth (odd steps) and decay (even steps) to force iterates below a minimum—**does not transfer directly**.

The connection between the two conjectures must instead exploit the *deviation of the odd density from 1/2* to produce—or rule out—the specific arithmetic configuration forbidden by Conjecture 1.

---

## Direction 1:  Conjecture 2 ⟹ Conjecture 1

**(Analogous to the easy direction, Conj 4 → Conj 5, in the paper.)**

### Strategy

If ρ(n) → 1/2, then O(m) ≈ m/2 for all large m.  The condition O(m) = m/3 requires the odd density at m to equal 1/3, a permanent deficit from 1/2.  For large m this is incompatible with convergence to 1/2.

### Detailed steps

1. **Quantify convergence.**  Assume ρ(n) → 1/2.  For every ε > 0 there exists N_ε such that for all n ≥ N_ε,  |ρ(n) − 1/2| < ε.

2. **Choose ε = 1/12.**  Then for n ≥ N_{1/12} we have ρ(n) > 1/2 − 1/12 = 5/12.  In particular O(n) > 5n/12.

3. **Compare with m/3.**  If m ≡ 0 (mod 3) and m ≥ N_{1/12}, then O(m) > 5m/12 > m/3 (since 5/12 > 4/12 = 1/3).  So the condition O(m) = m/3 cannot hold.

4. **Finite check.**  For the finitely many m < N_{1/12} with m ≡ 0 (mod 3), verify directly (by computation of D(0), D(1), …, D(N_{1/12})) that no such m satisfies the conditions of Conjecture 1.  Since D(0) = 7 is fixed and the recurrence is deterministic, this is a finite computation.

5. **Conclusion.**  No qualifying m exists.  Conjecture 1 holds.  ∎

### Remark
This direction is clean and the structure parallels the paper exactly: the density assumption eliminates all but finitely many candidates, and the finite remainder is checked by hand.

---

## Direction 2:  Conjecture 1 ⟹ Conjecture 2

**(Analogous to the hard direction, Conj 5 → Conj 4.)**

The original paper's tool was the *multiplicative bound* T^(k)(m) ≤ (3.1)^{k₁}/2^k · m, which shrinks to zero when k₁/k < ln 2 / ln 3.1 ≈ 0.614.  In our setting the map is uniformly expanding, so no single-step contraction is available.  We propose **three variant strategies**.

---
NOTE: VARIANTS A AND B ARE FUTILE

### Variant A:  Contrapositive via the Running Density

**Idea:**  Show ¬Conj 2 ⟹ ¬Conj 1.  If the odd density does *not* converge to 1/2, construct an explicit m that violates Conjecture 1.

#### Step A1 – Classify how Conjecture 2 can fail

If ρ(n) ↛ 1/2, then at least one of:

- (a) lim inf ρ(n) < 1/2  (there are arbitrarily long stretches where odd values are under-represented), or
- (b) lim sup ρ(n) > 1/2  (over-represented), or
- (c) both / oscillation.

#### Step A2 – Case (a): lim inf ρ(n) < 1/2

There exists δ > 0 and infinitely many indices n_j with ρ(n_j) < 1/2 − δ.  Pick δ so that 1/2 − δ < 1/3 + η for small η (this requires δ > 1/6).  If such δ exists, the density passes through 1/3 by the intermediate value theorem applied to O(n)/n (which changes by at most 1/n per step).

**Key Lemma (to prove):**  If ρ(n) passes through 1/3 at some index m ≡ 0 (mod 3), then show that D(m) is even and D(m) ≥ 5 with probability governed by the parity pattern.  Specifically:

- Since D(k) grows as (3/2)^k · 7, for m ≥ 3 we have D(m) ≥ 24, so D(m) ≥ 5 is automatic for m ≥ 3.
- Must show D(m) is even for at least one such m.

**Sub-lemma (to prove):**  Among any three consecutive multiples of 3 (say 3j, 3j+3, 3j+6), at least one has D(·) even.  *Approach:*  Analyze the parity propagation of D modulo 2 under the map.  Since the map modulo 2 is D(n+1) ≡ ⌈3D(n)/2⌉ mod 2, and this depends on D(n) mod 4, study the sequence D(n) mod 4.  The key insight: three consecutive even outputs among D(3j), D(3j+3), D(3j+6) is generically impossible because the "carry" from the ceiling function disrupts long odd runs at multiples of 3.

#### Step A3 – Case (b): lim sup ρ(n) > 1/2

If the density is sometimes above 1/2 and we need it to pass through 1/3, then by continuity of O(n)/n it must also pass through 1/3 at some earlier index.  Reduce to case (a).

#### Step A4 – Case (c): oscillation between values on both sides of 1/2

Again, the density must cross 1/3 from below at some point.  Same reduction.

#### Step A5 – Handle the edge case δ ≤ 1/6

If ρ stays in (1/3, 1/2 − ε) for some ε < 1/6, a more refined argument is needed.  This is where Variant B or C may be required.

---

### Variant B:  Modular Periodicity Argument

**Idea:**  Study D(n) modulo 2^N for increasing N to prove the odd density is exactly 1/2 *provided* a certain modular obstruction is absent.  Then connect the absence of that obstruction to Conjecture 1.

#### Step B1 – Eventual periodicity mod 2^N

For any fixed N, the map D ↦ ⌈3D/2⌉ mod 2^N is a map on a finite set, so the sequence D(n) mod 2^N is eventually periodic.  Let P_N denote the period length and let ρ_N be the odd density within one period.

#### Step B2 – Limiting density

As N → ∞, P_N may grow, but the density ρ_N stabilizes (since the higher bits affect lower bits less and less as D grows).  Prove:

    lim_{N→∞} ρ_N = ρ_∞ = the asymptotic odd density ρ.

**This is the technical core.**  It relies on the fact that D(n) mod 2^N is determined by D(0) mod 2^{N+k} for some bounded k, and the "forgetting" property of the map.

#### Step B3 – Compute ρ_∞ assuming Conjecture 1

The map ⌈3x/2⌉ on integers has the property that modulo 2:
- even → parity of 3x/2 = parity of x/2
- odd → parity of (3x+1)/2

This is closely related to the Collatz parity dynamics.  For generic initial conditions, heuristic equidistribution of D(n) mod 2^N gives ρ_∞ = 1/2.  The only obstruction to equidistribution would be a special modular pattern.

**Claim (to prove):**  If Conjecture 1 holds (the forbidden configuration never occurs), then the sequence D(n) mod 2^N is equidistributed in a suitable sense, implying ρ_∞ = 1/2.

**Approach:**  The forbidden configuration in Conjecture 1 acts as a "trapping condition" — if it occurred, D(m) would enter a cycle modulo 2^N that maintains the parity deficit.  Its absence guarantees sufficient mixing.

#### Step B4 – Conclude Conjecture 2

ρ = ρ_∞ = 1/2.  ∎

---

### Variant C:  Growth-Rate Refinement (Closest to the Paper's Method)

**Idea:**  Although D(n) always grows, the *rate* of growth depends on the odd density.  Use a bound on D(n) relative to a baseline to derive a contradiction.

#### Step C1 – Precise growth formula

Since D(n+1) = (3/2)·D(n) + ε_n where ε_n ∈ {0, 1/2} (with ε_n = 1/2 iff D(n) odd):

    D(k) = (3/2)^k · D(0) + (1/2) Σ_{i=0}^{k−1} (3/2)^{k−1−i} · 𝟙[D(i) odd]

Let S(k) = Σ_{i=0}^{k−1} (3/2)^{k−1−i} · 𝟙[D(i) odd].  Then:

    D(k) = (3/2)^k · 7 + S(k)/2.

#### Step C2 – Bound S(k) using the odd density

If the odd density up to k is ρ(k), the sum S(k) has O(k) = ρ(k)·k nonzero terms, each of size (3/2)^{k−1−i}.  By convexity/concavity arguments:

- If odd values are "spread uniformly": S(k) ≈ ρ(k) · (3/2)^k · 2 / (ln(3/2) · ... ) (geometric series estimate).
- If odd values are "concentrated early" or "concentrated late": S(k) deviates from this.

**Key bound (to prove):**

    D(k) = (3/2)^k · (7 + R(k))

where R(k) depends on the distribution of odd values, with:

    R(k) ≈ 1/(3−2) · ρ(k) = ρ(k)    (crude, dominant term).

More precisely: R(k) → 1 if ρ → 1/2, and R(k) → 2/3 if ρ → 1/3.

#### Step C3 – Use Conjecture 1 to rule out ρ = 1/3

Suppose for contradiction that ρ(n) → 1/3.  Then there are infinitely many m ≡ 0 (mod 3) with O(m) within 1 of m/3.  By density and the intermediate value property of O(m)/m, there exist m ≡ 0 (mod 3) with O(m) = m/3 exactly.

For such m, check: D(m) grows as (3/2)^m · (7 + 2/3 + o(1)), which is even or odd depending on fine arithmetic.  **Crucially:**

**Lemma (to prove):**  For the specific recurrence starting at D(0) = 7, among all m ≡ 0 (mod 3) with O(m) = m/3, infinitely many have D(m) even.

This follows from the equidistribution of D(m) mod 2 along such subsequences (which itself follows from the mixing properties of multiplication by 3 modulo powers of 2).

Since D(m) ≥ 5 is automatic for m ≥ 3, this contradicts Conjecture 1.

#### Step C4 – Extend to any limit ≠ 1/2

If ρ → L ≠ 1/2, consider two cases:

- **L < 1/2:**  By continuity of O(n)/n, the density passes through 1/3 at some point.  Apply the argument from Step C3.
- **L > 1/2:**  The density still passed through 1/3 earlier (since ρ(1) = 1/1 = 1 if D(0) is odd, or 0 if even; D(0) = 7 is odd so ρ(1) = 1, and ρ must decrease toward L > 1/2, crossing 1/3 is not guaranteed).  **Alternative approach needed for L > 1/2:** show that excess odd density creates a secondary periodic structure that also violates Conjecture 1.

#### Step C5 – Handle non-convergence

If ρ(n) does not converge, use lim inf.  If lim inf < 1/2, the density crosses 1/3 and the argument works.  If lim inf ≥ 1/2 but the limit doesn't exist, then lim sup > 1/2 and we need the L > 1/2 variant from Step C4.

---

## Summary: Recommended Proof Architecture

| Component | Status | Method |
|-----------|--------|--------|
| Conj 2 ⟹ Conj 1 | **Straightforward** | Density convergence + finite verification |
| Conj 1 ⟹ Conj 2, case ρ < 1/2 | **Most promising** | Variant A (contrapositive) or C (growth refinement) |
| Conj 1 ⟹ Conj 2, case ρ > 1/2 | **Requires extra work** | Variant B (modular periodicity) |
| Conj 1 ⟹ Conj 2, non-convergence | **Follows from above** | lim inf / lim sup reduction |

### Critical Lemmas to Establish

1. **Even-value density at multiples of 3.**  Among m ≡ 0 (mod 3) with O(m) = m/3, infinitely many have D(m) even.  (Likely provable via D(n) mod 2 analysis under the map.)

2. **D(m) ≥ 5 for m ≥ 3.**  Immediate from the growth D(m) ≥ (3/2)^m · 7.  Already D(3) = ⌈3·⌈3·⌈3·7/2⌉/2⌉/2⌉ = ⌈3·⌈3·11/2⌉/2⌉ = ⌈3·17/2⌉ = 26.  So D(m) ≥ 5 for all m ≥ 0 since D(0) = 7.

3. **Intermediate value property for O(m)/m.**  Since O(m+1)/m+1 differs from O(m)/m by at most ~1/m, the function O(m)/m is "nearly continuous" and must pass through every value between its lim sup and lim inf (up to an error of 1/m).

4. **Parity mixing under ×3 mod 2^N.**  Multiplication by 3 is an automorphism of ℤ/2^N ℤ for N ≥ 1, and has order 2^{N−2} for N ≥ 3.  This ensures sufficient mixing for the equidistribution claims.

---

import AntihydraBasics.Basics
import AntihydraBasics.Constant
import Mathlib.Data.ZMod.Basic

open Filter Topology

def K37 := 7.8641772620566189724051685296822813853

/-!
# Parity Analysis and Density Conjectures

The sequence is `Diter k 7 = D^[k] 7` with `D(0) = 7`, `D(n+1) = ⌈3·D(n)/2⌉`.

## Notation (following the plan)
- `OddCount n` = #{i ∈ {0,…,n−1} : Diter i 7 is odd}
- `oddDensity n` = OddCount n / n  (the running odd density ρ(n))
-/

/-- O(n): count of odd values among D(0), D(1), …, D(n−1). -/
def OddCount (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, Diter i 7 % 2

/-- ρ(n) = O(n)/n: the running odd density. -/
noncomputable def oddDensity (n : ℕ) : ℝ := (OddCount n : ℝ) / (n : ℝ)

/-! ## The Two Conjectures -/

/-- **Conjecture 1 (Avoidance).**
There is no m ≡ 0 (mod 3) such that D(m) is even, D(m) ≥ 5, and O(m) = m/3. -/
def Conj1 : Prop :=
  ¬∃ m : ℕ, 3 ∣ m ∧ Even (Diter m 7) ∧ Diter m 7 ≥ 5 ∧ OddCount m = m / 3

lemma not_Conj1_iff : ¬Conj1 ↔
  ∃ i, (Diter (i + 1) 7) % 2 = 0 ∧ (Diter (i + 1) 7) ≥ 5 ∧ i % 3 = 2 ∧
    (∑ j ∈ Finset.range (i + 1), Diter j 7 % 2) = (i + 1) / 3 := by sorry

/-- **Conjecture 2 (Density).**
The odd density converges: lim_{n→∞} ρ(n) = 1/2. -/
def Conj2 : Prop :=
  Tendsto oddDensity atTop (𝓝 (1 / 2 : ℝ))

/-! ## Critical Lemmas (to be proved) -/

/-- **Critical Lemma 2.**
D(m) ≥ 5 for all m ≥ 0, since D(0) = 7 and the recurrence is strictly increasing. -/
lemma Diter_7_ge_5 (m : ℕ) : Diter m 7 ≥ 5 := by
  have hD_strict : StrictMono D := by
    intro a b h
    have := Dstep_strictMono 3 (by omega) h
    simp only [Dstep_three] at this
    exact this
  suffices h : Diter m 7 ≥ 7 from by omega
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Diter_succ]
    have h1 : D 6 < D (Diter m 7) := hD_strict (by omega)
    have h2 : D 6 = 9 := by decide
    omega

/-- **Critical Lemma 3 (step bound).**
O(n) changes by exactly 0 or 1 at each step: |O(n+1) − O(n)| = D(n) % 2 ∈ {0,1}.
This is the key "near-continuity" of the density function. -/
lemma OddCount_step (n : ℕ) :
    OddCount (n + 1) = OddCount n + Diter n 7 % 2 := by sorry

/-- **Critical Lemma 3 (discrete IVP for 1/3).**
If the density is above 1/3 at index a and strictly below 1/3 at index b > a
(expressed as 3·O(a) > a and 3·O(b) < b), and 3 ∣ b, then there exists
m ∈ [a, b] with 3 ∣ m and O(m) = m/3 exactly. -/
lemma OddCount_IVP_one_third (a b : ℕ) (hab : a ≤ b)
    (ha : 3 * OddCount a > a) (hb : 3 * OddCount b < b) (h3b : 3 ∣ b) :
    ∃ m : ℕ, a ≤ m ∧ m ≤ b ∧ 3 ∣ m ∧ OddCount m = m / 3 := by sorry

/-- **Critical Lemma 4 (parity mixing — automorphism).**
Multiplication by 3 is a bijection on ZMod (2^N) for all N ≥ 1. -/
lemma mul3_bijective_ZMod_pow2 (N : ℕ) (hN : N ≥ 1) :
    Function.Bijective (fun x : ZMod (2 ^ N) => 3 * x) := by sorry

/-- **Critical Lemma 4 (parity mixing — order).**
The element 3 has order 2^(N−2) in (ZMod (2^N))× for N ≥ 3. -/
lemma mul3_order_ZMod_pow2 (N : ℕ) (hN : N ≥ 3) :
    orderOf (3 : ZMod (2 ^ N)) = 2 ^ (N - 2) := by sorry

/-- **Sub-lemma A2.**
Among any three consecutive multiples of 3 (as iteration counts), at least one
yields an even D-value: it is impossible for D(3j), D(3j+3), D(3j+6) all to be odd. -/
lemma consecutive_multiples_of_3_not_all_odd (j : ℕ) :
    Even (Diter (3 * j) 7) ∨
    Even (Diter (3 * j + 3) 7) ∨
    Even (Diter (3 * j + 6) 7) := by sorry

/-- **Critical Lemma 1 / Key Lemma (Variants A and C).**
Among all m ≡ 0 (mod 3) with O(m) = m/3, infinitely many have D(m) even.
(Equivalently, the set {m | 3 ∣ m ∧ O(m) = m/3 ∧ Even (D(m))} is infinite.) -/
lemma infinitely_many_even_at_density_one_third
    (h : Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3}) :
    Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3 ∧ Even (Diter m 7)} := by sorry

/-- **Variant B — Modular density.**
For fixed N, the sequence Diter k 7 mod 2^N is eventually periodic.
Let ρ_N be the odd density within one period; then ρ_N → ρ as N → ∞,
where ρ is the asymptotic odd density (lim ρ(n) if it exists). -/
lemma Diter_mod_pow2_eventually_periodic (N : ℕ) (hN : N ≥ 1) :
    ∃ T S : ℕ, T ≥ 1 ∧ ∀ k ≥ S, Diter (k + T) 7 % 2 ^ N = Diter k 7 % 2 ^ N := by sorry

/-- **Variant B — equidistribution under Conj1.**
If Conjecture 1 holds, then for every N ≥ 1 the orbit of 7 mod 2^N has
odd density exactly 1/2 within its eventual period:
there exist T ≥ 1 and S such that among D(S), …, D(S+T−1) exactly half are odd. -/
lemma equidistributed_mod_pow2_of_Conj1 (hC1 : Conj1) (N : ℕ) (hN : N ≥ 1) :
    ∃ T S : ℕ, T ≥ 2 ∧
    (∀ k ≥ S, Diter (k + T) 7 % 2 ^ N = Diter k 7 % 2 ^ N) ∧
    (∑ k ∈ Finset.range T, Diter (S + k) 7 % 2) * 2 = T := by sorry

/-! ## Main Equivalence -/

/-- The two conjectures are equivalent. -/
theorem conj1_iff_conj2 : Conj1 ↔ Conj2 := by sorry
