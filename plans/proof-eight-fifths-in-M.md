# Plan: Prove (8/5) ∈ M_{1/3}

## Status of the Claim

**Empirical fact** (verified in Lean via `#eval` up to n=5000):
- The deficit walk `3S_n - n` for α = 8/5 stays ≥ 0 for all tested n.
- Minimum value is 0, attained at n = 30.
- The density of odd parities is ≈ 0.49 (well above the 1/3 threshold).

**The notes' claims were wrong in two ways:**
1. The parity sequence is NOT period 3. Actual: `1,0,1,1,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,0,0,...`
2. The walk does NOT cycle through {0,1,2}. It reaches values up to ~16 before dropping back.

## Why Period-3 Fails

For α = 8/5, `y_n = (8/5)(3/2)^n = 8·3^n / (5·2^n)`.

The parity `P_n = ⌊y_n⌋ mod 2` follows the recurrence:
- `⌊y_{n+1}⌋ = ⌊y_n⌋ + ⌊y_n/2⌋` (since `(3/2)y = y + y/2` and `{y}/2 < 1`)

This gives `P_{n+1} ≡ P_n + ⌊y_n/2⌋ mod 2`. The parity depends on `⌊(4/5)(3/2)^n⌋ mod 2`, which is NOT periodic because `(4/5)(3/2)^n` grows without bound and its fractional part doesn't repeat.

Verified: at n=7, `P_7 = 1` but period-3 would predict `P_7 = 0`. The pattern breaks.

## Proof Strategy Options

### Option A: Finite Verification (Easiest, but limited)

The condition `∀ n, 3S_n - n ≥ 0` can be split:
- **Small n** (n ≤ N₀): direct computation via `#eval` or `decide`.
- **Large n** (n > N₀): prove the walk has positive drift and never returns to negative.

For the large-n part, if we can prove `S_n ≥ n/3 + c` for some constant `c > 0` and all `n > N₀`, then `3S_n - n ≥ 3c > 0`.

**Problem**: Proving the drift bound requires understanding the parity sequence analytically, which is hard.

**Estimated difficulty**: Moderate for small-n verification, hard for large-n bound.

### Option B: Use the Average Density

For α = 8/5, empirically `S_n/n ≈ 0.49` for large n. If we can prove `lim inf S_n/n > 1/3`, then there exists N₀ such that for all n > N₀, `S_n > n/3`, so `3S_n - n > 0`. Combined with finite verification for n ≤ N₀, this completes the proof.

**Key lemma needed**: `lim inf (S_n / n) > 1/3` for α = 8/5.

This requires understanding the distribution of `{(4/5)(3/2)^n mod 1}` (which determines whether `⌊(8/5)(3/2)^n⌋` is odd or even).

**Problem**: This is essentially a number-theoretic result about a specific algebraic number, unlikely to be in mathlib.

**Estimated difficulty**: Very hard.

### Option C: Explicit Walk Analysis via the Recurrence

Instead of proving periodicity, track the walk directly through the recurrence:

```
P_{n+1} ≡ P_n + ⌊(4/5)(3/2)^n⌋ mod 2
```

The step `ΔW_n = 3·P_n - 1` takes values:
- `ΔW_n = 2` when `P_n = 1`
- `ΔW_n = -1` when `P_n = 0`

So the walk increases by 2 or decreases by 1. The walk goes negative only if there's a run of ≥ 3 consecutive zeros in P starting from walk value 0 or 1, or a run of ≥ 2 zeros from walk value 0.

**Observation**: The longest run of consecutive zeros in the first 5000 terms is 6 (from n=16 to n=21), but the walk was at 12 when this started. The walk only reaches 0 once (at n=30), and the next value is `P_30 = 1`.

**Possible approach**: Prove a structural property of the P sequence — e.g., that any run of k zeros is preceded by enough ones to keep the walk non-negative.

**Estimated difficulty**: Hard (requires characterizing zero-run structure).

### Option D: Hybrid — Finite Computation + Cheating

For practical purposes, we can verify the claim up to a very large N (e.g., N = 10^6 or 10^7) computationally, then assert it as an axiom or trust the empirical evidence.

In Lean, this would look like:
1. Compute the walk for n = 0..N using `#eval` or a compiled program.
2. For n > N, argue that the density of P=1 is ≈ 0.49 > 1/3, so the walk drifts to +∞.

**Problem**: Lean can't run `#eval` on reals (noncomputable). Need to use `ℚ` arithmetic.

**Estimated difficulty**: Easy for finite check, impossible to close the gap formally without Option B.

## Recommended Approach

### Step 1: Reformulate with `ℚ` arithmetic (avoid noncomputable `ℝ`)

Define `y_rat (n : ℕ) : ℚ := (8 : ℚ) * (3 : ℚ) ^ n / ((5 : ℚ) * (2 : ℚ) ^ n)`.

Prove `⌊(8/5)(3/2)^n⌋₊ = y_rat n |>.floor.toNat` (bridge `ℝ` floor to `ℚ` floor).

This is needed because `ℝ` arithmetic is noncomputable in Lean.

**Key lemma**: `(8/5 : ℝ) * (3/2)^n = ((8 * 3^n : ℕ) : ℝ) / ((5 * 2^n : ℕ) : ℝ)` and then use `Rat.floor` or `Int.floor` of the rational.

### Step 2: Prove the walk formula with `ℚ`-based parity

```
def P_rat (n : ℕ) : ℤ := (y_rat n).floor % 2
def walk_rat (n : ℕ) : ℤ := 3 * (∑ i ∈ Finset.range n, P_rat i) - (n : ℤ)
```

Prove `P_rat n = P n` (the real-valued version) and `walk_rat n = walk n`.

### Step 3: Finite verification

Prove `∀ n ≤ N, walk_rat n ≥ 0` for some large N by computation.

In Lean, this could use:
- A decidable instance for `walk_rat n ≥ 0` for concrete n.
- `decide` for small n, or a `native_decide` / compiled check for larger n.

### Step 4: Asymptotic bound (hardest part)

Prove that for n > N, `walk_rat n > 0` using the density argument.

This requires:
- Characterizing the parity sequence well enough to prove `S_n > n/3 + c` for some c > 0.
- OR proving that the walk has a positive drift by showing the average of P_n exceeds 1/3.

**Realistic expectation**: Step 4 may not be feasible in Lean without significant new number-theoretic formalization.

## Alternative: Use α = 2 Instead

α = 2 also belongs to M_{1/3} (verified: density of P=1 is 1/2, walk grows linearly).

For α = 2: `y_n = 2·(3/2)^n = 3^n/2^{n-1}`. The recurrence `⌊y_{n+1}⌋ = ⌊y_n⌋ + ⌊y_n/2⌋` is cleaner because the initial value is an integer.

The parity sequence for α = 2 is: `0,1,0,0,1,0,0,1,0,0,1,...` which IS period-3 (at least for the first 9 terms). Let me verify this is actually period-3:

y_0 = 2, P_0 = 0
y_1 = 3, P_1 = 1
y_2 = 4.5, P_2 = 0
y_3 = 6.75, P_3 = 0
y_4 = 10.125, P_4 = 1
y_5 = 15.1875, P_5 = 0
y_6 = 22.78125, P_6 = 0
y_7 = 34.171875, P_7 = 1
y_8 = 51.2578125, P_8 = 0

Pattern: 0,1,0,0,1,0,0,1,0,... This is period 3: (0,1,0).

Wait, that's 0,1,0 repeating. S_n = ⌊(n+1)/3⌋. Then 3S_n - n:
n=0: 0-0=0
n=1: 0-1=-1 < 0!

So α = 2 is NOT in M_{1/3}! The walk goes negative at n=1.

So neither α = 2 nor α = 8/5 has a simple period-3 proof.

## Revised Recommendation

The lemma `eight_fifths_in_M_1_3` is almost certainly true (strong empirical evidence) but
proving it in Lean requires either:

1. **Finite computation to very large N** (pragmatic but doesn't constitute a proof of ∀n).
2. **Deep number-theoretic analysis** of the parity sequence (research-level formalization).

For the project's purposes, the most practical path is:
- Keep the `sorry` as a placeholder.
- Use the empirical verification (walk ≥ 0 for n ≤ 5000) as supporting evidence.
- Focus effort on the `M_1_3_co_null` lemma (co-null), which has a cleaner mathematical argument,
  or on the `not_in_mahler_implies_not_Conj1` theorem (already proved).

## Key Lean Technical Challenges

1. **ℝ → ℚ bridge**: `⌊(8/5)(3/2)^n⌋₊` must be related to `⌊8·3^n/(5·2^n)⌋` on ℚ.
   - Need: `(8/5 : ℝ) * (3/2 : ℝ)^n = ((8 * 3^n : ℕ) : ℝ) / ((5 * 2^n : ℕ) : ℝ)`
   - Then: `Nat.floor (a/b : ℝ) = (a / b : ℕ)` when `b > 0` and `b ∣ a`, or more generally use `Int.floor`.

2. **Sum of parities**: `∑ i ∈ Finset.range n, P i` needs to be computed via the ℚ definition.

3. **Computational verification**: Lean's `#eval` can handle ℚ but not ℝ. Need to bridge the result back.

4. **No periodicity to exploit**: Without a clean periodic structure, the proof has no natural inductive structure.
