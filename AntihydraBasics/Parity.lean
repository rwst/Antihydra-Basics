import AntihydraBasics.Basics
import AntihydraBasics.Constant
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

open Filter Topology Real
open scoped Topology

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

/-- Characterizes the failure of Conjecture 1 (Avoidance) in terms of an index `i` such that
    `i + 1` is a multiple of 3 and `Diter (i+1) 7` is a counterexample. -/
lemma not_Conj1_iff : ¬Conj1 ↔
  ∃ i, (Diter (i + 1) 7) % 2 = 0 ∧ (Diter (i + 1) 7) ≥ 5 ∧ i % 3 = 2 ∧
    (∑ j ∈ Finset.range (i + 1), Diter j 7 % 2) = (i + 1) / 3 := by
  simp only [Conj1, not_not, Nat.even_iff, OddCount]
  constructor
  · rintro ⟨_ | m, h3m, heven, hge5, hcount⟩
    · simp [Diter_zero] at heven
    · exact ⟨m, heven, hge5,
             by have := (Nat.dvd_iff_mod_eq_zero).mp h3m; omega,
             hcount⟩
  · rintro ⟨i, heven, hge5, hmod, hcount⟩
    exact ⟨i + 1, Nat.dvd_of_mod_eq_zero (by omega), heven, hge5, hcount⟩

/-- **Conjecture 2 (Density).**
The odd density converges: lim_{n→∞} ρ(n) = 1/2. -/
def Conj2 : Prop :=
  Tendsto oddDensity atTop (𝓝 (1 / 2 : ℝ))


/-- D(m) ≥ 5 for all m ≥ 0, since D(0) = 7 and the recurrence is strictly increasing. -/
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

/-- O(n) changes by exactly 0 or 1 at each step: |O(n+1) − O(n)| = D(n) % 2 ∈ {0,1}.
This is the key "near-continuity" of the density function. -/
lemma OddCount_step (n : ℕ) :
    OddCount (n + 1) = OddCount n + Diter n 7 % 2 := by
  simp [OddCount, Finset.sum_range_succ]

/-- If the density is above 1/3 at index a and strictly below 1/3 at index b > a
(expressed as 3·O(a) > a and 3·O(b) < b), then there exists
m ∈ [a, b] with 3 ∣ m and O(m) = m/3 exactly. -/
lemma OddCount_IVP_one_third (a b : ℕ) (hab : a ≤ b)
    (ha : 3 * OddCount a > a) (hb : 3 * OddCount b < b) :
    ∃ m : ℕ, a ≤ m ∧ m ≤ b ∧ 3 ∣ m ∧ OddCount m = m / 3 := by
  -- Reduce: 3 * OddCount m = m implies 3 ∣ m and OddCount m = m / 3
  suffices h : ∃ m, a ≤ m ∧ m ≤ b ∧ 3 * OddCount m = m by
    obtain ⟨m, hma, hmb, heq⟩ := h
    exact ⟨m, hma, hmb, ⟨OddCount m, heq.symm⟩, by omega⟩
  -- Key sub-lemma: h(n) = 3*OddCount(n) - n changes by +2 or -1 each step,
  -- so the first n ≥ a with h(n) ≤ 0 satisfies h(n) = 0 exactly.
  have hstep : ∀ n, (∀ k < n, ¬(a ≤ k ∧ 3 * OddCount k ≤ k)) →
      a ≤ n → 3 * OddCount n ≤ n → 3 * OddCount n = n := by
    intro n hmin hna hle
    -- Base case: n = a contradicts ha
    rcases eq_or_lt_of_le hna with h_eq | hn_gt
    · subst h_eq; omega
    -- Predecessor n-1 is not in the set (by minimality)
    have hna_pred : a ≤ n - 1 := by omega
    have hprev : 3 * OddCount (n - 1) > n - 1 := by
      by_contra h; push_neg at h
      exact hmin (n - 1) (by omega) ⟨hna_pred, h⟩
    -- Use OddCount_step: OddCount n = OddCount(n-1) + Diter(n-1) 7 % 2
    have hn_eq : n = (n - 1) + 1 := by omega
    rw [hn_eq, OddCount_step] at hle ⊢
    have : Diter (n - 1) 7 % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
    -- omega handles: if q ≤ 1, 3*(c+q) ≤ p+1, p < 3*c, then 3*(c+q) = p+1
    omega
  -- Find minimum n ≥ a with 3 * OddCount n ≤ n
  have hPex : ∃ n, a ≤ n ∧ 3 * OddCount n ≤ n := ⟨b, hab, Nat.le_of_lt hb⟩
  classical
  exact ⟨Nat.find hPex,
    (Nat.find_spec hPex).1,
    Nat.find_min' hPex ⟨hab, Nat.le_of_lt hb⟩,
    hstep _ (fun k hk => Nat.find_min hPex hk)
      (Nat.find_spec hPex).1 (Nat.find_spec hPex).2⟩

/-- Multiplication by 3 is a bijection on ZMod (2^N) for all N ≥ 1. -/
lemma mul3_bijective_ZMod_pow2 (N : ℕ) :
    Function.Bijective (fun x : ZMod (2 ^ N) => 3 * x) := by
  rw [← IsUnit.isUnit_iff_mulLeft_bijective]
  exact (ZMod.isUnit_iff_coprime 3 (2 ^ N)).mpr
    ((by decide : Nat.Coprime 3 2).pow_right N)

/-- The element 3 has order 2^(N−2) in (ZMod (2^N))× for N ≥ 3. -/
lemma mul3_order_ZMod_pow2 (N : ℕ) (hN : N ≥ 3) :
    orderOf (3 : ZMod (2 ^ N)) = 2 ^ (N - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  simp only [show n + 3 - 2 = n + 1 from by omega]
  -- orderOf (9 : ZMod (2^(n+3))) = 2^n  (since 9 = 1 + 2^3 * 1)
  have h9 : orderOf (9 : ZMod (2 ^ (n + 3))) = 2 ^ n := by
    have heq : (9 : ZMod (2 ^ (n + 3))) = 1 + 2 ^ 3 * (1 : ℤ) := by push_cast; norm_num
    rw [heq]
    exact ZMod.orderOf_one_add_mul_prime_pow Nat.prime_two 3 (by omega) (by omega)
      1 (by norm_num) n
  -- Use orderOf_eq_prime_pow: ¬ 3^(2^n) = 1 and 3^(2^(n+1)) = 1
  apply orderOf_eq_prime_pow
  · -- ¬ (3 : ZMod (2^(n+3)))^(2^n) = 1
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- n = 0: 3^1 = 3 ≠ 1 in ZMod 8
      simp at h; exact absurd h (by decide)
    · -- n ≥ 1: write n = m+1, derive 9^(2^m) = 1, contradicting orderOf 9 = 2^(m+1)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h9m : orderOf (9 : ZMod (2 ^ (m + 1 + 3))) = 2 ^ (m + 1) := h9
      have hstep : (9 : ZMod (2 ^ (m + 1 + 3))) ^ 2 ^ m = 1 := by
        have h2 : (3 : ZMod (2 ^ (m + 1 + 3))) ^ 2 = 9 := by norm_num
        calc (9 : ZMod (2 ^ (m + 1 + 3))) ^ 2 ^ m
            = ((3 : ZMod (2 ^ (m + 1 + 3))) ^ 2) ^ 2 ^ m := by rw [h2]
          _ = (3 : ZMod (2 ^ (m + 1 + 3))) ^ (2 * 2 ^ m) := by rw [← pow_mul]
          _ = (3 : ZMod (2 ^ (m + 1 + 3))) ^ 2 ^ (m + 1) := by congr 1; ring
          _ = 1 := h
      have hdvd := orderOf_dvd_of_pow_eq_one hstep
      rw [h9m] at hdvd
      exact absurd (Nat.le_of_dvd (by positivity) hdvd)
        (Nat.not_le.mpr (Nat.pow_lt_pow_right (by omega) (by omega)))
  · -- (3 : ZMod (2^(n+3)))^(2^(n+1)) = 1
    have h2 : (3 : ZMod (2 ^ (n + 3))) ^ 2 = 9 := by norm_num
    have hexp : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    calc (3 : ZMod (2 ^ (n + 3))) ^ 2 ^ (n + 1)
        = (3 : ZMod (2 ^ (n + 3))) ^ (2 ^ n * 2) := by rw [hexp]
      _ = ((3 : ZMod (2 ^ (n + 3))) ^ 2) ^ 2 ^ n := by
            rw [show 2 ^ n * 2 = 2 * 2 ^ n from mul_comm _ _, pow_mul]
      _ = (9 : ZMod (2 ^ (n + 3))) ^ 2 ^ n := by rw [h2]
      _ = 1 := h9 ▸ pow_orderOf_eq_one 9

/-- D(n) parity: D(n) % 2 = (n / 2) % 2.
    Equivalently, D(n) is even iff n ≡ 0 or 1 (mod 4). -/
lemma D_parity (n : ℕ) : D n % 2 = n / 2 % 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> simp [D] <;> omega

/-! ## 2-adic precision analysis of D

The map D(n) = ⌈3n/2⌉ acts on binary representations by reading and discarding the
lowest bit, multiplying the remaining bits by 3, and adding 0 or 2 depending on the
discarded bit. This means:
- D(a) mod 2^N is determined by a mod 2^(N+1) — one bit of precision is consumed.
- The precision loss is **exact**: D(a) - D(b) = 3(a-b)/2 when a ≡ b mod 2, so
  v₂(D(a) - D(b)) = v₂(a - b) - 1. In other words, D is 2-adically **expanding**
  by a factor of 2.
- After k iterations, Diter k a mod 2^N is determined by a mod 2^(N+k).
- The expansion is exact: v₂(Diter k a - Diter k b) = v₂(a - b) - k.

This expansion property is the fundamental obstruction to eventual periodicity mod 2^N:
pigeonhole gives finite-stretch periodicity (any collision mod 2^(N+L) yields mod 2^N
agreement for L/T periods), but the agreement degrades by T bits per period and
inevitably breaks down.
-/

/-- D preserves residues with one bit of precision loss:
    D(a) ≡ D(b) mod 2^N whenever a ≡ b mod 2^(N+1).

    Proof: a ≡ b mod 2^(N+1) implies same parity ε. Then D(a) - D(b) = 3(a-b)/2,
    and 2^(N+1) | (a-b) implies 2^N | 3(a-b)/2. -/
lemma D_mod_determined (N a b : ℕ) (h : a % 2 ^ (N + 1) = b % 2 ^ (N + 1)) :
    D a % 2 ^ N = D b % 2 ^ N := by sorry

/-- The precision loss of D is exact: one bit per step, no more, no less.
    If a ≡ b mod 2^(N+1) but a ≢ b mod 2^(N+2), then
    D(a) ≡ D(b) mod 2^N but D(a) ≢ D(b) mod 2^(N+1).

    Algebraically: D(a) - D(b) = 3(a-b)/2. If v₂(a-b) = N+1 exactly,
    then v₂(3(a-b)/2) = N+1-1 = N, giving agreement mod 2^N
    but disagreement mod 2^(N+1) (since 3 is odd). -/
lemma D_mod_exact (N a b : ℕ)
    (h_agree : a % 2 ^ (N + 1) = b % 2 ^ (N + 1))
    (h_disagree : a % 2 ^ (N + 2) ≠ b % 2 ^ (N + 2)) :
    D a % 2 ^ N = D b % 2 ^ N ∧ D a % 2 ^ (N + 1) ≠ D b % 2 ^ (N + 1) := by sorry

/-- Iterated D preserves residues: k applications of D consume k bits.
    Diter k a ≡ Diter k b mod 2^N whenever a ≡ b mod 2^(N+k). -/
lemma Diter_mod_determined (N k a b : ℕ) (h : a % 2 ^ (N + k) = b % 2 ^ (N + k)) :
    Diter k a % 2 ^ N = Diter k b % 2 ^ N := by sorry

/-- The precision loss of iterated D is exact: k steps consume exactly k bits.
    If a ≡ b mod 2^(N+k) but a ≢ b mod 2^(N+k+1), then
    Diter k a ≡ Diter k b mod 2^N but Diter k a ≢ Diter k b mod 2^(N+1).

    This is the **2-adic expansion property**: the disagreement bit propagates
    downward at exactly one bit per D-step. -/
lemma Diter_mod_exact (N k a b : ℕ)
    (h_agree : a % 2 ^ (N + k) = b % 2 ^ (N + k))
    (h_disagree : a % 2 ^ (N + k + 1) ≠ b % 2 ^ (N + k + 1)) :
    Diter k a % 2 ^ N = Diter k b % 2 ^ N ∧
    Diter k a % 2 ^ (N + 1) ≠ Diter k b % 2 ^ (N + 1) := by sorry

/-- The orbit of 7 under D is strictly increasing.
    Since D(n) > n for all n ≥ 1 (as (3n+1)/2 > n iff n > -1)
    and Diter k 7 ≥ 7 ≥ 1 for all k. -/
lemma Diter_7_strictMono : StrictMono (fun k => Diter k 7) := by sorry

/-- The orbit of 7 never revisits any value. Corollary of strict monotonicity. -/
lemma Diter_7_injective : Function.Injective (fun k => Diter k 7) :=
  Diter_7_strictMono.injective

/-- Pigeonhole gives finite-stretch mod-periodicity: for any N and any desired
    stretch length L, there exist M and T > 0 such that the orbit mod 2^N
    repeats with period T for at least L consecutive steps starting at M.

    Proof: choose precision P = N + L. Among the first 2^P + 1 orbit values,
    pigeonhole gives i < j with Diter i 7 ≡ Diter j 7 mod 2^P. Set T = j - i,
    M = i. Then Diter_mod_determined gives mod 2^N agreement for P - N = L steps. -/
lemma Diter_mod_periodic_finite_stretch (N L : ℕ) (hN : N ≥ 1) :
    ∃ T > 0, ∃ M, ∀ m ≤ L,
      Diter (M + m + T) 7 % 2 ^ N = Diter (M + m) 7 % 2 ^ N := by sorry

/-- The 2-adic expansion property limits how long finite-stretch periodicity lasts.
    If the orbit has a collision at mod 2^(N+L) precision (but not mod 2^(N+L+1)),
    and the collision period is T, then after ⌈(L+1)/T⌉ periods the mod 2^N
    agreement breaks. Specifically: if j·T > L, consecutive period-T blocks
    disagree mod 2^N.

    This shows that pigeonhole-derived periodicity is inherently self-limiting:
    each period consumes T bits of the initial precision surplus, and when the
    surplus is exhausted, periodicity fails. -/
lemma Diter_mod_agreement_degrades (N L T M : ℕ)
    (hT : T ≥ 1) (hL : L ≥ 1) (hNL : N + L + 1 ≥ T)
    (h_agree : Diter M 7 % 2 ^ (N + L) = Diter (M + T) 7 % 2 ^ (N + L))
    (h_exact : Diter M 7 % 2 ^ (N + L + 1) ≠ Diter (M + T) 7 % 2 ^ (N + L + 1))
    (j : ℕ) (hj : j * T > L) (hjN : (j + 1) * T ≤ N + L) :
    Diter (M + j * T) 7 % 2 ^ N ≠ Diter (M + (j + 1) * T) 7 % 2 ^ N := by sorry

/-- The map D(x) = ⌈3x/2⌉ modulo 2^N cannot be represented as a finite state machine
    on ZMod (2^N), because D(x + c * 2^N) is not necessarily congruent to D(x) modulo 2^N.
    Specifically, the "carry" from the division by 2 introduces dependence on higher bits. -/
lemma D_not_well_defined_mod_pow2 (N : ℕ) (hN : N ≥ 1) :
    ¬ ∀ x c : ℕ, D (x + c * 2 ^ N) % 2 ^ N = D x % 2 ^ N := by
  intro h
  have h1 := h 0 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have he : Even (2 ^ (k + 1)) := ⟨2 ^ k, by ring⟩
  have hD2 : D (2 ^ (k + 1)) = 3 * 2 ^ k := by
    rw [D_even he]
    omega
  have hD0 : D 0 = 0 := rfl
  have heq : 0 + 1 * 2 ^ (k + 1) = 2 ^ (k + 1) := by ring
  rw [heq, hD2, hD0] at h1
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [hp] at h1
  have hm : 3 * 2 ^ k = 2 * 2 ^ k + 2 ^ k := by ring
  rw [hm] at h1
  generalize hK : 2 ^ k = K at h1
  have hpos : K > 0 := by
    rw [← hK]
    exact Nat.two_pow_pos k
  have hmod : (2 * K + K) % (2 * K) = K := by
    rw [Nat.add_mod, Nat.mod_self, zero_add]
    have : K % (2 * K) = K := Nat.mod_eq_of_lt (by omega)
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod, Nat.zero_mod] at h1
  omega

/-- For `q = 3`, the error term `E(3, x)` is simply `x % 2` for `x ≥ 1`. -/
lemma E_three_eq (x : ℕ) (hx : x ≥ 1) : E 3 x = x % 2 := by
  simp only [E]
  have h1 : 3 - 2 = 1 := rfl
  have h2 : 3 - 1 = 2 := rfl
  rw [h1, h2]
  omega

/-- For `q = 3`, the step-wise error `e_step` is `(D^k(n) % 2) / 2`. -/
lemma e_step_three_eq (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    e_step 3 n k = ((Diter k n % 2 : ℕ) : ℝ) / 2 := by
  have h_Diter : Diter' k 3 n = Diter k n := Diter'_three k n
  simp only [e_step, h_Diter]
  have hDpos : Diter k n ≥ 1 := by
    rw [← h_Diter]
    exact Diter'_pos k 3 n (by decide) hn
  rw [E_three_eq _ hDpos]
  congr 1
  norm_num

/-- Summation formula for a sequence that becomes geometric after `M` steps
    with period `T` and ratio `(2/3)^T`. -/
lemma sum_periodic_shift (f : ℕ → ℝ) (T M : ℕ) (hT : T > 0)
    (h_per : ∀ j, f (j + T + M) = f (j + M) * (2/3 : ℝ)^T)
    (h_sum : Summable f) :
    ∑' j, f j = (∑ j ∈ Finset.range M, f j) +
      (∑ j ∈ Finset.range T, f (j + M)) / (1 - (2/3 : ℝ)^T) := by
  sorry

/-- The `j`-th term of the series for the Odlyzko-Wilf constant `K(3, n)`. -/
lemma K_summand_three_eq (n : ℕ) (j : ℕ) (hn : n ≥ 1) :
    K_summand 3 n j = ((Diter j n % 2 : ℕ) : ℝ) / (2 * (3/2 : ℝ) ^ (j + 1)) := by
  simp only [K_summand]
  rw [e_step_three_eq n j hn]
  have hα : α 3 = 3 / 2 := by norm_num [α]
  rw [hα]
  ring

/-- If the parity sequence of Diter is eventually periodic, then the Odlyzko-Wilf constant K(3,7) is rational. -/
lemma parity_periodic_implies_K37_rational (T M : ℕ) (hT : T > 0)
    (h_per : ∀ k ≥ M, Diter (k + T) 7 % 2 = Diter k 7 % 2) :
    ∃ p q : ℤ, q ≠ 0 ∧ ¬ Irrational (K_const 3 7) := by
  have hn : (7 : ℕ) ≥ 1 := by decide
  have h_sum : Summable (K_summand 3 7) := K_summand_summable 3 7 (by decide)
  let f := fun j => K_summand 3 7 j
  have hf_sum : Summable f := h_sum
  have hf_per : ∀ j, f (j + T + M) = f (j + M) * (2/3 : ℝ)^T := by
    intro j
    simp only [f]
    rw [K_summand_three_eq 7 (j + T + M) hn, K_summand_three_eq 7 (j + M) hn]
    have h_parity : Diter (j + T + M) 7 % 2 = Diter (j + M) 7 % 2 := by
      have : j + T + M = (j + M) + T := by omega
      rw [this]
      exact h_per (j + M) (by omega)
    rw [h_parity]
    have hp : (3/2 : ℝ) ^ (j + T + M + 1) = (3/2 : ℝ) ^ (j + M + 1) * (3/2 : ℝ) ^ T := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp]
    have h23 : (2/3 : ℝ) ^ T = 1 / (3/2 : ℝ) ^ T := by
      rw [← one_div_pow]
      congr 1
      norm_num
    rw [h23]
    ring
  have h_K_eval : K_const 3 7 = 7 + ∑' j, f j := rfl
  have h_shift := sum_periodic_shift f T M hT hf_per hf_sum
  rw [h_shift] at h_K_eval
  -- Need to show it's rational
  sorry

/-- The Odlyzko-Wilf constant K(3,7) is irrational. -/
lemma K37_irrational :
    Irrational (K_const 3 7) := by sorry

/-- The parity sequence of Diter is fundamentally not eventually periodic.
    This is equivalent to the irrationality of the Odlyzko-Wilf constant K(3). -/
lemma parity_not_eventually_periodic :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 = Diter k 7 % 2 := by
  intro ⟨T, hT, M, hM⟩
  have ⟨_, _, _, h_not_irr⟩ := parity_periodic_implies_K37_rational T M hT hM
  exact h_not_irr K37_irrational

/-- Generalizes the parity non-periodicity: the sequence `Diter k 7` modulo `2^N`
    is never eventually periodic for any `N ≥ 1`. -/
lemma not_Diter_mod_eventually_periodic (N : ℕ) (hN : N ≥ 1) :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 ^ N = Diter k 7 % 2 ^ N := by
  intro ⟨T, hT, M, hM⟩
  apply parity_not_eventually_periodic
  use T, hT, M
  intro k hk
  have h := hM k hk
  have h_dvd : 2 ∣ 2 ^ N := dvd_pow_self 2 (by omega)
  have h_modeq : Diter (k + T) 7 ≡ Diter k 7 [MOD 2 ^ N] := h
  have h_mod2 : Diter (k + T) 7 ≡ Diter k 7 [MOD 2] := h_modeq.of_dvd h_dvd
  exact h_mod2

/-- If S = {m | 3 ∣ m ∧ OddCount m = m/3} is infinite but all sufficiently large
    S-elements have Diter odd, we derive a contradiction.

    Proof sketch (Branch A of the plan):
    1. Eventual periodicity of parities → odd density converges
    2. S infinite with density hitting 1/3 infinitely often → limit = 1/3
    3. All large S-elements odd → equidistribution via mul3_order forces density 1/2
    4. Contradiction: 1/3 ≠ 1/2 -/
lemma density_one_third_all_odd_contradiction
    (hS_inf : Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3})
    (M : ℕ) (hM : ∀ m ≥ M, 3 ∣ m → OddCount m = m / 3 → Odd (Diter m 7)) :
    False := by sorry

/-- **Critical Lemma 1 / Key Lemma (Variant C).**
Among all m ≡ 0 (mod 3) with O(m) = m/3, infinitely many have Diter m 7 even.
(Equivalently, the set {m | 3 ∣ m ∧ O(m) = m/3 ∧ Even (Diter m 7)} is infinite.) -/
lemma infinitely_many_even_at_density_one_third
    (h : Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3}) :
    Set.Infinite {m : ℕ | 3 ∣ m ∧ OddCount m = m / 3 ∧ Even (Diter m 7)} := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- S_even is finite → bounded above in ℕ
  obtain ⟨M, hM⟩ := hfin.bddAbove
  -- Beyond M, all S-elements must have Diter odd → contradiction via mixing
  exact density_one_third_all_odd_contradiction h (M + 1) fun m hm h3 hoc => by
    rcases Nat.even_or_odd (Diter m 7) with heven | hodd
    · exact absurd (hM ⟨h3, hoc, heven⟩) (by omega)
    · exact hodd

set_option maxRecDepth 100000 in
/-- The claim that out of three consecutive multiples of 3, at least one yields an even D-value is FALSE.
    For example, at j = 66, the indices 198, 201, 204 all yield odd values for Diter. -/
lemma not_consecutive_multiples_of_3_not_all_odd :
    ¬ ∀ j : ℕ,
      Even (Diter (3 * j) 7) ∨
      Even (Diter (3 * j + 3) 7) ∨
      Even (Diter (3 * j + 6) 7) := by
  intro h
  have h66 := h 66
  revert h66
  decide

/-- Let $h(n) = 3 \cdot OddCount(n) - n$. $S$ is the set of indices where $h(n) = 0$.
    Since $D(m)$ is odd at these zeros, the sequence "bounces" off the zero line with a $+2$ step, meaning
    $h(n) \ge 0$ forever.

    It is possible to have an infinite sequence that satisfies this in the $2$-adic integers ($\mathbb{Z}_2$).
    If you start with an appropriate $2$-adic integer (for instance, one matching the pattern $x \equiv 13 \pmod{32}$),
    the map $x \mapsto \lceil \frac{3x}{2} \rceil$ will generate the parity sequence odd, even, even, which maps
    $h(m)=0 \to 2 \to 1 \to 0$. You can chain these paths together infinitely in $\mathbb{Z}_2$.

    This lemma expresses the finite natural-number projection of this $2$-adic trap. -/
lemma exists_arbitrarily_long_oee_pattern (K : ℕ) :
    ∃ x : ℕ, ∀ j < K,
      Diter (3 * j) x % 2 = 1 ∧
      Diter (3 * j + 1) x % 2 = 0 ∧
      Diter (3 * j + 2) x % 2 = 0 := by sorry

/-! ## Main Equivalence -/

/-- The two conjectures are equivalent. -/
theorem conj1_iff_conj2 : Conj1 ↔ Conj2 := by sorry
