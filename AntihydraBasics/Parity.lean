import AntihydraBasics.Basics
import AntihydraBasics.Constant
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic

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
    OddCount (n + 1) = OddCount n + Diter n 7 % 2 := by
  simp [OddCount, Finset.sum_range_succ]

/-- **Critical Lemma 3 (discrete IVP for 1/3).**
If the density is above 1/3 at index a and strictly below 1/3 at index b > a
(expressed as 3·O(a) > a and 3·O(b) < b), and 3 ∣ b, then there exists
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

/-- **Critical Lemma 4 (parity mixing — automorphism).**
Multiplication by 3 is a bijection on ZMod (2^N) for all N ≥ 1. -/
lemma mul3_bijective_ZMod_pow2 (N : ℕ) :
    Function.Bijective (fun x : ZMod (2 ^ N) => 3 * x) := by
  rw [← IsUnit.isUnit_iff_mulLeft_bijective]
  exact (ZMod.isUnit_iff_coprime 3 (2 ^ N)).mpr
    ((by decide : Nat.Coprime 3 2).pow_right N)

/-- **Critical Lemma 4 (parity mixing — order).**
The element 3 has order 2^(N−2) in (ZMod (2^N))× for N ≥ 3. -/
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

/-! ## Helper lemmas for the key lemma -/

/-- D(n) parity: D(n) % 2 = (n / 2) % 2.
    Equivalently, D(n) is even iff n ≡ 0 or 1 (mod 4). -/
lemma D_parity (n : ℕ) : D n % 2 = n / 2 % 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> simp [D] <;> omega

/-- The Diter sequence mod 2^N is eventually periodic for any N ≥ 1.
    This follows from the pigeonhole principle on ZMod (2^N):
    the map D mod 2^N has finitely many states, so the orbit must cycle. -/
lemma Diter_mod_eventually_periodic (N : ℕ) (hN : N ≥ 1) :
    ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 ^ N = Diter k 7 % 2 ^ N := by sorry

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
Among all m ≡ 0 (mod 3) with O(m) = m/3, infinitely many have D(m) even.
(Equivalently, the set {m | 3 ∣ m ∧ O(m) = m/3 ∧ Even (D(m))} is infinite.) -/
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

/-! ## Main Equivalence -/

/-- The two conjectures are equivalent. -/
theorem conj1_iff_conj2 : Conj1 ↔ Conj2 := by sorry
