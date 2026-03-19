import AntihydraBasics.Constant
import Mathlib.RingTheory.ZMod.UnitsCyclic

open Filter Topology Real
open scoped Topology

def K37 := 7.8641772620566189724051685296822813853

/-!
# Parity Analysis

The sequence is `Diter k 7 = D^[k] 7` with `D(0) = 7`, `D(n+1) = ⌈3·D(n)/2⌉`.
- `OddCount n` = #{i ∈ {0,…,n−1} : Diter i 7 is odd}
- `oddDensity n` = OddCount n / n  (the running odd density ρ(n))
-/

/-- O(n): count of odd values among D(0), D(1), …, D(n−1). -/
def OddCount (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, Diter i 7 % 2

/-- ρ(n) = O(n)/n: the running odd density. -/
noncomputable def oddDensity (n : ℕ) : ℝ := (OddCount n : ℝ) / (n : ℝ)


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
