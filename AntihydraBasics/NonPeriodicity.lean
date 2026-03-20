import AntihydraBasics.Basics
import Mathlib.Data.Nat.ModEq

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
    D a % 2 ^ N = D b % 2 ^ N := by
  simp [D]
  have h2 : 2 * 2 ^ N = 2 ^ (N + 1) := by ring
  have hdiv : ∀ x : ℕ, (3 * x + 1) / 2 % 2 ^ N = (3 * x + 1) % 2 ^ (N + 1) / 2 := by
    intro x
    rw [← Nat.mod_mul_right_div_self (3 * x + 1) 2 (2 ^ N), h2]
  rw [hdiv a, hdiv b]
  have hcong : (3 * a + 1) % 2 ^ (N + 1) = (3 * b + 1) % 2 ^ (N + 1) :=
    Nat.ModEq.add (Nat.ModEq.mul rfl h) rfl
  rw [hcong]

/-- If a ≡ b mod m and d | m, then a ≡ b mod d. -/
lemma mod_eq_of_mod_eq_of_dvd {a b d m : ℕ} (hd : d ∣ m) (h : a % m = b % m) :
    a % d = b % d :=
  Nat.ModEq.of_dvd hd h

/-- For any x, (3*x+1) % 2 = (x+1) % 2. -/
lemma three_mul_add_one_mod2 (x : ℕ) : (3 * x + 1) % 2 = (x + 1) % 2 := by omega

/-- Parity of (3*x+1) depends only on x mod 2^(N+1), not x mod 2^(N+2).
    If a ≡ b mod 2^(N+1) then (3*a+1) % 2^(N+2) ≡ (3*b+1) % 2^(N+2) mod 2. -/
lemma three_mul_add_one_mod2_agree (N a b : ℕ) (h : a % 2 ^ (N + 1) = b % 2 ^ (N + 1)) :
    (3 * a + 1) % 2 ^ (N + 2) % 2 = (3 * b + 1) % 2 ^ (N + 2) % 2 := by
  have h2ab : a % 2 = b % 2 :=
    mod_eq_of_mod_eq_of_dvd ⟨2 ^ N, by ring⟩ h
  rw [Nat.mod_mod_of_dvd _ ⟨2 ^ (N + 1), by ring⟩,
      Nat.mod_mod_of_dvd _ ⟨2 ^ (N + 1), by ring⟩]
  rw [three_mul_add_one_mod2, three_mul_add_one_mod2]
  omega

/-- If u / 2 = v / 2 and u % 2 = v % 2, then u = v.
    This is the injectivity of the map x ↦ (x/2, x%2). -/
lemma eq_of_div2_and_mod2 (u v : ℕ) (hdiv : u / 2 = v / 2) (hmod : u % 2 = v % 2) :
    u = v := by omega

/-- 3 is coprime to any power of 2. -/
lemma coprime_three_pow_two (n : ℕ) : Nat.Coprime 3 (2 ^ n) :=
  (Nat.Coprime.pow_left n (Nat.Coprime.symm (by decide))).symm

/-- From (3*a+1) % 2^(N+2) = (3*b+1) % 2^(N+2), derive a % 2^(N+2) = b % 2^(N+2).
    Key step: the coprimality of 3 and powers of 2. -/
lemma eq_of_three_mul_add_one_mod (N a b : ℕ)
    (h : (3 * a + 1) % 2 ^ (N + 2) = (3 * b + 1) % 2 ^ (N + 2)) :
    a % 2 ^ (N + 2) = b % 2 ^ (N + 2) := by
  have hcong : (3 * a + 1) ≡ (3 * b + 1) [MOD 2 ^ (N + 2)] := h
  have h3cong : 3 * a ≡ 3 * b [MOD 2 ^ (N + 2)] :=
    Nat.ModEq.add_right_cancel' 1 hcong
  rw [mul_comm 3 a, mul_comm 3 b] at h3cong
  exact Nat.ModEq.cancel_right_of_coprime
    ((coprime_three_pow_two (N + 2)).symm) h3cong

/-- The precision loss of D is exact: one bit per step, no more, no less.
    If a ≡ b mod 2^(N+1) but a ≢ b mod 2^(N+2), then
    D(a) ≡ D(b) mod 2^N but D(a) ≢ D(b) mod 2^(N+1).

    Algebraically: D(a) - D(b) = 3(a-b)/2. If v₂(a-b) = N+1 exactly,
    then v₂(3(a-b)/2) = N+1-1 = N, giving agreement mod 2^N
    but disagreement mod 2^(N+1) (since 3 is odd). -/
lemma D_mod_exact (N a b : ℕ)
    (h_agree : a % 2 ^ (N + 1) = b % 2 ^ (N + 1))
    (h_disagree : a % 2 ^ (N + 2) ≠ b % 2 ^ (N + 2)) :
    D a % 2 ^ N = D b % 2 ^ N ∧ D a % 2 ^ (N + 1) ≠ D b % 2 ^ (N + 1) := by
  constructor
  · exact D_mod_determined N a b h_agree
  · intro hmod
    have hdiv_a : (3 * a + 1) / 2 % 2 ^ (N + 1) = (3 * a + 1) % 2 ^ (N + 2) / 2 := by
      rw [← Nat.mod_mul_right_div_self (3 * a + 1) 2 (2 ^ (N + 1))]
      rw [show 2 * 2 ^ (N + 1) = 2 ^ (N + 2) by ring]
    have hdiv_b : (3 * b + 1) / 2 % 2 ^ (N + 1) = (3 * b + 1) % 2 ^ (N + 2) / 2 := by
      rw [← Nat.mod_mul_right_div_self (3 * b + 1) 2 (2 ^ (N + 1))]
      rw [show 2 * 2 ^ (N + 1) = 2 ^ (N + 2) by ring]
    simp [D] at hmod
    rw [hdiv_a, hdiv_b] at hmod
    set u := (3 * a + 1) % 2 ^ (N + 2)
    set v := (3 * b + 1) % 2 ^ (N + 2)
    have hpar : u % 2 = v % 2 := by
      change (3 * a + 1) % 2 ^ (N + 2) % 2 = (3 * b + 1) % 2 ^ (N + 2) % 2
      exact three_mul_add_one_mod2_agree N a b h_agree
    have heq : u = v := eq_of_div2_and_mod2 u v hmod hpar
    have hab : a % 2 ^ (N + 2) = b % 2 ^ (N + 2) :=
      eq_of_three_mul_add_one_mod N a b heq
    exact h_disagree hab

/-- Iterated D preserves residues: k applications of D consume k bits.
    Diter k a ≡ Diter k b mod 2^N whenever a ≡ b mod 2^(N+k). -/
lemma Diter_mod_determined (N k a b : ℕ) (h : a % 2 ^ (N + k) = b % 2 ^ (N + k)) :
    Diter k a % 2 ^ N = Diter k b % 2 ^ N :=
  go N k a b h
where
  go : ∀ N k a b, a % 2 ^ (N + k) = b % 2 ^ (N + k) → Diter k a % 2 ^ N = Diter k b % 2 ^ N
  | _, 0, _, _, h => by simp [Diter_zero] at h ⊢; exact h
  | N, k + 1, a, b, h => by
    rw [Diter_succ, Diter_succ]
    have h1 : (N + k) + 1 = N + (k + 1) := add_assoc N k 1
    have h2 : (N + k) + 1 = (N + 1) + k := by rw [h1, add_comm k 1, ← add_assoc]
    have h' : a % 2 ^ (N + 1 + k) = b % 2 ^ (N + 1 + k) := by rwa [← h1, h2] at h
    exact D_mod_determined N (Diter k a) (Diter k b) (go (N + 1) k a b h')

/-- The precision loss of iterated D is exact: k steps consume exactly k bits.
    If a ≡ b mod 2^(N+k) but a ≢ b mod 2^(N+k+1), then
    Diter k a ≡ Diter k b mod 2^N but Diter k a ≢ Diter k b mod 2^(N+1).

    This is the **2-adic expansion property**: the disagreement bit propagates
    downward at exactly one bit per D-step. -/
lemma Diter_mod_exact (N k a b : ℕ)
    (h_agree : a % 2 ^ (N + k) = b % 2 ^ (N + k))
    (h_disagree : a % 2 ^ (N + k + 1) ≠ b % 2 ^ (N + k + 1)) :
    Diter k a % 2 ^ N = Diter k b % 2 ^ N ∧
    Diter k a % 2 ^ (N + 1) ≠ Diter k b % 2 ^ (N + 1) :=
  go N k a b h_agree h_disagree
where
  go : ∀ N k a b, a % 2 ^ (N + k) = b % 2 ^ (N + k) → a % 2 ^ (N + k + 1) ≠ b % 2 ^ (N + k + 1) →
    Diter k a % 2 ^ N = Diter k b % 2 ^ N ∧ Diter k a % 2 ^ (N + 1) ≠ Diter k b % 2 ^ (N + 1)
  | N, 0, a, b, h_agree, h_disagree => by
    simp [Diter_zero] at h_agree h_disagree ⊢
    exact ⟨h_agree, h_disagree⟩
  | N, k + 1, a, b, h_agree, h_disagree => by
    rw [Diter_succ, Diter_succ]
    have heq1 : N + (k + 1) = N + 1 + k := by omega
    have heq2 : N + (k + 1) + 1 = N + 1 + k + 1 := by omega
    have h_agree' : a % 2 ^ (N + 1 + k) = b % 2 ^ (N + 1 + k) := by
      rw [← heq1]
      exact h_agree
    have h_disagree' : a % 2 ^ (N + 1 + k + 1) ≠ b % 2 ^ (N + 1 + k + 1) := by
      rw [← heq2]
      exact h_disagree
    have ih := go (N + 1) k a b h_agree' h_disagree'
    exact D_mod_exact N (Diter k a) (Diter k b) ih.1 ih.2

lemma n_lt_D_n (n : ℕ) (hn : n ≥ 1) : n < D n := by simp [D]; omega

/-- The iterated orbit of any m ≥ 1 stays positive. -/
lemma Diter_pos {m : ℕ} (hm : m ≥ 1) (k : ℕ) : Diter k m ≥ 1 := by
  induction k with
  | zero => exact hm
  | succ k ih => rw [Diter_succ]; linarith [n_lt_D_n (Diter k m) ih]

/-- The orbit of any m ≥ 1 under D is strictly increasing. -/
lemma Diter_strictMono {m : ℕ} (hm : m ≥ 1) : StrictMono (fun k => Diter k m) :=
  strictMono_nat_of_lt_succ fun k => by rw [Diter_succ]; exact n_lt_D_n _ (Diter_pos hm k)

/-- The orbit of any m ≥ 1 never revisits any value. -/
lemma Diter_injective {m : ℕ} (hm : m ≥ 1) : Function.Injective (fun k => Diter k m) :=
  (Diter_strictMono hm).injective

lemma Diter_7_pos (k : ℕ) : Diter k 7 ≥ 1 := Diter_pos (by decide) k

lemma Diter_7_strictMono : StrictMono (fun k => Diter k 7) := Diter_strictMono (by decide)

lemma Diter_7_injective : Function.Injective (fun k => Diter k 7) :=
  Diter_7_strictMono.injective

lemma Diter_add (a b n : ℕ) : Diter (a + b) n = Diter a (Diter b n) :=
  Function.iterate_add_apply D a b n

/-- Pigeonhole gives finite-stretch mod-periodicity: for any N and any desired
    stretch length L, there exist M and T > 0 such that the orbit mod 2^N
    repeats with period T for at least L consecutive steps starting at M.

    Proof: choose precision P = N + L. Among the first 2^P + 1 orbit values,
    pigeonhole gives i < j with Diter i m ≡ Diter j m mod 2^P. Set T = j - i,
    M = i. Then Diter_mod_determined gives mod 2^N agreement for P - N = L steps. -/
lemma Diter_mod_periodic_finite_stretch {m : ℕ} (N L : ℕ) :
    ∃ T > 0, ∃ M, ∀ n ≤ L,
      Diter (M + n + T) m % 2 ^ N = Diter (M + n) m % 2 ^ N := by
  let P := N + L
  let f : Fin (2^P + 1) → Fin (2^P) := fun k => ⟨Diter k.val m % 2^P, Nat.mod_lt _ (by positivity)⟩
  have h_pigeon : ∃ i j : Fin (2^P + 1), i < j ∧ f i = f j := by
    obtain ⟨i, j, hneq, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    rcases lt_trichotomy i j with hlt | heq2 | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact (hneq heq2).elim
    · exact ⟨j, i, hgt, heq.symm⟩
  obtain ⟨i, j, h_lt, h_eq⟩ := h_pigeon
  have h_eq_val : Diter i.val m % 2^P = Diter j.val m % 2^P := by
    have : (f i).val = (f j).val := by rw [h_eq]
    exact this
  use j.val - i.val
  constructor
  · exact Nat.sub_pos_of_lt h_lt
  use i.val
  intro n hn
  have eq_1 : Diter (i.val + n + (j.val - i.val)) m = Diter n (Diter j.val m) := by
    have : i.val + n + (j.val - i.val) = n + j.val := by omega
    rw [this, Diter_add]
  have eq_2 : Diter (i.val + n) m = Diter n (Diter i.val m) := by
    have : i.val + n = n + i.val := by omega
    rw [this, Diter_add]
  rw [eq_1, eq_2]
  have h_eq_mod_Nm : Diter j.val m % 2^(N+n) = Diter i.val m % 2^(N+n) := by
    have hdvd : 2^(N+n) ∣ 2^P := by
      apply Nat.pow_dvd_pow
      omega
    exact mod_eq_of_mod_eq_of_dvd hdvd h_eq_val.symm
  exact Diter_mod_determined N n _ _ h_eq_mod_Nm

/-- The 2-adic expansion property limits how long finite-stretch periodicity lasts.
    If the orbit has a collision at mod 2^(N+L) precision (but not mod 2^(N+L+1)),
    and the collision period is T, then after ⌈(L+1)/T⌉ periods the mod 2^N
    agreement breaks. Specifically: if j·T > L, consecutive period-T blocks
    disagree mod 2^N.

    This shows that pigeonhole-derived periodicity is inherently self-limiting:
    each period consumes T bits of the initial precision surplus, and when the
    surplus is exhausted, periodicity fails. -/
lemma Diter_mod_agreement_degrades {m : ℕ} (N L T M : ℕ) (hT : T ≥ 1)
    (h_agree : Diter M m % 2 ^ (N + L) = Diter (M + T) m % 2 ^ (N + L))
    (h_exact : Diter M m % 2 ^ (N + L + 1) ≠ Diter (M + T) m % 2 ^ (N + L + 1))
    (j : ℕ) (hj : j * T > L) (hjN : (j + 1) * T ≤ N + L) :
    Diter (M + j * T) m % 2 ^ N ≠ Diter (M + (j + 1) * T) m % 2 ^ N := by
  set a := Diter M m
  set b := Diter (M + T) m
  have eq_1 : Diter (M + j * T) m = Diter (j * T) a := by
    have : M + j * T = j * T + M := by omega
    rw [this, Diter_add]
  have eq_2 : Diter (M + (j + 1) * T) m = Diter (j * T) b := by
    have : M + (j + 1) * T = j * T + (M + T) := by
      have : (j + 1) * T = j * T + T := by rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [this, Diter_add]
  rw [eq_1, eq_2]
  set k := j * T
  set N' := N + L - k
  have h_j1T : (j + 1) * T = j * T + T := by rw [Nat.add_mul, Nat.one_mul]
  have hjN_rewritten : k + T ≤ N + L := by
    dsimp [k]
    rw [h_j1T] at hjN
    exact hjN
  have h_N_eq : N' + k = N + L := by
    dsimp [N', k]
    omega
  have h_agree' : a % 2 ^ (N' + k) = b % 2 ^ (N' + k) := by
    rw [h_N_eq]
    exact h_agree
  have h_exact' : a % 2 ^ (N' + k + 1) ≠ b % 2 ^ (N' + k + 1) := by
    have : N' + k + 1 = N + L + 1 := by omega
    rw [this]
    exact h_exact
  have h_exact_k := Diter_mod_exact N' k a b h_agree' h_exact'
  have h_disagree_N_prime : Diter k a % 2 ^ (N' + 1) ≠ Diter k b % 2 ^ (N' + 1) := h_exact_k.2
  intro h_eq_N
  have h_N_prime_le : N' + 1 ≤ N := by
    dsimp [N', k]
    omega
  have h_eq_N_prime : Diter k a % 2 ^ (N' + 1) = Diter k b % 2 ^ (N' + 1) := by
    apply mod_eq_of_mod_eq_of_dvd _ h_eq_N
    apply Nat.pow_dvd_pow _ h_N_prime_le
  exact h_disagree_N_prime h_eq_N_prime

lemma exists_exact_mod_pow_two_agreement {a b : ℕ} (h : a ≠ b) :
    ∃ m : ℕ, a % 2 ^ m = b % 2 ^ m ∧ a % 2 ^ (m + 1) ≠ b % 2 ^ (m + 1) := by
  have h_diff_mod : ∃ k, a % 2 ^ k ≠ b % 2 ^ k := by
    use max a b + 1
    have h1_le : a ≤ max a b := le_max_left a b
    have h1_lt : max a b < 2 ^ (max a b + 1) := by
      have := Nat.lt_two_pow_self (n := max a b + 1)
      omega
    have h1 : a < 2 ^ (max a b + 1) := by omega
    have h2_le : b ≤ max a b := le_max_right a b
    have h2 : b < 2 ^ (max a b + 1) := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    exact h
  have h_zero : a % 2 ^ 0 = b % 2 ^ 0 := by omega
  set S := { k : ℕ | a % 2 ^ k ≠ b % 2 ^ k }
  have h_nonempty : S.Nonempty := h_diff_mod
  set m' := Nat.find h_nonempty
  have hm'_in : m' ∈ S := Nat.find_spec h_nonempty
  have hm'_pos : m' > 0 := by
    by_contra h_le
    have h_zero_eq : m' = 0 := by omega
    rw [h_zero_eq] at hm'_in
    exact hm'_in h_zero
  use m' - 1
  have hm'_eq : m' - 1 + 1 = m' := by omega
  constructor
  · have h_lt : m' - 1 < m' := by omega
    have h_not_in := Nat.find_min h_nonempty h_lt
    change ¬ (a % 2 ^ (m' - 1) ≠ b % 2 ^ (m' - 1)) at h_not_in
    omega
  · rw [hm'_eq]
    change a % 2 ^ m' ≠ b % 2 ^ m' at hm'_in
    exact hm'_in

lemma mod_eq_of_le_pow (a b m n : ℕ) (h : a % 2 ^ n = b % 2 ^ n) (hmn : m ≤ n) :
    a % 2 ^ m = b % 2 ^ m :=
  Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hmn) h

/-- **No collision is self-reinforcing.**
    For any candidate period T ≥ 1 and modulus 2^N with N ≥ 1, the orbit of m ≥ 1
    eventually disagrees at distance T. Equivalently, no period T can sustain
    mod 2^N agreement forever.

    Proof sketch (does NOT require K(3,7) irrationality):
    1. By `Diter_injective`, Diter M m ≠ Diter (M+T) m for T ≥ 1.
    2. Since they are distinct naturals, their 2-adic agreement is finite:
       ∃ M', Diter M m ≡ Diter (M+T) m mod 2^M' but ≢ mod 2^(M'+1).
    3. By `Diter_mod_exact`, each period of T steps degrades the agreement
       by exactly T bits (the 2-adic expansion property).
    4. After ⌈(M'−N+1)/T⌉ periods, the agreement drops below N bits,
       giving mod 2^N disagreement.

    This lemma implies both `parity_not_eventually_periodic_of` and
    `not_Diter_mod_eventually_periodic_of` without any irrationality assumption. -/
lemma Diter_no_self_reinforcing_collision {m : ℕ} (hm : m ≥ 1)
    (N T : ℕ) (hN : N ≥ 1) (hT : T ≥ 1) (M : ℕ) :
    ∃ k ≥ M, Diter k m % 2 ^ N ≠ Diter (k + T) m % 2 ^ N := by
  by_contra h_all
  push_neg at h_all
  set a := Diter M m
  set b := Diter (M + T) m
  have h_neq : a ≠ b := by
    intro h_eq
    have h_inj := Diter_injective hm h_eq
    omega
  obtain ⟨P, h_agree, h_exact⟩ := exists_exact_mod_pow_two_agreement h_neq
  have h_P_ge : P ≥ N := by
    by_contra h_lt
    push_neg at h_lt
    have h_P1_le : P + 1 ≤ N := by omega
    have h_agree_N := h_all M (by omega)
    have h_agree_P1 : Diter M m % 2 ^ (P + 1) = Diter (M + T) m % 2 ^ (P + 1) :=
      mod_eq_of_le_pow _ _ _ _ h_agree_N h_P1_le
    exact h_exact h_agree_P1
  obtain ⟨k, hk⟩ : ∃ k, k = P - N + 1 := ⟨P - N + 1, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N', N' = N - 1 := ⟨N - 1, rfl⟩
  have h_P_eq : N' + k = P := by omega
  have h_agree' : a % 2 ^ (N' + k) = b % 2 ^ (N' + k) := by
    rw [h_P_eq]
    exact h_agree
  have h_exact' : a % 2 ^ (N' + k + 1) ≠ b % 2 ^ (N' + k + 1) := by
    have : N' + k + 1 = P + 1 := by omega
    rw [this]
    exact h_exact
  have h_exact_k := Diter_mod_exact N' k a b h_agree' h_exact'
  have h_disagree : Diter k a % 2 ^ (N' + 1) ≠ Diter k b % 2 ^ (N' + 1) := h_exact_k.2
  have h_N_prime_eq : N' + 1 = N := by omega
  rw [h_N_prime_eq] at h_disagree
  have h_Diter_a : Diter k a = Diter (M + k) m := by
    have : M + k = k + M := by omega
    rw [this, Diter_add]
  have h_Diter_b : Diter k b = Diter (M + k + T) m := by
    have : M + k + T = k + (M + T) := by omega
    rw [this, Diter_add]
  rw [h_Diter_a, h_Diter_b] at h_disagree
  have h_all_k : Diter (M + k) m % 2 ^ N = Diter (M + k + T) m % 2 ^ N := h_all (M + k) (by omega)
  exact h_disagree h_all_k

/-- The parity sequence of Diter starting from any m ≥ 1 is fundamentally not eventually periodic.
    This is equivalent to the irrationality of the Odlyzko-Wilf constant K(3). -/
lemma parity_not_eventually_periodic_of {m : ℕ} (hm : m ≥ 1) :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) m % 2 = Diter k m % 2 := by
  rintro ⟨T, hT, M, h_all⟩
  have h_col := Diter_no_self_reinforcing_collision hm 1 T (by decide) hT M
  obtain ⟨k, hk_ge, hk_neq⟩ := h_col
  have h_eq := h_all k hk_ge
  rw [pow_one] at hk_neq
  exact hk_neq h_eq.symm

/-- The sequence `Diter k m` modulo `2^N` is never eventually periodic
    for any `m ≥ 1` and `N ≥ 1`. -/
lemma not_Diter_mod_eventually_periodic_of {m : ℕ} (hm : m ≥ 1) (N : ℕ) (hN : N ≥ 1) :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) m % 2 ^ N = Diter k m % 2 ^ N := by
  rintro ⟨T, hT, M, h_all⟩
  have h_col := Diter_no_self_reinforcing_collision hm N T hN hT M
  obtain ⟨k, hk_ge, hk_neq⟩ := h_col
  have h_eq := h_all k hk_ge
  exact hk_neq h_eq.symm

/-- The parity sequence of Diter starting from 7 is not eventually periodic. -/
lemma parity_not_eventually_periodic :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 = Diter k 7 % 2 :=
  parity_not_eventually_periodic_of (by decide)

/-- The sequence `Diter k 7` modulo `2^N` is never eventually periodic for any `N ≥ 1`. -/
lemma not_Diter_mod_eventually_periodic (N : ℕ) (hN : N ≥ 1) :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 ^ N = Diter k 7 % 2 ^ N :=
  not_Diter_mod_eventually_periodic_of (by decide) N hN

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
