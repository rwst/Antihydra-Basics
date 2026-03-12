import Mathlib.Analysis.Normed.Ring.Lemmas

open BigOperators

/-- `C n = ⌊3 * n / 2⌋` for `n : ℕ`. -/
def C (n : ℕ) : ℕ := 3 * n / 2

/-- `' n = ⌈3 * n / 2⌉` for `n : ℕ`. -/
def D (n : ℕ) : ℕ := (3 * n + 1) / 2

/-- When `n` is even, `C n = 3 * n / 2` (exact, no remainder). -/
lemma C_even {n : ℕ} (_ : Even n) : C n = 3 * n / 2 := rfl

/-- When `n` is odd, `C n = (3 * n - 1) / 2`. -/
lemma C_odd {n : ℕ} (h : Odd n) : C n = (3 * n - 1) / 2 := by
  obtain ⟨k, hk⟩ := h
  subst hk
  simp [C]
  omega

/-- When `n` is even, `D n = 3 * n / 2` (same as `C n`). -/
lemma D_even {n : ℕ} (h : Even n) : D n = 3 * n / 2 := by
  obtain ⟨k, hk⟩ := h
  subst hk
  simp [D]
  omega

/-- When `n` is odd, `D n = (3 * n + 1) / 2` (exact, no remainder). -/
lemma D_odd {n : ℕ} (_ : Odd n) : D n = (3 * n + 1) / 2 := rfl

/-- Closed-form formula: `C n = (6n - 1 + (-1)^n) / 4` as integers.
Equivalently, `C n = 3n/2` when `n` is even, `(3n-1)/2` when `n` is odd. -/
lemma C_formula (n : ℕ) : (C n : ℤ) = (6 * n - 1 + (-1 : ℤ)^n) / 4 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [Even.neg_one_pow he]
    obtain ⟨k, hk⟩ := he; subst hk
    simp [C]; omega
  · rw [Odd.neg_one_pow ho]
    obtain ⟨k, hk⟩ := ho; subst hk
    simp [C]; omega

/-- Closed-form formula: `D n = (6n + 1 - (-1)^n) / 4` as integers.
Equivalently, `D n = 3n/2` when `n` is even, `(3n+1)/2` when `n` is odd. -/
lemma D_formula (n : ℕ) : (D n : ℤ) = (6 * n + 1 - (-1 : ℤ)^n) / 4 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [Even.neg_one_pow he]
    obtain ⟨k, hk⟩ := he; subst hk
    simp [D]; omega
  · rw [Odd.neg_one_pow ho]
    obtain ⟨k, hk⟩ := ho; subst hk
    simp [D]; omega

/-- `Citer i n = C^i(n)`: apply `C` exactly `i` times starting from `n`,
using `Function.iterate`.  The two defining equations are:
- `Citer_zero : Citer 0 n = n`
- `Citer_succ : Citer (i + 1) n = C (Citer i n)` -/
def Citer (i : ℕ) (n : ℕ) : ℕ := C^[i] n

@[simp] lemma Citer_zero (n : ℕ) : Citer 0 n = n := rfl


@[simp] lemma Citer_succ (i : ℕ) (n : ℕ) : Citer (i + 1) n = C (Citer i n) := by
  simp [Citer, Function.iterate_succ_apply']

/-- `Diter i n = (D)^i(n)`: apply `D` exactly `i` times starting from `n`,
using `Function.iterate`.  The two defining equations are:
- `Diter_zero : Diter 0 n = n`
- `Diter_succ : Diter (i + 1) n = D (Diter i n)` -/
def Diter (i : ℕ) (n : ℕ) : ℕ := D^[i] n

@[simp] lemma Diter_zero (n : ℕ) : Diter 0 n = n := rfl

@[simp] lemma Diter_succ (i : ℕ) (n : ℕ) : Diter (i + 1) n = D (Diter i n) := by
  simp [Diter, Function.iterate_succ_apply']

/-- Key helper: `C(m + 1) = D(m) + 1` for all `m : ℕ`. -/
lemma C_succ_eq_D_succ (m : ℕ) : C (m + 1) = D m + 1 := by
  simp [C, D]; omega

/-- Generalisation: `C^i(n + 1) = (D)^i(n) + 1` for all `i n : ℕ`.
The previous `Citer_two_eq_Diter_one_succ` is the special case `n = 1`. -/
lemma Citer_succ_eq_Diter_succ (i n : ℕ) : Citer i (n + 1) = Diter i n + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Citer_succ, Diter_succ, ih]
    exact C_succ_eq_D_succ _

def A (ab : ℕ × ℕ) : ℕ × ℕ :=
  let (a, b) := ab
  let n := a / 2
  if a % 2 == 0 then (3 * n + 2, b + 2)
  else              (3 * n + 3, b - 1)

-- i-th iterate of A
def Aiter (i : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := A^[i] ab

/-- A applied to (c - 4, b) where c = C-value gives first component C(c) - 4. -/
-- Helper: unfold BEq for Nat
@[simp] lemma Nat.beq_eq_decide' (a b : ℕ) : (a == b) = decide (a = b) := by
  simp [BEq.beq]

lemma A_fst (c b : ℕ) (hc : c ≥ 4) :
    (A (c - 4, b)).1 = C c - 4 := by
  unfold A; simp [C]
  split <;> omega

/-- C n ≥ n for n ≥ 2. -/
lemma C_ge_self (n : ℕ) (h : n ≥ 2) : C n ≥ n := by
  simp [C]; omega

/-- Citer i 8 ≥ 8 for all i. -/
lemma Citer_ge_8 (i : ℕ) : Citer i 8 ≥ 8 := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [Citer_succ]
    calc C (Citer i 8) ≥ Citer i 8 := C_ge_self _ (by omega)
    _ ≥ 8 := ih

/-- First component of A depends only on the first input. -/
lemma A_fst_only (a b b' : ℕ) : (A (a, b)).1 = (A (a, b')).1 := by
  unfold A; simp; split <;> rfl

/-- First component relation: (Aiter i (8, 2)).1 = Citer (i+1) 8 - 4. -/
lemma Aiter_fst_eq (i : ℕ) : (Aiter i (8, 2)).1 = Citer (i + 1) 8 - 4 := by
  induction i with
  | zero => simp [Aiter, Citer_succ, C]
  | succ i ih =>
    simp only [Aiter, Function.iterate_succ_apply']
    have ih' : (A^[i] (8, 2)).1 = Citer (i + 1) 8 - 4 := ih
    have h1 : (A (A^[i] (8, 2))).1 = (A ((A^[i] (8, 2)).1, 0)).1 := A_fst_only _ _ _
    rw [h1, ih', A_fst _ _ (by have := Citer_ge_8 (i + 1); omega)]
    simp [Citer_succ]

/-- Parity equivalence for first component. -/
lemma Aiter_fst_parity (i : ℕ) :
    (Aiter i (8, 2)).1 % 2 = 1 ↔ Citer (i + 1) 8 % 2 = 1 := by
  rw [Aiter_fst_eq]
  have := Citer_ge_8 (i + 1)
  omega

/-- Size equivalence for first component. -/
lemma Aiter_fst_div2 (i : ℕ) :
    (Aiter i (8, 2)).1 / 2 ≥ 1 ↔ Citer (i + 1) 8 ≥ 6 := by
  rw [Aiter_fst_eq]
  have := Citer_ge_8 (i + 1)
  omega

/-- Second component as integer: b_int i = 2 + 2i - 3 * Psum(i). -/
noncomputable def b_int (i : ℕ) : ℤ :=
  2 + 2 * (i : ℤ) - 3 * (∑ j ∈ Finset.range (i + 1), ((Citer j 8 : ℤ) % 2))

/-- Second component of A: step rule. -/
lemma A_snd (a b : ℕ) :
    (A (a, b)).2 = if a % 2 == 0 then b + 2 else b - 1 := by
  unfold A; simp; split <;> rfl

/-- Parity of (c - 4) matches parity of c for c ≥ 4. -/
lemma sub_four_mod2 (c : ℕ) (hc : c ≥ 4) : (c - 4) % 2 = c % 2 := by omega

lemma b_int_step (i : ℕ) :
    b_int (i + 1) = b_int i + 2 - 3 * ((Citer (i + 1) 8 : ℤ) % 2) := by
  simp only [b_int, Finset.sum_range_succ]; push_cast; ring

/-- The formula b_int tracks the ℕ value of the second component,
provided no truncation occurs (a odd → b ≥ 1). -/
lemma Aiter_snd_eq_b_int (i : ℕ)
    (h : ∀ j < i, (Aiter j (8, 2)).1 % 2 = 1 → (Aiter j (8, 2)).2 ≥ 1) :
    ((Aiter i (8, 2)).2 : ℤ) = b_int i := by
  induction i with
  | zero =>
    simp [Aiter, b_int, Citer_zero]
  | succ i ih =>
    have hprev : ∀ j < i, (Aiter j (8, 2)).1 % 2 = 1 → (Aiter j (8, 2)).2 ≥ 1 :=
      fun j hj => h j (by omega)
    have ih' := ih hprev
    have hfst_mod : (Aiter i (8, 2)).1 % 2 = Citer (i + 1) 8 % 2 := by
      have := Aiter_fst_eq i; have := Citer_ge_8 (i + 1); omega
    have step : Aiter (i + 1) (8, 2) = A (Aiter i (8, 2)) := by
      simp [Aiter, Function.iterate_succ_apply']
    rw [step, A_snd, b_int_step]
    split
    · rename_i hbeq; simp at hbeq
      have : ((Citer (i + 1) 8 : ℤ) % 2) = 0 := by exact_mod_cast (by omega : Citer (i + 1) 8 % 2 = 0)
      push_cast; linarith
    · rename_i hbeq; simp at hbeq
      have hc' : ((Citer (i + 1) 8 : ℤ) % 2) = 1 := by
        exact_mod_cast (by omega : Citer (i + 1) 8 % 2 = 1)
      have hpos : (Aiter i (8, 2)).2 ≥ 1 := h i (by omega) (by omega)
      have : ((↑((Aiter i (8, 2)).2 - 1) : ℤ)) = ↑(Aiter i (8, 2)).2 - 1 := by omega
      rw [this]; linarith

/-- Cast: ℤ-sum of parities equals ℕ-sum of parities. -/
lemma psum_cast (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), ((Citer j 8 : ℤ) % 2)) =
    ↑(∑ j ∈ Finset.range (i + 1), (Citer j 8) % 2) := by
  norm_cast

lemma b_int_eq_zero_iff (i : ℕ) :
    b_int i = 0 ↔ (i % 3 = 2 ∧
      (∑ j ∈ Finset.range (i + 1), (Citer j 8) % 2) = 2 * (i + 1) / 3) := by
  set S := ∑ j ∈ Finset.range (i + 1), (Citer j 8) % 2
  simp only [b_int]
  rw [psum_cast]
  constructor
  · intro h
    have h3S : 3 * S = 2 * (i + 1) := by omega
    constructor
    · omega
    · omega
  · intro ⟨hmod, hsum⟩
    have h3S : 3 * S = 2 * (i + 1) := by omega
    omega

/-- The /2 ≥ 1 condition is always satisfied. -/
lemma Aiter_fst_div2_always (i : ℕ) : (Aiter i (8, 2)).1 / 2 ≥ 1 := by
  rw [Aiter_fst_eq]; have := Citer_ge_8 (i + 1); omega

/-- The ≥ 6 condition is always satisfied. -/
lemma Citer_succ_ge_6 (i : ℕ) : Citer (i + 1) 8 ≥ 6 := by
  have := Citer_ge_8 (i + 1); omega

lemma Aiter_8_2_halt_iff_Citer_8_halt :
  (∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0) ↔
  (∃ i, (Citer (i + 1) 8) % 2 = 1 ∧ (Citer (i + 1) 8) ≥ 6 ∧ i % 3 = 2 ∧
    (∑ j ∈ Finset.range (i + 1), (Citer j 8) % 2) = 2 * (i + 1) / 3) := by
  constructor
  · -- Forward: LHS → RHS
    rintro ⟨i, hpar, _, hb0⟩
    -- Take minimum i₀ with a odd ∧ b = 0
    have hexists : ∃ j, (Aiter j (8, 2)).1 % 2 = 1 ∧ (Aiter j (8, 2)).2 = 0 := ⟨i, hpar, hb0⟩
    let P := fun j => (Aiter j (8, 2)).1 % 2 = 1 ∧ (Aiter j (8, 2)).2 = 0
    have hdec : DecidablePred P := inferInstance
    let i₀ := Nat.find hexists
    have hi₀ : P i₀ := Nat.find_spec hexists
    have hmin : ∀ j < i₀, ¬P j := fun j hj => Nat.find_min hexists hj
    -- No truncation before i₀: if a_j odd then b_j ≥ 1
    have hnotrunc : ∀ j < i₀, (Aiter j (8, 2)).1 % 2 = 1 → (Aiter j (8, 2)).2 ≥ 1 := by
      intro j hj hodd
      by_contra h
      push_neg at h
      have : (Aiter j (8, 2)).2 = 0 := by omega
      exact hmin j hj ⟨hodd, this⟩
    -- Apply formula at i₀
    have hbint : ((Aiter i₀ (8, 2)).2 : ℤ) = b_int i₀ := Aiter_snd_eq_b_int i₀ hnotrunc
    have hbint0 : b_int i₀ = 0 := by
      have := hi₀.2; rw [this] at hbint; exact_mod_cast hbint.symm
    -- Extract conditions from b_int = 0
    rw [b_int_eq_zero_iff] at hbint0
    refine ⟨i₀, ?_, Citer_succ_ge_6 i₀, hbint0.1, hbint0.2⟩
    exact (Aiter_fst_parity i₀).mp hi₀.1
  · -- Backward: RHS → LHS
    rintro ⟨i, hpar, _, hmod, hsum⟩
    -- From sum condition, b_int i = 0
    have hbint0 : b_int i = 0 := (b_int_eq_zero_iff i).mpr ⟨hmod, hsum⟩
    -- Either no truncation up to i, or there was an earlier LHS witness
    by_cases hnotrunc : ∀ j < i, (Aiter j (8, 2)).1 % 2 = 1 → (Aiter j (8, 2)).2 ≥ 1
    · -- No truncation: b_i = b_int i = 0
      have hbint := Aiter_snd_eq_b_int i hnotrunc
      rw [hbint0] at hbint
      have hb0 : (Aiter i (8, 2)).2 = 0 := by exact_mod_cast hbint
      exact ⟨i, (Aiter_fst_parity i).mpr hpar, Aiter_fst_div2_always i, hb0⟩
    · -- Truncation occurred: ∃ j < i with a_j odd ∧ b_j = 0
      push_neg at hnotrunc
      obtain ⟨j, hji, hodd, hb⟩ := hnotrunc
      have hb0 : (Aiter j (8, 2)).2 = 0 := by omega
      exact ⟨j, hodd, Aiter_fst_div2_always j, hb0⟩

lemma Aiter_8_2_halt_iff_Diter_7_halt :
  (∃ i, (Aiter i (8, 2)).1 % 2 = 1 ∧ (Aiter i (8, 2)).1 / 2 ≥ 1 ∧ (Aiter i (8, 2)).2 = 0) ↔
  (∃ i, (Diter (i + 1) 7) % 2 = 0 ∧ (Diter (i + 1) 7) ≥ 5 ∧ i % 3 = 2 ∧
    (∑ j ∈ Finset.range (i + 1), (Diter j 7) % 2) = (i + 1) / 3) := by
  rw [Aiter_8_2_halt_iff_Citer_8_halt]
  simp only [show (8 : ℕ) = 7 + 1 from rfl, Citer_succ_eq_Diter_succ]
  constructor <;> rintro ⟨i, h1, h2, h3, h4⟩ <;> refine ⟨i, by omega, by omega, h3, ?_⟩
  · -- (Diter j 7 + 1) % 2 sum = 2*(i+1)/3  →  Diter j 7 % 2 sum = (i+1)/3
    -- Key: (n+1)%2 + n%2 = 1, so the two sums add to (i+1)
    have hsum_add : ∀ n, (∑ j ∈ Finset.range (n + 1), (Diter j 7 + 1) % 2) +
        (∑ j ∈ Finset.range (n + 1), Diter j 7 % 2) = n + 1 := by
      intro n; rw [← Finset.sum_add_distrib]; simp_rw [show ∀ j, (Diter j 7 + 1) % 2 + Diter j 7 % 2 = 1 from by omega]
      simp [Finset.sum_const, Finset.card_range]
    have := hsum_add i; omega
  · have hsum_add : ∀ n, (∑ j ∈ Finset.range (n + 1), (Diter j 7 + 1) % 2) +
        (∑ j ∈ Finset.range (n + 1), Diter j 7 % 2) = n + 1 := by
      intro n; rw [← Finset.sum_add_distrib]; simp_rw [show ∀ j, (Diter j 7 + 1) % 2 + Diter j 7 % 2 = 1 from by omega]
      simp [Finset.sum_const, Finset.card_range]
    have := hsum_add i; omega

--#min_imports
