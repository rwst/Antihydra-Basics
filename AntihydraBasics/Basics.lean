import Mathlib

/-- `H n = ⌊3 * n / 2⌋` for `n : ℕ`. -/
def H (n : ℕ) : ℕ := 3 * n / 2

/-- `H' n = ⌈3 * n / 2⌉` for `n : ℕ`. -/
def H' (n : ℕ) : ℕ := (3 * n + 1) / 2

/-- When `n` is even, `H n = 3 * n / 2` (exact, no remainder). -/
lemma H_even {n : ℕ} (_ : Even n) : H n = 3 * n / 2 := rfl

/-- When `n` is odd, `H n = (3 * n - 1) / 2`. -/
lemma H_odd {n : ℕ} (h : Odd n) : H n = (3 * n - 1) / 2 := by
  obtain ⟨k, hk⟩ := h
  subst hk
  simp [H]
  omega

/-- When `n` is even, `H' n = 3 * n / 2` (same as `H n`). -/
lemma H'_even {n : ℕ} (h : Even n) : H' n = 3 * n / 2 := by
  obtain ⟨k, hk⟩ := h
  subst hk
  simp [H']
  omega

/-- When `n` is odd, `H' n = (3 * n + 1) / 2` (exact, no remainder). -/
lemma H'_odd {n : ℕ} (_ : Odd n) : H' n = (3 * n + 1) / 2 := rfl

/-- Closed-form formula: `H n = (6n - 1 + (-1)^n) / 4` as integers.
Equivalently, `H n = 3n/2` when `n` is even, `(3n-1)/2` when `n` is odd. -/
lemma H_formula (n : ℕ) : (H n : ℤ) = (6 * n - 1 + (-1 : ℤ)^n) / 4 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [Even.neg_one_pow he]
    obtain ⟨k, hk⟩ := he; subst hk
    simp [H]; omega
  · rw [Odd.neg_one_pow ho]
    obtain ⟨k, hk⟩ := ho; subst hk
    simp [H]; omega

/-- Closed-form formula: `H' n = (6n + 1 - (-1)^n) / 4` as integers.
Equivalently, `H' n = 3n/2` when `n` is even, `(3n+1)/2` when `n` is odd. -/
lemma H'_formula (n : ℕ) : (H' n : ℤ) = (6 * n + 1 - (-1 : ℤ)^n) / 4 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [Even.neg_one_pow he]
    obtain ⟨k, hk⟩ := he; subst hk
    simp [H']; omega
  · rw [Odd.neg_one_pow ho]
    obtain ⟨k, hk⟩ := ho; subst hk
    simp [H']; omega

/-- `Hiter i n = H^i(n)`: apply `H` exactly `i` times starting from `n`,
using `Function.iterate`.  The two defining equations are:
- `Hiter_zero : Hiter 0 n = n`
- `Hiter_succ : Hiter (i + 1) n = H (Hiter i n)` -/
def Hiter (i : ℕ) (n : ℕ) : ℕ := H^[i] n

@[simp] lemma Hiter_zero (n : ℕ) : Hiter 0 n = n := rfl


@[simp] lemma Hiter_succ (i : ℕ) (n : ℕ) : Hiter (i + 1) n = H (Hiter i n) := by
  simp [Hiter, Function.iterate_succ_apply']

/-- `Diter i n = (H')^i(n)`: apply `H'` exactly `i` times starting from `n`,
using `Function.iterate`.  The two defining equations are:
- `Diter_zero : Diter 0 n = n`
- `Diter_succ : Diter (i + 1) n = H' (Diter i n)` -/
def Diter (i : ℕ) (n : ℕ) : ℕ := H'^[i] n

@[simp] lemma Diter_zero (n : ℕ) : Diter 0 n = n := rfl

@[simp] lemma Diter_succ (i : ℕ) (n : ℕ) : Diter (i + 1) n = H' (Diter i n) := by
  simp [Diter, Function.iterate_succ_apply']

/-- Key helper: `H(m + 1) = H'(m) + 1` for all `m : ℕ`. -/
lemma H_succ_eq_H'_succ (m : ℕ) : H (m + 1) = H' m + 1 := by
  simp [H, H']; omega

/-- Generalisation: `H^i(n + 1) = (H')^i(n) + 1` for all `i n : ℕ`.
The previous `Hiter_two_eq_Diter_one_succ` is the special case `n = 1`. -/
lemma Hiter_succ_eq_Diter_succ (i n : ℕ) : Hiter i (n + 1) = Diter i n + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Hiter_succ, Diter_succ, ih]
    exact H_succ_eq_H'_succ _
