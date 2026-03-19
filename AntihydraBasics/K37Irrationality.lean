import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.Real.Irrational
import AntihydraBasics.Constant

/-- For `q = 3`, the error term `E(3, x)` is simply `x % 2` for `x ≥ 1`. -/
private lemma E_three_eq (x : ℕ) (hx : x ≥ 1) : E 3 x = x % 2 := by
  simp only [E]
  have h1 : 3 - 2 = 1 := rfl
  have h2 : 3 - 1 = 2 := rfl
  rw [h1, h2]
  omega

/-- For `q = 3`, the step-wise error `e_step` is `(D^k(n) % 2) / 2`. -/
private lemma e_step_three_eq (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    e_step 3 n k = ((Diter k n % 2 : ℕ) : ℝ) / 2 := by
  have h_Diter : Diter' k 3 n = Diter k n := Diter'_three k n
  simp only [e_step, h_Diter]
  have hDpos : Diter k n ≥ 1 := by
    rw [← h_Diter]
    exact Diter'_pos k 3 n (by decide) hn
  rw [E_three_eq _ hDpos]
  congr 1
  norm_num


/-- The `j`-th term of the series for the Odlyzko-Wilf constant `K(3, n)`. -/
lemma K_summand_three_eq (n : ℕ) (j : ℕ) (hn : n ≥ 1) :
    K_summand 3 n j = ((Diter j n % 2 : ℕ) : ℝ) / (2 * (3/2 : ℝ) ^ (j + 1)) := by
  simp only [K_summand]
  rw [e_step_three_eq n j hn]
  have hα : α 3 = 3 / 2 := by norm_num [α]
  rw [hα]
  ring

/-- Each K_summand 3 7 j is rational (not irrational). -/
lemma K_summand_three_7_not_irrational (j : ℕ) : ¬ Irrational (K_summand 3 7 j) := by
  rw [K_summand_three_eq 7 j (by decide)]
  have : ((Diter j 7 % 2 : ℕ) : ℝ) / (2 * (3/2 : ℝ) ^ (j + 1)) =
      ↑((↑(Diter j 7 % 2) : ℚ) / (2 * (3/2 : ℚ) ^ (j + 1))) := by push_cast; ring
  rw [this]; exact Rat.not_irrational _

/-- Finite sums of non-irrational reals are non-irrational. -/
lemma finset_sum_not_irrational {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, ¬ Irrational (f i)) : ¬ Irrational (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [not_irrational_zero]
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact fun h => h.add_cases.elim (hf a (Finset.mem_cons_self a s))
      (ih fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))

/-- Summation formula for a sequence that becomes geometric after `M` steps
    with period `T` and ratio `(2/3)^T`. -/
lemma sum_periodic_shift (f : ℕ → ℝ) (T M : ℕ) (hT : T > 0)
    (h_per : ∀ j, f (j + T + M) = f (j + M) * (2/3 : ℝ)^T)
    (h_sum : Summable f) :
    ∑' j, f j = (∑ j ∈ Finset.range M, f j) +
      (∑ j ∈ Finset.range T, f (j + M)) / (1 - (2/3 : ℝ)^T) := by
  set r := (2/3 : ℝ) ^ T with hr_def
  have hr_lt : r < 1 := by
    calc r ≤ (2/3 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
      _ = 2/3 := pow_one _
      _ < 1 := by norm_num
  have h1mr : (1 : ℝ) - r ≠ 0 := ne_of_gt (by linarith)
  -- Summability of shifted sequences
  have hfM_sum : Summable (fun k => f (k + M)) :=
    h_sum.comp_injective (add_left_injective M)
  have hfTM_sum : Summable (fun k => f (k + T + M)) :=
    hfM_sum.comp_injective (add_left_injective T)
  -- Split at M: ∑' j, f j = ∑_{j<M} f j + ∑' k, f(k+M)
  have hsplit_M : ∑' j, f j = (∑ j ∈ Finset.range M, f j) + ∑' k, f (k + M) :=
    h_sum.hasSum.unique hfM_sum.hasSum.sum_range_add
  -- Split tail at T: ∑' k, f(k+M) = ∑_{t<T} f(t+M) + ∑' k, f(k+T+M)
  have hsplit_T : ∑' k, f (k + M) = (∑ t ∈ Finset.range T, f (t + M)) + ∑' k, f (k + T + M) :=
    hfM_sum.hasSum.unique hfTM_sum.hasSum.sum_range_add
  -- Tail = r * total: ∑' k, f(k+T+M) = r * ∑' k, f(k+M)
  have htail_eq : ∑' k, f (k + T + M) = r * ∑' k, f (k + M) := by
    simp_rw [h_per, tsum_mul_right, mul_comm]
  -- Self-referential equation: S = A + r * S, solve for S = A / (1 - r)
  have hS : ∑' k, f (k + M) = (∑ t ∈ Finset.range T, f (t + M)) / (1 - r) := by
    rw [eq_div_iff h1mr]; nlinarith [hsplit_T, htail_eq]
  rw [hsplit_M, hS]

/-- If the parity sequence of Diter is eventually periodic, then the Odlyzko-Wilf constant K(3,7) is rational. -/
lemma parity_periodic_implies_K37_rational (T M : ℕ) (hT : T > 0)
    (h_per : ∀ k ≥ M, Diter (k + T) 7 % 2 = Diter k 7 % 2) : ¬ Irrational (K_const 3 7) := by
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
  -- All parts are rational, so the whole expression is not irrational
  rw [h_K_eval]
  have h1 : ¬ Irrational (∑ j ∈ Finset.range M, f j) :=
    finset_sum_not_irrational fun i _ => K_summand_three_7_not_irrational i
  have h2 : ¬ Irrational (∑ j ∈ Finset.range T, f (j + M)) :=
    finset_sum_not_irrational fun i _ => K_summand_three_7_not_irrational (i + M)
  have h3 : ¬ Irrational (1 - (2/3 : ℝ) ^ T) := by
    have : (1 : ℝ) - (2/3 : ℝ) ^ T = ↑((1 : ℚ) - (2/3 : ℚ) ^ T) := by push_cast; ring
    rw [this]; exact Rat.not_irrational _
  intro h_irr
  exact h_irr.add_cases.elim (Nat.not_irrational 7)
    (fun h_rest => h_rest.add_cases.elim h1 (fun h4 => h4.div_cases.elim h2 h3))

/-- From the non-periodicity of the parity sequence follows the irrationality of K(3,7). -/
lemma Diter_nonperiodic_implies_K37_irrational
    (h_nonper : ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 = Diter k 7 % 2) :
    Irrational (K_const 3 7) := by sorry

/-- The Odlyzko-Wilf constant K(3,7) is irrational. -/
lemma K37_irrational :
    Irrational (K_const 3 7) := by sorry

/-- The parity sequence of Diter is fundamentally not eventually periodic,
    assuming the irrationality of the Odlyzko-Wilf constant K(3,7). -/
lemma parity_not_eventually_periodic (h_irr : Irrational (K_const 3 7)) :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 = Diter k 7 % 2 := by
  intro ⟨T, hT, M, hM⟩
  exact (parity_periodic_implies_K37_rational T M hT hM) h_irr

/-- Generalizes the parity non-periodicity: the sequence `Diter k 7` modulo `2^N`
    is never eventually periodic for any `N ≥ 1`, assuming K(3,7) is irrational. -/
lemma not_Diter_mod_eventually_periodic (h_irr : Irrational (K_const 3 7)) (N : ℕ) (hN : N ≥ 1) :
    ¬ ∃ T > 0, ∃ M, ∀ k ≥ M, Diter (k + T) 7 % 2 ^ N = Diter k 7 % 2 ^ N := by
  intro ⟨T, hT, M, hM⟩
  apply parity_not_eventually_periodic h_irr
  use T, hT, M
  intro k hk
  have h := hM k hk
  have h_dvd : 2 ∣ 2 ^ N := dvd_pow_self 2 (by omega)
  have h_modeq : Diter (k + T) 7 ≡ Diter k 7 [MOD 2 ^ N] := h
  have h_mod2 : Diter (k + T) 7 ≡ Diter k 7 [MOD 2] := h_modeq.of_dvd h_dvd
  exact h_mod2
