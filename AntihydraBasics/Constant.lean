import AntihydraBasics.Basics
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

open Real

/-- One step of the generalised iteration: `⌈q/(q-1) * n⌉ = (q * n + q - 2) / (q - 1)` in `ℕ`.
    Requires `q ≥ 2` for `q - 1 > 0`. -/
def Dstep (q : ℕ) (n : ℕ) : ℕ := (q * n + q - 2) / (q - 1)

/-- `Diter' k q n` iterates `Dstep q` exactly `k` times starting from `n`.
    This is `D_k^{(q)}` from the paper (ignoring their fixed start value `D_0 = 1`). -/
def Diter' (k : ℕ) (q : ℕ) (n : ℕ) : ℕ := (Dstep q)^[k] n

@[simp] lemma Diter'_zero (q n : ℕ) : Diter' 0 q n = n := rfl

@[simp] lemma Diter'_succ (k q n : ℕ) :
    Diter' (k + 1) q n = Dstep q (Diter' k q n) := by
  simp [Diter', Function.iterate_succ_apply']

/-- When `q = 3`, `Dstep 3 = D` (i.e., `⌈3/2 * n⌉`). -/
lemma Dstep_three (n : ℕ) : Dstep 3 n = D n := by simp [Dstep, D]

/-- When `q = 3`, `Diter'` coincides with `Diter`. -/
lemma Diter'_three (k n : ℕ) : Diter' k 3 n = Diter k n := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Diter'_succ, Dstep_three, Diter_succ, ih]

-- ══════════════════════════════════════════════════════════════════════
-- Phase 1: Purely Natural Arithmetic
-- ══════════════════════════════════════════════════════════════════════

/-- Error term: `E(q, n) = q - 2 - ((n - 1) % (q - 1))` for `n ≥ 1`.
    For `n = 0`, we define `E(q, 0) = q - 2` (matching the ceiling formula). -/
def E (q : ℕ) (n : ℕ) : ℕ := q - 2 - ((n - 1) % (q - 1))

/-- E is bounded above by q - 2. -/
lemma E_le (q n : ℕ) (hq : q ≥ 2) : E q n ≤ q - 2 := by
  simp only [E]; omega

/-- Exact division lemma: Dstep q n * (q - 1) = q * n + E(q, n) for q ≥ 2, n ≥ 1. -/
lemma Dstep_exact (q n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    Dstep q n * (q - 1) = q * n + E q n := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Dstep, E, show q' + 2 - 2 = q' from by omega,
    show q' + 2 - 1 = q' + 1 from by omega, show n' + 1 - 1 = n' from by omega]
  -- Simplify the numerator: (q'+2)*(n'+1) + (q'+2) - 2 = (q'+2)*(n'+1) + q'
  have hnum : (q' + 2) * (n' + 1) + (q' + 2) - 2 = (q' + 2) * (n' + 1) + q' := by omega
  rw [hnum]
  -- Now goal: ((q'+2)*(n'+1) + q') / (q'+1) * (q'+1) = (q'+2)*(n'+1) + (q' - n' % (q'+1))
  -- Decomposition: (q'+2)*(n'+1) + q' = (q'+1)*(n'+2) + n'
  have hdecomp : (q' + 2) * (n' + 1) + q' = (q' + 1) * (n' + 2) + n' := by ring
  have hmod : ((q' + 2) * (n' + 1) + q') % (q' + 1) = n' % (q' + 1) := by
    rw [hdecomp, Nat.mul_add_mod]
  have hdm := Nat.div_add_mod ((q' + 2) * (n' + 1) + q') (q' + 1)
  rw [hmod] at hdm
  have hr : n' % (q' + 1) ≤ q' := by have := Nat.mod_lt n' (by omega : q' + 1 > 0); omega
  rw [Nat.mul_comm] at hdm
  -- Abstract nonlinear terms to make omega work
  generalize (q' + 2) * (n' + 1) = P at hdm ⊢
  generalize n' % (q' + 1) = r at hdm hr ⊢
  generalize (P + q') / (q' + 1) * (q' + 1) = Y at hdm ⊢
  omega

/-- Dstep preserves positivity: n ≥ 1 → Dstep q n ≥ 1 for q ≥ 2. -/
lemma Dstep_pos (q n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) : Dstep q n ≥ 1 := by
  have h := Dstep_exact q n hq hn
  -- Dstep q n * (q - 1) = q * n + E q n ≥ q * n ≥ 2
  -- So Dstep q n * (q - 1) ≥ 1, hence Dstep q n ≥ 1
  by_contra hlt; push_neg at hlt
  have : Dstep q n = 0 := by omega
  rw [this] at h; simp at h
  -- h : q * n + E q n = 0, but q * n ≥ 2
  have : q * n ≥ 2 * 1 := Nat.mul_le_mul hq hn
  omega

/-- Diter' preserves positivity by induction. -/
lemma Diter'_pos (k q n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) : Diter' k q n ≥ 1 := by
  induction k with
  | zero => simp; omega
  | succ k ih => simp [Diter'_succ]; exact Dstep_pos q _ hq ih

/-- The n = 0 case: Dstep q 0 = 0 for q ≥ 2. -/
lemma Dstep_zero (q : ℕ) (hq : q ≥ 2) : Dstep q 0 = 0 := by
  simp only [Dstep]
  apply Nat.div_eq_of_lt; omega

/-- Diter' k q 0 = 0 for all k. -/
lemma Diter'_zero_start (k q : ℕ) (hq : q ≥ 2) : Diter' k q 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Diter'_succ, ih, Dstep_zero q hq]

/-- For q = 2: E(2, n) = 0 for n ≥ 1. -/
lemma E_two (n : ℕ) : E 2 n = 0 := by
  simp only [E]; omega

-- ══════════════════════════════════════════════════════════════════════
-- Phase 2: Transition to Real Sequences
-- ══════════════════════════════════════════════════════════════════════

/-- The growth ratio α = q / (q - 1). -/
noncomputable def α (q : ℕ) : ℝ := (q : ℝ) / ((q : ℝ) - 1)

/-- α > 1 for q ≥ 2. -/
lemma α_gt_one (q : ℕ) (hq : q ≥ 2) : α q > 1 := by
  simp only [α, gt_iff_lt]
  have hq' : (q : ℝ) ≥ 2 := by exact_mod_cast hq
  rw [one_lt_div (by linarith : (q : ℝ) - 1 > 0)]
  linarith

/-- α > 0 for q ≥ 2. -/
lemma α_pos (q : ℕ) (hq : q ≥ 2) : α q > 0 :=
  lt_trans zero_lt_one (α_gt_one q hq)

/-- The real error per step: e_k = E(q, D_{k-1}) / (q - 1). -/
noncomputable def e_step (q : ℕ) (n : ℕ) (k : ℕ) : ℝ :=
  (E q (Diter' k q n) : ℝ) / ((q : ℝ) - 1)

/-- e_step is non-negative. -/
lemma e_step_nonneg (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) : e_step q n k ≥ 0 := by
  simp only [e_step]
  apply div_nonneg (Nat.cast_nonneg _)
  have : (q : ℝ) ≥ 2 := by exact_mod_cast hq
  linarith

/-- e_step is bounded above by (q - 2) / (q - 1). -/
lemma qm1_pos (q : ℕ) (hq : q ≥ 2) : (q : ℝ) - 1 > 0 := by
  have : (q : ℝ) ≥ 2 := by exact_mod_cast hq
  linarith

lemma e_step_le (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) :
    e_step q n k ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
  simp only [e_step]
  apply div_le_div_of_nonneg_right _ (qm1_pos q hq).le
  exact_mod_cast E_le q (Diter' k q n) hq

/-- The real recurrence: D_{k+1} = α * D_k + e_{k+1} for n ≥ 1. -/
lemma Diter'_real_recurrence (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    (Diter' (k + 1) q n : ℝ) = α q * (Diter' k q n : ℝ) + e_step q n k := by
  have hqm1 := qm1_pos q hq
  have hpos := Diter'_pos k q n hq hn
  have hexact := Dstep_exact q (Diter' k q n) hq hpos
  -- hexact : Dstep q (Diter' k q n) * (q - 1) = q * Diter' k q n + E q (Diter' k q n)
  -- Goal: Dstep q (Diter' k q n) = q/(q-1) * Diter' k q n + E/(q-1)
  simp only [Diter'_succ, α, e_step]
  -- Goal: ↑(Dstep q (Diter' k q n)) = ↑q / (↑q - 1) * ↑(Diter' k q n) + ↑(E q (Diter' k q n)) / (↑q - 1)
  -- Multiply both sides by (q - 1)
  -- Cast hexact to ℝ
  set D := Diter' k q n with hD_def
  set S := Dstep q D with hS_def
  set Ev := E q D with hEv_def
  -- hexact : S * (q - 1) = q * D + Ev  (in ℕ)
  have hR : (S : ℝ) * ((q - 1 : ℕ) : ℝ) = (q : ℝ) * (D : ℝ) + (Ev : ℝ) := by
    exact_mod_cast hexact
  rw [show ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 from by
    rw [Nat.cast_sub (show 1 ≤ q by omega)]; simp] at hR
  -- hR : ↑S * (↑q - 1) = ↑q * ↑D + ↑Ev
  have hne : ((q : ℝ) - 1) ≠ 0 := hqm1.ne'
  rw [div_mul_eq_mul_div, ← add_div]
  rw [eq_div_iff hne]
  linarith

/-- The normalized sequence u_k = D_k / α^k. -/
noncomputable def u_seq (q : ℕ) (n : ℕ) (k : ℕ) : ℝ :=
  (Diter' k q n : ℝ) / (α q) ^ k

-- u_{k+1} = u_k + e_step / α^{k+1}, so u_k = n + ∑_{j<k} e_step q n j / α^{j+1}

-- ══════════════════════════════════════════════════════════════════════
-- Phase 3: Defining K via convergent series
-- ══════════════════════════════════════════════════════════════════════

/-- The summand for the series defining K. -/
noncomputable def K_summand (q : ℕ) (n : ℕ) (j : ℕ) : ℝ :=
  e_step q n j / (α q) ^ (j + 1)

/-- The summands are non-negative. -/
lemma K_summand_nonneg (q : ℕ) (n : ℕ) (j : ℕ) (hq : q ≥ 2) : K_summand q n j ≥ 0 := by
  simp only [K_summand]
  apply div_nonneg (e_step_nonneg q n j hq).le
  exact pow_nonneg (α_pos q hq).le _

/-- The summands are bounded by a geometric series. -/
lemma K_summand_le (q : ℕ) (n : ℕ) (j : ℕ) (hq : q ≥ 2) :
    K_summand q n j ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1) := by
  simp only [K_summand]
  apply div_le_div_of_nonneg_right (e_step_le q n j hq)
  exact pow_nonneg (α_pos q hq).le _

/-- The series ∑ K_summand is summable. -/
lemma K_summand_summable (q : ℕ) (n : ℕ) (hq : q ≥ 2) :
    Summable (K_summand q n) := by
  apply Summable.of_nonneg_of_le (fun j => (K_summand_nonneg q n j hq).le) (K_summand_le q n · hq)
  -- Need to show ∑ (q-2)/(q-1) / α^(j+1) is summable
  -- This is (q-2)/(q-1) * ∑ (1/α)^(j+1) which is a geometric series
  have hα := α_gt_one q hq
  have : ((q : ℝ) - 2) / ((q : ℝ) - 1) ≥ 0 := by
    apply div_nonneg <;> linarith [show (q : ℝ) ≥ 2 from by exact_mod_cast hq]
  -- Rewrite as constant * geometric
  have hαinv : (α q)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hαinv_nn : 0 ≤ (α q)⁻¹ := by positivity
  simp_rw [div_eq_mul_inv, ← inv_pow]
  -- Goal: Summable fun x => (q-2) * (q-1)⁻¹ * (α q)⁻¹ ^ (x + 1)
  -- Factor as C * α⁻¹ * (α⁻¹)^x
  have : (fun x => ((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹ ^ (x + 1)) =
      (fun x => (((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹) * (α q)⁻¹ ^ x) := by
    ext x; ring
  rw [this]
  exact Summable.mul_left _ (summable_geometric_of_lt_one hαinv_nn hαinv)

-- K(q, n) = n + ∑ e_step q n j / α^{j+1}
noncomputable def K_const (q : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) + ∑' j, K_summand q n j

-- ══════════════════════════════════════════════════════════════════════
-- Phase 4 & 5: Error bounds
-- ══════════════════════════════════════════════════════════════════════

/-- u_seq step: u_{k+1} = u_k + K_summand q n k. -/
lemma u_seq_step (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    u_seq q n (k + 1) = u_seq q n k + K_summand q n k := by
  simp only [u_seq, K_summand]
  rw [Diter'_real_recurrence q n k hq hn, pow_succ]
  have hα : α q ≠ 0 := (α_pos q hq).ne'
  have hαk : (α q) ^ k ≠ 0 := pow_ne_zero _ hα
  field_simp

/-- u_seq telescoping: u_k = n + ∑ j < k, K_summand q n j. -/
lemma u_seq_telescope (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    u_seq q n k = (n : ℝ) + ∑ j ∈ Finset.range k, K_summand q n j := by
  induction k with
  | zero => simp [u_seq]
  | succ k ih =>
    rw [u_seq_step q n k hq hn, ih, Finset.sum_range_succ]
    ring

/-- The error ε_k = D_k - K * α^k equals the negative tail sum. -/
/-- u_seq ≤ K_const: partial sums ≤ total (all summands non-negative). -/
lemma u_seq_le_K (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    u_seq q n k ≤ K_const q n := by
  rw [u_seq_telescope q n k hq hn, K_const]
  apply add_le_add_left
  apply sum_le_tsum (Finset.range k) (fun j _ => (K_summand_nonneg q n j hq).le)
    (K_summand_summable q n hq)

/-- K_const - u_seq < q - 2 for q ≥ 3. -/
lemma K_sub_u_lt (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) (hq3 : q ≥ 3) :
    K_const q n - u_seq q n k < (q : ℝ) - 2 := sorry

/-- For q = 2, all e_step are zero. -/
lemma e_step_zero_of_q2 (n : ℕ) (k : ℕ) :
    e_step 2 n k = 0 := by
  simp only [e_step, E_two]
  simp

/-- For q = 2, K_summand is zero. -/
lemma K_summand_zero_of_q2 (n : ℕ) (k : ℕ) (hn : n ≥ 1) :
    K_summand 2 n k = 0 := by
  simp only [K_summand, e_step_zero_of_q2 n k hn]

/-- For q = 2, tsum K_summand = 0. -/
lemma tsum_K_summand_zero_of_q2 (n : ℕ) (hn : n ≥ 1) :
    ∑' j, K_summand 2 n j = 0 := by
  simp [show ∀ j, K_summand 2 n j = 0 from fun j => K_summand_zero_of_q2 n j hn, tsum_zero]

/-- For q = 2, K_const = n. -/
lemma K_const_q2 (n : ℕ) (hn : n ≥ 1) :
    K_const 2 n = (n : ℝ) := by
  simp [K_const, tsum_K_summand_zero_of_q2 n hn]

/-- For q = 2, Dstep 2 n = 2*n for n ≥ 1. -/
lemma Dstep_two (n : ℕ) (hn : n ≥ 1) : Dstep 2 n = 2 * n := by
  have h := Dstep_exact 2 n (by omega) hn
  have hE := E_two n
  simp [hE] at h; omega

/-- For q = 2, Diter' k 2 n = 2^k * n. -/
lemma Diter'_two (k n : ℕ) (hn : n ≥ 1) : Diter' k 2 n = 2 ^ k * n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 2 ^ k * n ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    simp [Diter'_succ, ih, Dstep_two _ hpos]
    ring

/-- α 2 = 2. -/
lemma α_two : α 2 = 2 := by simp [α]; norm_num

theorem Diter'_asymptotic (q : ℕ) (hq : q ≥ 2) (n : ℕ) :
    ∃ K : ℝ, ∀ k : ℕ,
      let ε := (Diter' k q n : ℝ) - K * ((q : ℝ) / ((q : ℝ) - 1)) ^ k
      (q = 2 → ε = 0) ∧
      (q ≥ 3 → -((q : ℝ) - 2) < ε ∧ ε ≤ 0) := sorry
