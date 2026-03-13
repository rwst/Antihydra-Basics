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
  have hαinv_nn : 0 ≤ (α q)⁻¹ := inv_nonneg.mpr (α_pos q hq).le
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

/-- u_seq ≤ K_const: partial sums ≤ total (all summands non-negative). -/
lemma u_seq_le_K (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    u_seq q n k ≤ K_const q n := by
  rw [u_seq_telescope q n k hq hn, K_const]
  gcongr
  exact (K_summand_summable q n hq).sum_le_tsum (Finset.range k)
    (fun j _ => (K_summand_nonneg q n j hq).le)

/-- The full geometric bound equals q - 2. -/
lemma geom_bound_eq (q : ℕ) (hq : q ≥ 2) :
    ∑' j, (((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1)) = (q : ℝ) - 2 := by
  have hαinv : (α q)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (α_gt_one q hq)
  have hαinv_nn : 0 ≤ (α q)⁻¹ := inv_nonneg.mpr (α_pos q hq).le
  -- Rewrite as C * ∑ (α⁻¹)^(j+1) = C * α⁻¹/(1 - α⁻¹) = C * 1/(α-1) = C*(q-1) = q-2
  simp_rw [div_eq_mul_inv, ← inv_pow]
  have hfact : (fun j => ((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹ ^ (j + 1)) =
      (fun j => (((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹) * (α q)⁻¹ ^ j) := by
    ext j; ring
  rw [hfact, tsum_mul_left, tsum_geometric_of_lt_one hαinv_nn hαinv]
  simp only [α]
  have hq' : (q : ℝ) ≥ 2 := by exact_mod_cast hq
  have hqm1 : (q : ℝ) - 1 > 0 := by linarith
  field_simp
  ring

/-- K_const ≤ n + q - 2 (non-strict). -/
lemma K_const_le (q : ℕ) (n : ℕ) (hq : q ≥ 2) :
    K_const q n ≤ (n : ℝ) + ((q : ℝ) - 2) := by
  simp only [K_const]
  gcongr
  have bound_summable : Summable (fun j => ((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1)) := by
    simp_rw [div_eq_mul_inv, ← inv_pow]
    have hfact : (fun j => ((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹ ^ (j + 1)) =
        (fun j => (((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹) * (α q)⁻¹ ^ j) := by
      ext j; ring
    rw [hfact]
    exact Summable.mul_left _ (summable_geometric_of_lt_one
      (inv_nonneg.mpr (α_pos q hq).le) (inv_lt_one_of_one_lt₀ (α_gt_one q hq)))
  calc ∑' j, K_summand q n j
      ≤ ∑' j, (((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1)) :=
        (K_summand_summable q n hq).tsum_le_tsum (K_summand_le q n · hq) bound_summable
    _ = (q : ℝ) - 2 := geom_bound_eq q hq

/-- Dstep q n ≥ 2 for q ≥ 2, n ≥ 1. -/
lemma Dstep_ge_two (q n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) : Dstep q n ≥ 2 := by
  have h := Dstep_exact q n hq hn
  have hE := E_le q n hq
  -- Dstep q n * (q-1) = q*n + E ≥ q*n ≥ 2*1 = 2
  -- Also q-1 ≥ 1, so Dstep ≥ 2 requires Dstep*(q-1) ≥ 2*(q-1)
  -- q*n + E ≥ q ≥ 2, and (q-1) ≥ 1
  -- If Dstep = 1, then q-1 = q*n + E ≥ q ≥ 2, so q-1 ≥ q, contradiction
  -- Dstep*(q-1) = q*n + E ≥ q*n ≥ q ≥ 2
  -- If Dstep ≤ 1, then Dstep*(q-1) ≤ q-1, but q*n ≥ q, so q-1 ≥ q, contradiction
  have hqn : q * n ≥ 2 * 1 := Nat.mul_le_mul hq hn
  -- Dstep*(q-1) ≥ q*n ≥ 2, but if Dstep ≤ 1 then Dstep*(q-1) ≤ q-1 < q ≤ q*n
  by_contra hlt; push_neg at hlt
  have hD1 : Dstep q n ≤ 1 := by omega
  have hD_mul : Dstep q n * (q - 1) ≤ 1 * (q - 1) := Nat.mul_le_mul_right _ hD1
  simp at hD_mul
  -- hD_mul : Dstep q n * (q - 1) ≤ q - 1
  -- h : Dstep q n * (q - 1) = q * n + E q n
  -- So q * n + E q n ≤ q - 1
  -- But q * n ≥ q (since n ≥ 1) and q > q - 1 (since q ≥ 2)
  have hqn2 : q * n ≥ q := Nat.le_mul_of_pos_right q (by omega)
  generalize Dstep q n * (q - 1) = P at h hD_mul
  generalize q * n = QN at h hqn2
  omega

/-- If E(q, D_k) = q-2 for all k (starting from some point), then (q-1)^m | y_0
    for all m, which is impossible. This is the Phase 5 divisibility argument. -/
lemma tsum_K_summand_lt (q : ℕ) (n : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) (hq3 : q ≥ 3) :
    ∑' j, K_summand q n j < (q : ℝ) - 2 := by
  -- By contradiction: if ∑' K_summand = q-2 = ∑' bound, then each K_summand = bound.
  -- This means E(q, D_k) = q-2 for all k, forcing D_k ≡ 1 (mod q-1).
  -- Then y_k = D_k + q - 2 satisfies y_{k+1}*(q-1) = q*y_k.
  -- By coprimality, (q-1)^m | y_0 for all m, contradicting finiteness.
  by_contra h; push_neg at h
  -- h : ∑' K_summand ≥ q - 2
  -- We know ∑' K_summand ≤ q - 2 from K_const_le
  have hle := K_const_le q n hq
  simp only [K_const] at hle
  have hle' : ∑' j, K_summand q n j ≤ (q : ℝ) - 2 := by linarith
  have heq : ∑' j, K_summand q n j = (q : ℝ) - 2 := le_antisymm hle' h
  -- Each K_summand j = bound_j (from tsum equality with non-negative summands)
  -- This means E(q, Diter' j q n) = q-2 for all j
  -- First: derive E = q-2 for all j from the tsum equality
  -- If any K_summand j < bound_j, the tsum would be strictly less (contradiction)
  -- So K_summand j = bound_j for all j
  -- Therefore e_step q n j = (q-2)/(q-1) for all j
  -- Therefore E(q, Diter' j q n) = q-2 for all j
  have hE_all : ∀ j, E q (Diter' j q n) = q - 2 := by
    intro j; by_contra hne
    have hlt : E q (Diter' j q n) < q - 2 := by
      have := E_le q (Diter' j q n) hq; omega
    -- K_summand j < bound_j
    have hKj_lt : K_summand q n j < ((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1) := by
      simp only [K_summand, e_step]
      apply div_lt_div_of_pos_right _ (pow_pos (α_pos q hq) _)
      apply div_lt_div_of_pos_right _ (qm1_pos q hq)
      exact_mod_cast hlt
    have bound_summable : Summable (fun j => ((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1)) := by
      simp_rw [div_eq_mul_inv, ← inv_pow]
      have hfact : (fun j => ((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹ ^ (j + 1)) =
          (fun j => (((q : ℝ) - 2) * ((q : ℝ) - 1)⁻¹ * (α q)⁻¹) * (α q)⁻¹ ^ j) := by
        ext j; ring
      rw [hfact]
      exact Summable.mul_left _ (summable_geometric_of_lt_one
        (inv_nonneg.mpr (α_pos q hq).le) (inv_lt_one_of_one_lt₀ (α_gt_one q hq)))
    have : ∑' j, K_summand q n j <
        ∑' j, (((q : ℝ) - 2) / ((q : ℝ) - 1) / (α q) ^ (j + 1)) :=
      Summable.tsum_lt_tsum_of_nonneg (fun j => (K_summand_nonneg q n j hq).le)
        (K_summand_le q n · hq) hKj_lt bound_summable
    rw [geom_bound_eq q hq] at this
    linarith
  -- Now: E(q, D_j) = q-2 for all j means (D_j - 1) % (q-1) = 0
  -- From E def: E q m = q-2 - ((m-1) % (q-1)), so q-2 = q-2 - ((D_j-1)%(q-1))
  -- Therefore (D_j - 1) % (q-1) = 0
  have hmod_all : ∀ j, (Diter' j q n - 1) % (q - 1) = 0 := by
    intro j; have := hE_all j; simp only [E] at this; omega
  -- y_j = D_j + q - 2 satisfies y_{j+1}*(q-1) = q*y_j
  -- From Dstep_exact: D_{j+1}*(q-1) = q*D_j + E(q, D_j) = q*D_j + q-2
  -- So (D_{j+1} + q-2)*(q-1) = D_{j+1}*(q-1) + (q-2)*(q-1)
  --                            = q*D_j + q-2 + (q-2)*(q-1)
  --                            = q*D_j + (q-2)*q = q*(D_j + q-2)
  -- So y_{j+1}*(q-1) = q*y_j
  set y := fun j => Diter' j q n + q - 2 with hy_def
  have hy_rec : ∀ j, y (j + 1) * (q - 1) = q * y j := by
    intro j
    have hpos := Diter'_pos j q n hq hn
    have hexact := Dstep_exact q (Diter' j q n) hq hpos
    have hEj := hE_all j
    simp only [Diter'_succ, hy_def] at *
    -- hexact : Dstep q (Diter' j q n) * (q-1) = q * Diter' j q n + E q (Diter' j q n)
    -- hEj : E q (Diter' j q n) = q-2
    rw [hEj] at hexact
    -- (Dstep q D_j + q - 2) * (q-1) = Dstep*(q-1) + (q-2)*(q-1) = q*D_j + q-2 + (q-2)*(q-1)
    -- = q*D_j + (q-2)*q = q*(D_j + q-2)
    have hDpos : Dstep q (Diter' j q n) ≥ 1 := Dstep_pos q _ hq hpos
    -- Need: (Dstep + q - 2) * (q - 1) = q * (D_j + q - 2)
    -- LHS = Dstep*(q-1) + (q-2)*(q-1) = q*D_j + (q-2) + (q-2)*(q-1)
    --      = q*D_j + (q-2)*q = q*(D_j + q - 2) = RHS
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
    simp only [show q' + 2 - 1 = q' + 1 from by omega,
      show q' + 2 - 2 = q' from by omega] at hexact ⊢
    -- hexact: Dstep * (q'+1) = (q'+2) * D_j + q'
    -- Goal: (Dstep + q') * (q'+1) = (q'+2) * (D_j + q')
    -- Expand: Dstep*(q'+1) + q'*(q'+1) = (q'+2)*D_j + (q'+2)*q'
    -- From hexact: LHS = (q'+2)*D_j + q' + q'*(q'+1) = (q'+2)*D_j + q' + q'^2 + q'
    -- = (q'+2)*D_j + q'^2 + 2q'= (q'+2)*D_j + q'*(q'+2) = RHS
    generalize Dstep (q' + 2) (Diter' j (q' + 2) n) = S at hexact ⊢
    generalize Diter' j (q' + 2) n = D at hexact hpos ⊢
    have h1 : S + (q' + 2) - 2 = S + q' := by omega
    have h2 : D + (q' + 2) - 2 = D + q' := by omega
    rw [h1, h2]
    nlinarith
  -- By induction: y m * (q-1)^m = y 0 * q^m
  have hy_pow : ∀ m, y m * (q - 1) ^ m = y 0 * q ^ m := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      have hrec := hy_rec m
      calc y (m + 1) * (q - 1) ^ (m + 1)
          = y (m + 1) * ((q - 1) ^ m * (q - 1)) := by rw [pow_succ]
        _ = y (m + 1) * (q - 1) * (q - 1) ^ m := by ring
        _ = q * y m * (q - 1) ^ m := by rw [hrec]
        _ = q * (y m * (q - 1) ^ m) := by ring
        _ = q * (y 0 * q ^ m) := by rw [ih]
        _ = y 0 * (q ^ m * q) := by ring
        _ = y 0 * q ^ (m + 1) := by rw [pow_succ]
  -- Since gcd(q-1, q) = 1, (q-1)^m | y 0 for all m
  have hcop : Nat.Coprime (q - 1) q := by
    rw [Nat.Coprime, Nat.gcd_comm]
    rw [show q = q - 1 + 1 from by omega]
    simp [Nat.gcd_succ]
  have hdvd : ∀ m, (q - 1) ^ m ∣ y 0 := by
    intro m
    have := hy_pow m
    have : (q - 1) ^ m ∣ y 0 * q ^ m := ⟨y m, by linarith⟩
    exact (hcop.pow_left m |>.pow_right m).dvd_of_dvd_mul_right this
  -- y 0 = n + q - 2 ≥ 1 (since n ≥ 1 and q ≥ 3)
  have hy0_pos : y 0 ≥ 1 := by simp [hy_def]; omega
  -- For m large enough, (q-1)^m > y 0, contradiction
  have hqm1_ge2 : q - 1 ≥ 2 := by omega
  have : ∀ m, (q - 1) ^ m ≤ y 0 := fun m => Nat.le_of_dvd (by omega) (hdvd m)
  -- But (q-1)^m → ∞, so for large m this fails
  have := this (y 0 + 1)
  have : (q - 1) ^ (y 0 + 1) ≥ 2 ^ (y 0 + 1) := Nat.pow_le_pow_left hqm1_ge2 _
  have : 2 ^ (y 0 + 1) > y 0 := by
    induction (y 0) with
    | zero => simp
    | succ k ih =>
      have : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      omega
  omega

/-- K_const - u_seq < q - 2 for q ≥ 3. -/
lemma K_sub_u_lt (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) (hq3 : q ≥ 3) :
    K_const q n - u_seq q n k < (q : ℝ) - 2 := by
  have hu0 : u_seq q n 0 = (n : ℝ) := by simp [u_seq]
  suffices h : K_const q n - (n : ℝ) < (q : ℝ) - 2 by
    have huk := u_seq_le_K q n k hq hn
    have hu0_le : (n : ℝ) ≤ u_seq q n k := by
      rw [u_seq_telescope q n k hq hn]
      linarith [(Finset.sum_nonneg (fun j _ => (K_summand_nonneg q n j hq).le) :
        ∑ j ∈ Finset.range k, K_summand q n j ≥ 0)]
    linarith
  simp only [K_const, add_sub_cancel_left]
  exact tsum_K_summand_lt q n hq hn hq3

/-- For q = 2, all e_step are zero. -/
lemma e_step_zero_of_q2 (n : ℕ) (k : ℕ) :
    e_step 2 n k = 0 := by
  simp only [e_step, E_two]
  simp

/-- For q = 2, K_summand is zero. -/
lemma K_summand_zero_of_q2 (n : ℕ) (k : ℕ) :
    K_summand 2 n k = 0 := by
  simp only [K_summand, e_step_zero_of_q2 n k, zero_div]

/-- For q = 2, tsum K_summand = 0. -/
lemma tsum_K_summand_zero_of_q2 (n : ℕ) :
    ∑' j, K_summand 2 n j = 0 := by
  simp [show ∀ j, K_summand 2 n j = 0 from fun j => K_summand_zero_of_q2 n j, tsum_zero]

/-- For q = 2, K_const = n. -/
lemma K_const_q2 (n : ℕ) :
    K_const 2 n = (n : ℝ) := by
  simp [K_const, tsum_K_summand_zero_of_q2 n]

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

/-- Iteration composition: Diter' (j + k) q n = Diter' j q (Diter' k q n). -/
lemma Diter'_add (j k q n : ℕ) : Diter' (j + k) q n = Diter' j q (Diter' k q n) := by
  simp [Diter', Function.iterate_add_apply]

/-- The tail of the K_summand series, multiplied by α^k, equals
    the K_summand series for the shifted starting point. -/
lemma K_tail_eq_shifted (q : ℕ) (n : ℕ) (k : ℕ) (hq : q ≥ 2) (hn : n ≥ 1) :
    (K_const q n - u_seq q n k) * (α q) ^ k =
    ∑' j, K_summand q (Diter' k q n) j := by
  have hαk_pos : (α q) ^ k > 0 := pow_pos (α_pos q hq) k
  have hα_ne : (α q) ^ k ≠ 0 := hαk_pos.ne'
  -- Step 1: K - u_k = ∑' j, K_summand q n (j + k)
  have htail : K_const q n - u_seq q n k = ∑' j, K_summand q n (j + k) := by
    rw [u_seq_telescope q n k hq hn, K_const]
    -- n + ∑' j, f j - (n + ∑ j<k, f j) = ∑' j, f (j+k)
    have hsum := (K_summand_summable q n hq).sum_add_tsum_nat_add k
    linarith
  -- Step 2: K_summand q (Diter' k q n) j = K_summand q n (j + k) * α^k
  have hrel : ∀ j, K_summand q (Diter' k q n) j =
      K_summand q n (j + k) * (α q) ^ k := by
    intro j
    simp only [K_summand, e_step, Diter'_add]
    have hα_pos := α_pos q hq
    have hqm1 := qm1_pos q hq
    field_simp
    ring
  -- Step 3: Combine
  simp_rw [hrel, tsum_mul_right]
  rw [htail]

theorem Diter'_asymptotic (q : ℕ) (hq : q ≥ 2) (n : ℕ) :
    ∃ K : ℝ, ∀ k : ℕ,
      let ε := (Diter' k q n : ℝ) - K * ((q : ℝ) / ((q : ℝ) - 1)) ^ k
      (q = 2 → ε = 0) ∧
      (q ≥ 3 → -((q : ℝ) - 2) < ε ∧ ε ≤ 0) := by
  -- Case split on n = 0 vs n ≥ 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: sequence is all 0, K = 0
    exact ⟨0, fun k => by
      simp only [Diter'_zero_start k q hq]
      constructor
      · intro _; simp
      · intro hq3
        have : (q : ℝ) ≥ 3 := by exact_mod_cast hq3
        simp; linarith⟩
  · -- n ≥ 1
    have hn' : n ≥ 1 := hn
    -- Use K = K_const q n
    refine ⟨K_const q n, fun k => ?_⟩
    -- Note: α q = q / (q - 1)
    have hα_eq : α q = (q : ℝ) / ((q : ℝ) - 1) := rfl
    constructor
    · -- q = 2 case
      intro hq2; subst hq2
      -- ε = Diter' k 2 n - K_const 2 n * 2^k
      show (Diter' k 2 n : ℝ) - K_const 2 n * (2 / (2 - 1)) ^ k = 0
      rw [K_const_q2 n, Diter'_two k n hn']
      push_cast; ring
    · -- q ≥ 3 case
      intro hq3
      constructor
      · -- ε > -(q-2), i.e., D_k - K * α^k > -(q-2)
        -- Equivalently: K * α^k - D_k < (q-2)
        -- Equivalently: (K - u_k) * α^k < (q-2) [since D_k = u_k * α^k]
        -- Follows from K - u_k < q - 2 and α^k ≥ 1
        rw [show -((q : ℝ) - 2) = -(((q : ℝ) - 2)) from rfl]
        rw [← hα_eq]
        have hKu := K_sub_u_lt q n k hq hn' hq3
        -- K - u_k < q-2, and D_k - K*α^k = -(K - u_k) * α^k... no
        -- D_k = u_k * α^k, so D_k - K*α^k = (u_k - K)*α^k
        have hαk_pos : (α q) ^ k > 0 := pow_pos (α_pos q hq) k
        rw [show (Diter' k q n : ℝ) = u_seq q n k * (α q) ^ k from by
          simp [u_seq]; rw [div_mul_cancel₀ _ hαk_pos.ne']]
        rw [show u_seq q n k * (α q) ^ k - K_const q n * (α q) ^ k =
          (u_seq q n k - K_const q n) * (α q) ^ k from by ring]
        -- (u_k - K) * α^k > -(q-2), i.e., (K - u_k) * α^k < q-2
        -- By K_tail_eq_shifted, (K - u_k) * α^k = ∑' j, K_summand q (Diter' k q n) j
        -- By tsum_K_summand_lt, this is < q - 2
        have htail := K_tail_eq_shifted q n k hq hn'
        have hDk_pos := Diter'_pos k q n hq hn'
        have hlt := tsum_K_summand_lt q (Diter' k q n) hq hDk_pos hq3
        linarith
      · -- ε ≤ 0, i.e., D_k ≤ K * α^k
        rw [← hα_eq]
        have hαk_pos : (α q) ^ k > 0 := pow_pos (α_pos q hq) k
        rw [show (Diter' k q n : ℝ) = u_seq q n k * (α q) ^ k from by
          simp [u_seq]; rw [div_mul_cancel₀ _ hαk_pos.ne']]
        rw [show u_seq q n k * (α q) ^ k - K_const q n * (α q) ^ k =
          (u_seq q n k - K_const q n) * (α q) ^ k from by ring]
        have huk_le := u_seq_le_K q n k hq hn'
        nlinarith
