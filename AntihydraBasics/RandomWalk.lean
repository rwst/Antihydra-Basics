import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Notation
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Lemmas

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
/-!
# Random Walk Escape Probability
We consider a random walk on ℤ where each step is +1 with probability 1/2 and -2 with
probability 1/2. Starting at depth `-d` (for `d > 0`), we ask: what is the probability
of ever reaching height 0 or above?
## Mathematical Analysis
The walk has expected step E[X] = 1·(1/2) + (-2)·(1/2) = -1/2 < 0 (negative drift).
By the Strong Law of Large Numbers, S_n/n → -1/2 a.s., so the walk drifts to -∞.
The escape probability p(d) = P(ever reach 0 from -d) satisfies the recurrence:
  p(d) = (1/2) p(d-1) + (1/2) p(d+2)
with p(0) = 1 and p(d) → 0 as d → ∞.
The characteristic equation r³ - 2r + 1 = 0 factors as (r-1)(r²+r-1) = 0.
The bounded solution is p(d) = φ^d where φ = (√5-1)/2 (the golden ratio conjugate).
For d = 2: p(2) = φ² = ((√5-1)/2)² = (3-√5)/2 ≈ 0.382.
## Proof approach for `probability_not_certain`
The rigorous proof combines two ingredients:
1. **SLLN-based limit**: By the Strong Law of Large Numbers
   (`ProbabilityTheory.strong_law_ae_real`), the partial sums S_n = Σ X_i satisfy
   S_n/n → -1/2 a.s. This implies sup_n S_n < ∞ a.s., so P(sup S_n ≥ d) → 0
   as d → ∞. In particular, there exists d₀ with P(gets_out X d₀) < 1.
2. **First-step bootstrapping**: By conditioning on X_0 and using independence,
   P(gets_out X d) ≤ 1/2 + 1/2 · P(gets_out X (d+2)).
   So P(gets_out X (d+2)) < 1 implies P(gets_out X d) < 1.
Combining: from the d₀ given by step 1, bootstrap downward by 2 to cover all d ≥ 1.
## Formalization challenges
Full formalization requires:
- Applying SLLN to integer-valued random variables
- The first-step decomposition (requires independence + shift invariance of i.i.d. sequences)
- Conditional probability computations
These require probability theory infrastructure beyond current Mathlib capabilities
for this specific setup. We prove the algebraic/combinatorial helper lemmas and
state the main results with the correct hypotheses.
-/
section RandomWalk
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable (X : ℕ → Ω → ℤ)

/-- The position after `n` steps starting at `-depth`. -/
def position (depth : ℤ) (n : ℕ) (ω : Ω) : ℤ :=
  -depth + (Finset.range n).sum (X · ω)
/-- The event that you ever reach the surface (depth 0 or higher). -/
def gets_out (depth : ℤ) : Set Ω :=
  { ω | ∃ n, position X depth n ω ≥ 0 }

/-! ## Combinatorial/Set-theoretic properties of gets_out -/
omit [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Deeper starting position means harder to escape -/
lemma gets_out_mono {d₁ d₂ : ℤ} (h : d₁ ≤ d₂) :
    gets_out X d₂ ⊆ gets_out X d₁ := by
  intro ω ⟨n, hn⟩
  exact ⟨n, by unfold position at *; linarith⟩

omit [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- gets_out at depth 0 is the whole space -/
lemma gets_out_zero : gets_out X 0 = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun ω => ⟨0, by simp [position]⟩

omit [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Each step is at most 1, so S_n ≤ n. When n < depth, position n < 0. -/
lemma position_neg_of_lt {n : ℕ} {depth : ℤ} (_hd : depth > 0) (hn : (n : ℤ) < depth)
    {ω : Ω} (hω : ∀ i, X i ω = 1 ∨ X i ω = -2) :
    position X depth n ω < 0 := by
  unfold position
  have : (Finset.range n).sum (X · ω) ≤ n := by
    calc (Finset.range n).sum (X · ω)
        ≤ (Finset.range n).sum (fun _ => (1 : ℤ)) := by
          apply Finset.sum_le_sum; intro i _; rcases hω i with h | h <;> omega
      _ = n := by simp
  linarith

/-! ## Measurability -/
omit [IsProbabilityMeasure (volume : Measure Ω)] in
lemma position_measurable (hmeas : ∀ n, Measurable (X n)) (d : ℤ) (n : ℕ) :
    Measurable (position X d n) := by
  unfold position
  exact Measurable.add measurable_const (Finset.measurable_sum _ fun i _ => hmeas i)

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- gets_out is measurable as a countable union of measurable sets -/
lemma gets_out_measurable (hmeas : ∀ n, Measurable (X n)) (d : ℤ) :
    MeasurableSet (gets_out X d) := by
  show MeasurableSet {ω | ∃ n, position X d n ω ≥ 0}
  have : {ω : Ω | ∃ n, position X d n ω ≥ 0} = ⋃ n, {ω | position X d n ω ≥ 0} := by
    ext ω; simp [Set.mem_iUnion]
  rw [this]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (position_measurable X hmeas d n)

/-! ## Distribution Lemma -/
/-
PROBLEM
The steps take values in {1, -2} almost surely
PROVIDED SOLUTION
Each X i ω is either 1 or -2, so X i ω ≤ 1. Therefore sum of first n steps ≤ n. Since n < depth, position = -depth + sum ≤ -depth + n < 0. Use Finset.sum_le_sum to bound the sum, and linarith for the final inequality.
-/
lemma step_values_ae
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_meas : ∀ n, Measurable (X n))
    (n : ℕ) : ∀ᵐ ω ∂ℙ, X n ω = 1 ∨ X n ω = -2 := by
  have h_sum_eq : ℙ {ω | X n ω = 1 ∨ X n ω = -2} = 1 := by
    rw [ show { ω | X n ω = 1 ∨ X n ω = -2 } = { ω | X n ω = 1 } ∪ { ω | X n ω = -2 } by rfl, MeasureTheory.measure_union ] <;> norm_num [ h_dist ];
    · norm_num [ ENNReal.inv_two_add_inv_two ];
    · exact Set.disjoint_left.mpr fun ω hω₁ hω₂ => by linarith [ hω₁.symm, hω₂.symm ] ;
    · exact measurableSet_eq_fun ( h_meas n ) measurable_const |> MeasurableSet.mem;
  have := h_sum_eq ▸ MeasureTheory.measure_compl ( show MeasurableSet { ω | X n ω = 1 ∨ X n ω = -2 } from by measurability ) ( MeasureTheory.measure_ne_top _ _ ) ; aesop;

/-! ## Main Theorems -/

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Monotonicity of escape probability: deeper start ⟹ lower probability -/
lemma prob_gets_out_mono {d₁ d₂ : ℤ} (h : d₁ ≤ d₂) :
    ℙ (gets_out X d₂) ≤ ℙ (gets_out X d₁) :=
  measure_mono (gets_out_mono X h)

/-- The event of escaping using the shifted sequence X₁, X₂, ... -/
def gets_out_shifted (depth : ℤ) : Set Ω :=
  { ω | ∃ n, -(depth : ℤ) + (Finset.range n).sum (fun i => X (i + 1) ω) ≥ 0 }

omit [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- First-step set decomposition: gets_out X d is contained in the union of
    "X₀ = 1 and escape from d-1 with shifted walk" and
    "X₀ = -2 and escape from d+2 with shifted walk". -/
lemma gets_out_subset_union (d : ℤ) (hd : d > 0) (ω : Ω)
    (hω : X 0 ω = 1 ∨ X 0 ω = -2) (h : ω ∈ gets_out X d) :
    ω ∈ ({ω | X 0 ω = 1} ∩ gets_out_shifted X (d - 1)) ∪
      ({ω | X 0 ω = -2} ∩ gets_out_shifted X (d + 2)) := by
  obtain ⟨n, hn⟩ := h
  unfold position at hn
  cases n with
  | zero => simp at hn; omega
  | succ m =>
    rw [Finset.sum_range_succ'] at hn
    simp at hn
    rcases hω with h1 | h2
    · left
      exact ⟨h1, ⟨m, by
        show -(d - 1) + (Finset.range m).sum (fun i => X (i + 1) ω) ≥ 0
        rw [h1] at hn; linarith⟩⟩
    · right
      exact ⟨h2, ⟨m, by
        show -(d + 2) + (Finset.range m).sum (fun i => X (i + 1) ω) ≥ 0
        rw [h2] at hn; linarith⟩⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- The shifted sequence X₁, X₂, ... is also iIndepFun. -/
lemma iIndepFun_shift
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume) :
    @iIndepFun Ω ℕ _ (fun _ => ℤ) _ (fun i => X (i + 1)) volume := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  -- Use the original iIndepFun on the shifted finset S.map (·+1)
  have h_orig := iIndepFun_iff_measure_inter_preimage_eq_mul.mp h_indep
  -- Map each element i ∈ S to i+1
  have key := h_orig (S.map ⟨(· + 1), Nat.succ_injective⟩)
    (sets := fun j => if h : j ≥ 1 then sets (j - 1) else Set.univ)
    (by intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        simp only
        exact hsets j hj)
  -- The intersection ⋂ i ∈ S.map (·+1), X i ⁻¹' ... equals ⋂ i ∈ S, X (i+1) ⁻¹' sets i
  have h_set_eq : (⋂ i ∈ S, X (i + 1) ⁻¹' sets i) =
      ⋂ i ∈ S.map ⟨(· + 1), Nat.succ_injective⟩,
        X i ⁻¹' (fun j => if h : j ≥ 1 then sets (j - 1) else Set.univ) i := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      simp only [Function.Embedding.coeFn_mk, ge_iff_le, show 1 ≤ j + 1 by omega,
        ↓reduceDIte, Nat.add_sub_cancel]
      exact h j hj
    · intro h j hj
      have := h (j + 1) (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
      simp only [ge_iff_le, show 1 ≤ j + 1 by omega,
        ↓reduceDIte, Nat.add_sub_cancel] at this
      exact this
  have h_prod_eq : (∏ i ∈ S, ℙ (X (i + 1) ⁻¹' sets i)) =
      ∏ i ∈ S.map ⟨(· + 1), Nat.succ_injective⟩,
        ℙ (X i ⁻¹' (fun j => if h : j ≥ 1 then sets (j - 1) else Set.univ) i) :=
    Finset.prod_nbij (· + 1) (by intro i hi; exact Finset.mem_map.mpr ⟨i, hi, rfl⟩)
      (by intro a b _ _ h; exact Nat.succ_injective h)
      (by intro j hj; obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj; exact ⟨i, hi, rfl⟩)
      (by intro i _; simp only [show i + 1 ≥ 1 by omega, ↓reduceDIte, Nat.add_sub_cancel])
  rw [h_set_eq, h_prod_eq, key]

/-- The shifted and original sequences have the same joint distribution.
    This follows from `IdentDistrib.pi` (in `Mathlib.Probability.IdentDistribIndep`)
    applied to `identDistrib_X` and `iIndepFun_shift`. -/
lemma identDistrib_shifted
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n)) :
    IdentDistrib (fun ω (n : ℕ) => X (n + 1) ω) (fun ω (n : ℕ) => X n ω)
      (ℙ : Measure Ω) ℙ := by
  have h_shift_indep := iIndepFun_shift X h_indep
  have h_shift_meas : ∀ i, Measurable (fun ω => X (i + 1) ω) := fun i => h_meas (i + 1)
  -- Map of original sequence = infinitePi of marginals
  have h_map_orig := (iIndepFun_iff_map_fun_eq_infinitePi_map h_meas).mp h_indep
  -- Map of shifted sequence = infinitePi of shifted marginals
  have h_map_shift := (iIndepFun_iff_map_fun_eq_infinitePi_map h_shift_meas).mp h_shift_indep
  -- Each X_j has the same distribution as X_0
  have h_same_map : ∀ j, Measure.map (X j) ℙ = Measure.map (X 0) ℙ := by
    intro j; rw [Measure.ext_iff_singleton]; intro z
    simp only [Measure.map_apply (h_meas j) (measurableSet_singleton z),
      Measure.map_apply (h_meas 0) (measurableSet_singleton z), Set.preimage, Set.mem_singleton_iff]
    by_cases hz1 : z = 1
    · subst hz1; rw [(h_dist j).1, (h_dist 0).1]
    · by_cases hz2 : z = -2
      · subst hz2; rw [(h_dist j).2, (h_dist 0).2]
      · have hae := fun k => step_values_ae X h_dist h_meas k
        have hsub : ∀ k, {ω | X k ω = z} ⊆ {ω | ¬(X k ω = 1 ∨ X k ω = -2)} :=
          fun k ω hω => by simp only [Set.mem_setOf_eq] at hω ⊢; omega
        have hzero : ∀ k, ℙ {ω | X k ω = z} = 0 := fun k =>
          le_antisymm ((measure_mono (hsub k)).trans (le_of_eq ((ae_iff.mp (hae k))))) (zero_le _)
        rw [hzero j, hzero 0]
  -- Shifted marginals equal original marginals
  have h_marginals_eq : (fun i => Measure.map (fun ω => X (i + 1) ω) ℙ) =
      (fun i => Measure.map (X i) ℙ) := by
    funext i; exact (h_same_map (i + 1)).trans (h_same_map i).symm
  have hf : Measurable (fun ω (i : ℕ) => X (i + 1) ω) :=
    measurable_pi_lambda _ (fun i => h_meas (i + 1))
  have hg : Measurable (fun ω (i : ℕ) => X i ω) :=
    measurable_pi_lambda _ h_meas
  exact {
    aemeasurable_fst := hf.aemeasurable
    aemeasurable_snd := hg.aemeasurable
    map_eq := by rw [h_map_shift, h_marginals_eq, ← h_map_orig]
  }

lemma prob_gets_out_shifted_eq
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (d : ℤ) :
    ℙ (gets_out_shifted X d) = ℙ (gets_out X d) := by
  have h_id := identDistrib_shifted X h_dist h_indep h_meas
  -- Both sets are preimages of the same S ⊆ (ℕ → ℤ) under shifted/original tuple
  have h_shifted_eq : gets_out_shifted X d =
      (fun ω (n : ℕ) => X (n + 1) ω) ⁻¹'
        {f : ℕ → ℤ | ∃ n, -(d : ℤ) + (Finset.range n).sum f ≥ 0} := by
    ext ω; simp [gets_out_shifted]
  have h_orig_eq : gets_out X d =
      (fun ω (n : ℕ) => X n ω) ⁻¹'
        {f : ℕ → ℤ | ∃ n, -(d : ℤ) + (Finset.range n).sum f ≥ 0} := by
    ext ω; simp [gets_out, position]
  rw [h_shifted_eq, h_orig_eq]
  have hf : Measurable (fun ω (i : ℕ) => X (i + 1) ω) :=
    measurable_pi_lambda _ (fun i => h_meas (i + 1))
  have hg : Measurable (fun ω (i : ℕ) => X i ω) :=
    measurable_pi_lambda _ h_meas
  have hs : MeasurableSet {f : ℕ → ℤ | ∃ n, -(d : ℤ) + (Finset.range n).sum f ≥ 0} := by
    have : {f : ℕ → ℤ | ∃ n, -(d : ℤ) + (Finset.range n).sum f ≥ 0} =
        ⋃ n, {f | -(d : ℤ) + (Finset.range n).sum f ≥ 0} := by ext; simp [Set.mem_iUnion]
    rw [this]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_le measurable_const
        ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_add _)
  rw [← Measure.map_apply hf hs, ← Measure.map_apply hg hs, h_id.map_eq]

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Independence: X₀ is independent from the shifted walk events.
    Since gets_out_shifted d depends only on X₁, X₂, ..., and X₀ is independent
    of all other X_i by iIndepFun, we have P({X₀ = v} ∩ gets_out_shifted d) =
    P({X₀ = v}) · P(gets_out_shifted d). -/
lemma prob_inter_gets_out_shifted
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (v : ℤ) (d : ℤ) :
    ℙ ({ω | X 0 ω = v} ∩ gets_out_shifted X d) =
      ℙ {ω | X 0 ω = v} * ℙ (gets_out_shifted X d) := by
  -- Use Indep of σ(X₀) and σ(X₁, X₂, ...) from iIndepFun
  have h_ind := indep_iSup_of_disjoint
    (fun i => MeasurableSpace.comap_le_iff_le_map.mpr (h_meas i))
    h_indep
    (show Disjoint ({0} : Set ℕ) (Set.Ici 1) by simp [Set.mem_Ici])
  rw [Indep_iff] at h_ind
  apply h_ind
  · -- {X 0 = v} is measurable w.r.t. ⨆ i ∈ {0}, comap (X i)
    exact (le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
      MeasurableSpace.comap (X i) inferInstance) 0 rfl) _
      ⟨{v}, measurableSet_singleton v, rfl⟩
  · -- gets_out_shifted X d is measurable w.r.t. ⨆ i ∈ Ici 1, comap (X i)
    have hXm : ∀ i, @Measurable Ω ℤ
        (⨆ j ∈ (Set.Ici 1 : Set ℕ), MeasurableSpace.comap (X j) inferInstance) inferInstance
        (X (i + 1)) := fun i =>
      Measurable.mono (comap_measurable (X (i + 1)))
        (le_iSup₂ (f := fun j (_ : j ∈ (Set.Ici 1 : Set ℕ)) =>
          MeasurableSpace.comap (X j) inferInstance) (i + 1) (Set.mem_Ici.mpr (by omega)))
        le_rfl
    unfold gets_out_shifted
    have heq : {ω : Ω | ∃ n, -(d : ℤ) + (Finset.range n).sum (fun i => X (i + 1) ω) ≥ 0} =
        ⋃ n, {ω | -(d : ℤ) + (Finset.range n).sum (fun i => X (i + 1) ω) ≥ 0} := by
      ext ω; simp [Set.mem_iUnion]
    rw [heq]
    exact MeasurableSet.iUnion fun n =>
      (@Finset.measurable_sum ℤ ℕ Ω _ _ _
        (⨆ j ∈ (Set.Ici 1 : Set ℕ), MeasurableSpace.comap (X j) inferInstance) _
        (Finset.range n) (fun i _ => hXm i)).const_add (-d) measurableSet_Ici

/-- First-step decomposition inequality.
    By conditioning on X₀: if X₀ = 1, the walk needs to escape from depth d-1;
    if X₀ = -2, it needs to escape from depth d+2. Both subsequent walks use
    the shifted sequence X₁, X₂, ... which is i.i.d. with the same distribution.
    Therefore P(gets_out X d) ≤ 1/2 · P(gets_out X (d-1)) + 1/2 · P(gets_out X (d+2)). -/
lemma prob_gets_out_le_half_add_half
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (d : ℤ) (hd : d > 0) :
    ℙ (gets_out X d) ≤ 1 / 2 * ℙ (gets_out X (d - 1)) + 1 / 2 * ℙ (gets_out X (d + 2)) := by
  -- Step 1: gets_out X d ⊆ᵃᵉ the union of the two first-step cases
  have h_ae := step_values_ae X h_dist h_meas 0
  have h_sub : gets_out X d ≤ᵐ[ℙ]
      (({ω | X 0 ω = 1} ∩ gets_out_shifted X (d - 1)) ∪
        ({ω | X 0 ω = -2} ∩ gets_out_shifted X (d + 2)) : Set Ω) := by
    filter_upwards [h_ae] with ω hω hω_in
    exact gets_out_subset_union X d hd ω hω hω_in
  -- Step 2: Bound the measure
  calc ℙ (gets_out X d)
      ≤ ℙ (({ω | X 0 ω = 1} ∩ gets_out_shifted X (d - 1)) ∪
            ({ω | X 0 ω = -2} ∩ gets_out_shifted X (d + 2))) :=
        measure_mono_ae h_sub
    _ ≤ ℙ ({ω | X 0 ω = 1} ∩ gets_out_shifted X (d - 1)) +
        ℙ ({ω | X 0 ω = -2} ∩ gets_out_shifted X (d + 2)) :=
        measure_union_le _ _
    _ = ℙ {ω | X 0 ω = 1} * ℙ (gets_out_shifted X (d - 1)) +
        ℙ {ω | X 0 ω = -2} * ℙ (gets_out_shifted X (d + 2)) := by
        rw [prob_inter_gets_out_shifted X h_indep h_meas 1 (d - 1),
            prob_inter_gets_out_shifted X h_indep h_meas (-2) (d + 2)]
    _ = 1 / 2 * ℙ (gets_out_shifted X (d - 1)) +
        1 / 2 * ℙ (gets_out_shifted X (d + 2)) := by
        rw [(h_dist 0).1, (h_dist 0).2]
    _ = 1 / 2 * ℙ (gets_out X (d - 1)) + 1 / 2 * ℙ (gets_out X (d + 2)) := by
        rw [prob_gets_out_shifted_eq X h_dist h_indep h_meas (d - 1),
            prob_gets_out_shifted_eq X h_dist h_indep h_meas (d + 2)]

/-- Phase 2: First-step bootstrapping.
    P(gets_out X d) ≤ 1/2 · P(gets_out X (d-1)) + 1/2 · P(gets_out X (d+2))
    so P(gets_out X (d+2)) < 1 implies P(gets_out X d) < 1. -/
lemma prob_gets_out_lt_one_of_add_two
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (d : ℤ) (hd : d > 0)
    (h : ℙ (gets_out X (d + 2)) < 1) :
    ℙ (gets_out X d) < 1 := by
  have key := prob_gets_out_le_half_add_half X h_dist h_indep h_meas d hd
  have hle1 : ℙ (gets_out X (d - 1)) ≤ 1 := prob_le_one
  have hle2 : ℙ (gets_out X (d + 2)) ≤ 1 := prob_le_one
  have half_ne_top : (1 / 2 : ENNReal) ≠ ⊤ := by norm_num
  calc ℙ (gets_out X d)
      ≤ 1 / 2 * ℙ (gets_out X (d - 1)) + 1 / 2 * ℙ (gets_out X (d + 2)) := key
    _ ≤ 1 / 2 * 1 + 1 / 2 * ℙ (gets_out X (d + 2)) := by
        gcongr
    _ < 1 / 2 * 1 + 1 / 2 * 1 := by
        gcongr <;> first | exact h | norm_num
    _ = 1 := by
        norm_num
        exact ENNReal.inv_two_add_inv_two

private lemma singleton_measure_zero_of_not_val
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_meas : ∀ n, Measurable (X n)) (k : ℕ) (z : ℤ) (hz1 : z ≠ 1) (hz2 : z ≠ -2) :
    ℙ {ω | X k ω = z} = 0 := by
  have hae := step_values_ae X h_dist h_meas k
  rw [ae_iff] at hae
  have hsub : {ω | X k ω = z} ⊆ {ω | ¬(X k ω = 1 ∨ X k ω = -2)} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; omega
  exact le_antisymm ((measure_mono hsub).trans (le_of_eq hae)) (zero_le _)

private lemma map_eq_of_same_dist
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_meas : ∀ n, Measurable (X n)) (i : ℕ) :
    Measure.map (X i) volume = Measure.map (X 0) volume := by
  rw [Measure.ext_iff_singleton]
  intro z
  simp only [Measure.map_apply (h_meas i) (measurableSet_singleton z),
      Measure.map_apply (h_meas 0) (measurableSet_singleton z),
      Set.preimage, Set.mem_singleton_iff]
  by_cases hz1 : z = 1
  · subst hz1; rw [(h_dist i).1, (h_dist 0).1]
  · by_cases hz2 : z = -2
    · subst hz2; rw [(h_dist i).2, (h_dist 0).2]
    · rw [singleton_measure_zero_of_not_val X h_dist h_meas i z hz1 hz2,
          singleton_measure_zero_of_not_val X h_dist h_meas 0 z hz1 hz2]

lemma identDistrib_X
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_meas : ∀ n, Measurable (X n)) (i : ℕ) :
    IdentDistrib (X i) (X 0) volume volume :=
  { aemeasurable_fst := (h_meas i).aemeasurable
    aemeasurable_snd := (h_meas 0).aemeasurable
    map_eq := map_eq_of_same_dist X h_dist h_meas i }

/-- The partial sums of an i.i.d. sequence with mean -1/2 are a.s. bounded above.
    This follows from the Strong Law of Large Numbers: S_n/n → E[X] = -1/2 a.s.,
    which implies S_n → -∞ a.s., hence sup_n S_n < ∞ a.s.
    The full formalization requires casting ℤ-valued RVs to ℝ, establishing
    identDistrib and integrability, and applying `ProbabilityTheory.strong_law_ae_real`. -/
lemma partial_sums_bdd_above_ae
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n)) :
    ∀ᵐ ω ∂ℙ, ∃ M : ℤ, ∀ n, (Finset.range n).sum (X · ω) ≤ M := by
  -- Cast to ℝ-valued random variables for the SLLN
  let Y : ℕ → Ω → ℝ := fun n ω => (X n ω : ℝ)
  have hY_meas : ∀ n, Measurable (Y n) := fun n =>
    (measurable_of_countable (Int.cast : ℤ → ℝ)).comp (h_meas n)
  -- Independence: iIndepFun for Y follows from iIndepFun for X by composition
  have hY_pairwise : Pairwise (fun i j => IndepFun (Y i) (Y j) volume) := by
    intro i j hij
    exact (h_indep.comp (fun _ => (Int.cast : ℤ → ℝ)) (fun _ => measurable_of_countable _)).indepFun hij
  -- IdentDistrib for Y follows from IdentDistrib for X by composition
  have hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) volume volume :=
    fun i => (identDistrib_X X h_dist h_meas i).comp (measurable_of_countable _)
  -- Integrability: Y 0 is integrable since it takes only finitely many values a.e.
  have hY_int : Integrable (Y 0) volume := by
    apply Integrable.of_bound (hY_meas 0).aestronglyMeasurable 2
    filter_upwards [step_values_ae X h_dist h_meas 0] with ω hω
    rcases hω with h | h <;> simp [Y, h]
  -- Apply the Strong Law of Large Numbers
  have h_slln := ProbabilityTheory.strong_law_ae_real Y hY_int hY_pairwise hY_ident
  -- Compute E[Y 0] = -1/2
  have h_expect : ∫ ω, Y 0 ω = -1/2 := by
    -- Split integral over {X 0 = 1} and its complement
    have hS₁ : MeasurableSet {ω : Ω | X 0 ω = 1} := (h_meas 0) (measurableSet_singleton 1)
    have h_split := integral_add_compl hS₁ hY_int
    -- On {X 0 = 1}, Y 0 = 1
    have h_on_S₁ : ∫ ω in {ω | X 0 ω = 1}, Y 0 ω = 1/2 := by
      rw [setIntegral_congr_fun hS₁ (fun ω hω => by
        show (X 0 ω : ℝ) = 1; rw [Set.mem_setOf_eq.mp hω]; simp)]
      rw [setIntegral_const]
      simp [Measure.real, (h_dist 0).1]
    -- On {X 0 = 1}ᶜ, Y 0 = -2 a.e.
    have h_on_S₁c : ∫ ω in {ω | X 0 ω = 1}ᶜ, Y 0 ω = -1 := by
      have h_ae_neg2 : ∀ᵐ ω ∂(volume : Measure Ω).restrict {ω | X 0 ω = 1}ᶜ,
          Y 0 ω = (-2 : ℝ) := by
        rw [ae_restrict_iff' hS₁.compl]
        filter_upwards [step_values_ae X h_dist h_meas 0] with ω hω hω_compl
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω_compl
        rcases hω with h | h
        · exact absurd h hω_compl
        · simp [Y, h]
      rw [integral_congr_ae h_ae_neg2, setIntegral_const]
      have h_compl_meas : ℙ {ω : Ω | X 0 ω = 1}ᶜ = 1/2 := by
        rw [measure_compl hS₁ (measure_ne_top _ _), (h_dist 0).1]
        simp
      simp [Measure.real, h_compl_meas]
    linarith [h_split]
  -- From S_n/n → -1/2 < 0, deduce S_n is bounded above a.e.
  have h_neg : (∫ ω, Y 0 ω) < 0 := by linarith
  -- For a.e. ω, S_n/n → -1/2, so eventually S_n/n < 0, hence S_n < 0.
  filter_upwards [h_slln] with ω hω
  -- hω : Tendsto (fun n => (∑ i ∈ Finset.range n, Y i ω) / ↑n) atTop (𝓝 (∫ x, Y 0 x))
  -- Eventually S_n/n < 0, so S_n < 0 for large n
  have h_ev : ∀ᶠ n in Filter.atTop, (∑ i ∈ Finset.range n, Y i ω) / (n : ℝ) < 0 :=
    (hω.eventually (Iio_mem_nhds h_neg)).mono (fun n hn => hn)
  have h_ev_neg : ∀ᶠ n in Filter.atTop, (∑ i ∈ Finset.range n, (X · ω) i) ≤ 0 := by
    apply h_ev.mono
    intro n hn
    by_cases hn0 : (n : ℝ) = 0
    · simp [hn0] at hn
    · have hn_pos : (0 : ℝ) < n := by positivity
      have : (∑ i ∈ Finset.range n, Y i ω) < 0 := by
        rwa [div_lt_iff₀ hn_pos, zero_mul] at hn
      have : (∑ i ∈ Finset.range n, (X i ω : ℝ)) < 0 := this
      have : (↑(∑ i ∈ Finset.range n, (X · ω) i) : ℝ) < 0 := by
        convert this using 1
        push_cast
        rfl
      exact_mod_cast this.le
  -- Extract the threshold N
  obtain ⟨N, hN⟩ := h_ev_neg.exists_forall_of_atTop
  -- For n ≥ N, S_n ≤ 0. For n < N, S_n is in a finite set.
  -- Take M = max over all S_0, ..., S_N (the range (N+1) is nonempty)
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
  let f : ℕ → ℤ := fun n => (Finset.range n).sum (X · ω)
  refine ⟨(Finset.range (N + 1)).sup' hne f, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · calc f n ≤ 0 := hN n hn
      _ = f 0 := by simp [f]
      _ ≤ (Finset.range (N + 1)).sup' hne f :=
        Finset.le_sup' f (Finset.mem_range.mpr (Nat.zero_lt_succ N))
  · push_neg at hn
    exact Finset.le_sup' f (Finset.mem_range.mpr (by omega))

/-- The intersection of all gets_out sets has measure zero.
    For a.e. ω, the partial sums are bounded above by some M, so for d > M,
    position X d n ω = -d + S_n ≤ -d + M < 0 for all n. -/
lemma iInter_gets_out_measure_zero
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n)) :
    ℙ (⋂ d : ℕ, gets_out X (↑d + 1)) = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc ℙ (⋂ d : ℕ, gets_out X (↑d + 1))
      ≤ ℙ {ω | ∀ d : ℕ, ∃ n, (Finset.range n).sum (X · ω) ≥ (↑d + 1)} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at hω ⊢
        intro d
        obtain ⟨n, hn⟩ := hω d
        exact ⟨n, by unfold position at hn; omega⟩
    _ ≤ ℙ {ω | ¬∃ M : ℤ, ∀ n, (Finset.range n).sum (X · ω) ≤ M} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro ⟨M, hM⟩
        have := hω M.toNat
        obtain ⟨n, hn⟩ := this
        have := hM n
        omega
    _ = 0 := by
        have h_ae := partial_sums_bdd_above_ae X h_dist h_indep h_meas
        rw [ae_iff] at h_ae
        convert h_ae using 1

/-- Phase 1: SLLN implies escape probability is < 1 for some large depth.
    By the strong law, S_n/n → -1/2 a.s., so S_n → -∞ a.s.,
    hence sup S_n < ∞ a.s. and P(gets_out X d) → 0 as d → ∞. -/
lemma exists_depth_prob_lt_one
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n)) :
    ∃ d₀ : ℤ, d₀ > 0 ∧ ℙ (gets_out X d₀) < 1 := by
  -- The measures of gets_out X (d+1) tend to 0 as d → ∞
  have h_tendsto : Filter.Tendsto (fun d : ℕ => ℙ (gets_out X (↑d + 1)))
      Filter.atTop (nhds (ℙ (⋂ d : ℕ, gets_out X (↑d + 1)))) := by
    apply tendsto_measure_iInter_atTop
    · intro d; exact (gets_out_measurable X h_meas _).nullMeasurableSet
    · intro d₁ d₂ hle; exact gets_out_mono X (by omega)
    · exact ⟨0, measure_ne_top _ _⟩
  rw [iInter_gets_out_measure_zero X h_dist h_indep h_meas] at h_tendsto
  -- Since the limit is 0, eventually the measure is < 1
  have h_ev := h_tendsto.eventually (Iio_mem_nhds one_pos)
  obtain ⟨d, hd⟩ := h_ev.exists
  exact ⟨↑d + 1, by omega, hd⟩

/-- Iterated bootstrapping: reduce depth by 2, k times -/
lemma prob_lt_one_of_add_two_mul
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (d : ℤ) (hd : d > 0) (k : ℕ)
    (h : ℙ (gets_out X (d + 2 * (k : ℤ))) < 1) :
    ℙ (gets_out X d) < 1 := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply prob_gets_out_lt_one_of_add_two X h_dist h_indep h_meas (d + 2 * (n : ℤ))
    · omega
    · convert h using 2; push_cast; ring_nf

/--
  The probability of getting out is strictly less than 1 when starting below the surface.
  Combines SLLN (Phase 1) with first-step bootstrapping (Phase 2).
-/
theorem probability_not_certain
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (depth : ℤ) (h_pos : depth > 0) :
    ℙ (gets_out X depth) < (1 : ENNReal) := by
  obtain ⟨d₀, hd₀_pos, hd₀⟩ := exists_depth_prob_lt_one X h_dist h_indep h_meas
  apply prob_lt_one_of_add_two_mul X h_dist h_indep h_meas depth h_pos (d₀ - depth).toNat
  calc ℙ (gets_out X (depth + 2 * ((d₀ - depth).toNat : ℤ)))
      ≤ ℙ (gets_out X d₀) := prob_gets_out_mono X (by omega)
    _ < 1 := hd₀

end RandomWalk
