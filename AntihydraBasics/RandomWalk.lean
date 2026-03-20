import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
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
/--
  The probability of getting out is strictly less than 1 when starting below the surface.
  This is the key non-trivial result. The proof combines the Strong Law of Large Numbers
  (giving P(gets_out X d) → 0 as d → ∞) with a first-step bootstrapping argument
  (giving P(gets_out X d) < 1 for all d ≥ 1 from P(gets_out X d₀) < 1 for some d₀).
-/
theorem probability_not_certain
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : @iIndepFun Ω ℕ _ (fun _ => ℤ) _ X volume)
    (h_meas : ∀ n, Measurable (X n))
    (depth : ℤ) (h_pos : depth > 0) :
    ℙ (gets_out X depth) < (1 : ENNReal) := by
  sorry

end RandomWalk
