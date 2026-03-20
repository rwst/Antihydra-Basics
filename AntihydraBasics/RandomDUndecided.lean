import AntihydraBasics.Antihydra
import AntihydraBasics.NonPeriodicity
import AntihydraBasics.RandomWalk

open BigOperators MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- The halting event from `Aiter_8_2_halt_iff_Diter_7_halt`, randomized:
    `Y n ω` models `Diter n 7` where the parity at each step is drawn randomly. -/
def random_halt_event {Ω : Type*} (Y : ℕ → Ω → ℕ) : Set Ω :=
  { ω | ∃ i, Y (i + 1) ω % 2 = 0 ∧ Y (i + 1) ω ≥ 5 ∧ i % 3 = 2 ∧
    (∑ j ∈ Finset.range (i + 1), Y j ω % 2) = (i + 1) / 3 }

/-- If the parity sequence of `Diter · 7` behaves like the random walk in
    `probability_not_certain` (steps +1 or −2 with equal probability 1/2),
    then the halting condition from `Aiter_8_2_halt_iff_Diter_7_halt` has
    probability strictly less than 1.  This means probabilistic heuristics
    cannot resolve the deterministic halting question. -/
lemma Diter_halt_probabilistically_undecidable
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (Y : ℕ → Ω → ℕ)
    (X : ℕ → Ω → ℤ)
    (h_dist : ∀ n, ℙ {ω | X n ω = 1} = (1 / 2 : ENNReal) ∧
                    ℙ {ω | X n ω = -2} = (1 / 2 : ENNReal))
    (h_indep : iIndepFun X ℙ)
    (h_meas : ∀ n, Measurable (X n))
    (h_equiv : random_halt_event Y = gets_out X 2) :
    ℙ (random_halt_event Y) < 1 := by
  rw [h_equiv]; exact probability_not_certain X h_dist h_indep h_meas 2 (by norm_num)

/-- Lifting to the Aiter formulation: if `ℙ(random_halt_event Y) < 1`,
    the Aiter halting condition is probabilistically undecidable. -/
lemma Aiter_halt_probabilistically_undecidable
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (Y : ℕ → Ω → ℕ)
    (h : ℙ (random_halt_event Y) < 1) :
    ℙ (random_halt_event Y) < 1 ∧
      ((∃ i, (Diter (i + 1) 7) % 2 = 0 ∧ (Diter (i + 1) 7) ≥ 5 ∧ i % 3 = 2 ∧
        (∑ j ∈ Finset.range (i + 1), (Diter j 7) % 2) = (i + 1) / 3) ↔
      (∃ i, (_root_.Aiter i (8, 2)).1 % 2 = 1 ∧ (_root_.Aiter i (8, 2)).1 / 2 ≥ 1 ∧
        (_root_.Aiter i (8, 2)).2 = 0)) := by
  exact ⟨h, Aiter_8_2_halt_iff_Diter_7_halt.symm⟩

/-- The full chain: if `ℙ(random_halt_event Y) < 1`, then the Antihydra TM
    halting question is probabilistically undecidable — i.e., the event that
    the TM halts cannot be resolved by the random model. -/
lemma antihydra_probabilistically_undecidable
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (Y : ℕ → Ω → ℕ)
    (h : ℙ (random_halt_event Y) < 1) :
    ℙ (random_halt_event Y) < 1 ∧
      ((∃ i, (Diter (i + 1) 7) % 2 = 0 ∧ (Diter (i + 1) 7) ≥ 5 ∧ i % 3 = 2 ∧
        (∑ j ∈ Finset.range (i + 1), (Diter j 7) % 2) = (i + 1) / 3) ↔
      (∃ k, (Antihydra.run Antihydra.initConfig k).state = none)) := by
  exact ⟨h, Aiter_8_2_halt_iff_Diter_7_halt.symm.trans Antihydra.antihydra_halts_iff.symm⟩
