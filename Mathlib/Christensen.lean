import Mathlib

open MeasureTheory Measure Metric
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {μ ν : Measure X}

class UniformlyDistributed (μ : Measure X) : Prop where
  protected uniformlydistributed :
   ∀ ⦃r : ℝ⦄, 0 < r → ∀ x y : X, μ (ball x r) = μ (ball y r) ∧ 0 < μ (ball x r) ∧ μ (ball x r) < ⊤

omit [BorelSpace X] in
/-- Outer regular measures are determined by values on open sets. -/
theorem eq_of_eq_on_isOpen [OuterRegular μ] [OuterRegular ν]
    (hμν : ∀ U, IsOpen U → μ U = ν U) : μ = ν := by
  ext s ms
  rw [Set.measure_eq_iInf_isOpen, Set.measure_eq_iInf_isOpen]
  congr! 4 with t _ ht2
  exact hμν t ht2

/-- **Christensen's Lemma**: Uniformly distributed measures are unique up to a constant. -/
theorem uniformly_distri_unique [OuterRegular μ] [OuterRegular ν]
    [UniformlyDistributed μ] [UniformlyDistributed ν] : ∃ c : NNReal, μ = c • ν := by
  sorry

variable {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
variable [BorelSpace E] [FiniteDimensional ℝ E]

theorem measure_toSphere_outer_regular (m : Measure E) [m.IsAddHaarMeasure] :
    OuterRegular m.toSphere := by
  sorry

theorem measure_toSphere_uniformlydist (m : Measure E) [m.IsAddHaarMeasure] :
    UniformlyDistributed m.toSphere := by
  sorry

theorem hausdorffMeasure_restirct_sphere_outer_regular : OuterRegular
    (μH[↑(Module.finrank ℝ E) - 1].comap Subtype.val : Measure (sphere (0 : E) 1)) := by
  sorry

theorem hausdorffMeasure_restrict_sphere_uniformlydist : UniformlyDistributed
    (μH[↑(Module.finrank ℝ E) - 1].comap Subtype.val : Measure (sphere (0 : E) 1)) := by
  sorry

/-- The restriction of the Hausdorff `n-1` dimensional measure in `ℝⁿ` is the same as -/
theorem hausdorff_eq_measure.toSphere (m : Measure E) [m.IsAddHaarMeasure] :
    (μH[↑(Module.finrank ℝ E) - 1].comap Subtype.val : Measure (sphere (0 : E) 1)) =
    m.toSphere := by
  sorry

#min_imports
