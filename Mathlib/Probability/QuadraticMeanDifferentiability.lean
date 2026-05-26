/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Quadratic mean differentiability

-/

@[expose] public section

noncomputable section

open scoped Topology NNReal ENNReal

open Filter MeasureTheory Real

namespace ProbabilityTheory

namespace QuadraticMeanDifferentiability

def QuadraticMeanDifferentiableAt {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : E → Measure Ω) (μ : Measure Ω) (θ : E) (s : Set E) : Prop :=
  ∃ A : E →L[ℝ] (Ω →₂[P θ] ℝ), (fun h ↦ lpNorm
    (fun ω => sqrt (μ.rnDeriv (P (θ + h)) ω).toReal -
    sqrt (μ.rnDeriv (P θ) ω).toReal - 2⁻¹ * (A h ω) * sqrt (μ.rnDeriv (P θ) ω).toReal) 2 μ)
    =o[𝓝[s] 0] norm



end QuadraticMeanDifferentiability

end ProbabilityTheory
