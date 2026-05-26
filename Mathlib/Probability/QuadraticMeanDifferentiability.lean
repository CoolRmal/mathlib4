/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
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

def QuadraticMeanDifferentiableAt {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : E → Measure Ω) (μ : Measure Ω) (θ : E) (s : Set E)
    (A : E →L[ℝ] (Ω →₂[P θ] ℝ)) : Prop :=
  (fun h => lpNorm
    (fun ω => sqrt ((P (θ + h)).rnDeriv μ ω).toReal -
    sqrt ((P θ).rnDeriv μ ω).toReal - 2⁻¹ * (A h ω) * sqrt ((P θ).rnDeriv μ ω).toReal) 2 μ)
    =o[𝓝[s] 0] norm

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : E → Measure Ω} {μ : Measure Ω} {θ : E} {s : Set E} {A : E →L[ℝ] (Ω →₂[P θ] ℝ)}

lemma lemma1 {m₁ m₂ : Measure Ω} [SigmaFinite μ] [IsProbabilityMeasure m₁]
    [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ) (hm₂ : m₂ ≪ μ) :
    ∫ ω, (sqrt (m₁.rnDeriv μ ω).toReal - sqrt (m₂.rnDeriv μ ω).toReal) *
      (sqrt (m₁.rnDeriv μ ω).toReal + sqrt (m₂.rnDeriv μ ω).toReal) ∂μ = 0 := by
  rw [integral_congr_ae, integral_sub (Measure.integrable_toReal_rnDeriv (μ := m₁) (ν := μ))
      (Measure.integrable_toReal_rnDeriv (μ := m₂) (ν := μ)),
      Measure.integral_toReal_rnDeriv hm₁, Measure.integral_toReal_rnDeriv hm₂]
  · simp
  · filter_upwards with ω
    calc
      _ = sqrt (m₁.rnDeriv μ ω).toReal ^ 2 - sqrt (m₂.rnDeriv μ ω).toReal ^ 2 := by ring
      _ = (m₁.rnDeriv μ ω).toReal - (m₂.rnDeriv μ ω).toReal := by
        simp [sq_sqrt ENNReal.toReal_nonneg]

theorem lim1 (hs : ∀ x ∈ s, P x ≪ μ) (h : E) :
    Tendsto (fun t => ∫ ω,
      (sqrt ((P (θ + t • h)).rnDeriv μ ω).toReal - sqrt ((P θ).rnDeriv μ ω).toReal -
      2⁻¹ * A h ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
      (sqrt ((P (θ + t • h)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) (𝓝[>] 0)
      (𝓝 <| ∫ ω, A h ω * ((P θ).rnDeriv μ ω).toReal ∂μ) := by
  sorry

theorem lim2 (hs : ∀ x ∈ s, P x ≪ μ) (h : E) :
    Tendsto (fun t => ∫ ω, A h ω * sqrt ((P θ).rnDeriv μ ω).toReal *
      (sqrt ((P (θ + t • h)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) (𝓝[>] 0)
      (𝓝 <| ∫ ω, A h ω * ((P θ).rnDeriv μ ω).toReal ∂μ) := by
  sorry

end ProbabilityTheory
