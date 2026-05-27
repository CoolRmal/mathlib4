/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Quadratic mean differentiability

-/

@[expose] public section

noncomputable section

open scoped Topology NNReal ENNReal

open Filter MeasureTheory Real

/-- Note : hadamard; P is a function defined on E instead of s; no need to assume absolute
continuity at this point as rnDeriv gives junk values.
def HasHadamardQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] (P : E → Measure Ω) (μ : Measure Ω)
    (s : Set E) (θ : E) (A : E →L[ℝ] (Ω →₂[P θ] ℝ)) : Prop :=
  ∀ (h : E) {ι : Type*} (l : Filter ι) (t : ι → ℝ) (a : ι → E), Tendsto t l (𝓝 0) →
    Tendsto a l (𝓝 h) → ∀ᶠ i in l, θ + (t i) • (a i) ∈ s → Tendsto (fun i =>
    (t i)⁻¹ * lpNorm (fun ω => sqrt ((P (θ + (t i) • (a i))).rnDeriv μ ω).toReal -
    sqrt ((P θ).rnDeriv μ ω).toReal -
    2⁻¹ * (A ((t i) • h) ω) * sqrt ((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0)
-/
def HasQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : E → Measure Ω) (μ : Measure Ω)
    (s : Set E) (x : E) (A : E →L[ℝ] (Ω →₂[P x] ℝ)) : Prop :=
  (fun y =>
    lpNorm (fun ω => sqrt ((P y).rnDeriv μ ω).toReal -
    sqrt ((P x).rnDeriv μ ω).toReal -
    2⁻¹ * (A (y - x) ω) * sqrt ((P x).rnDeriv μ ω).toReal) 2 μ) =o[𝓝[s] x] (fun y => y - x)

def HasHadamardQuadraticMeanDerivWithinAt {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E] (P : E → Measure Ω) (μ : Measure Ω)
    (s : Set E) (θ : E) (A : E →L[ℝ] (Ω →₂[P θ] ℝ)) : Prop :=
  ∀ (h : E) (l : Filter (ℝ × E)), Tendsto Prod.fst l (𝓝 0) →
    Tendsto Prod.snd l (𝓝 h) → (∀ᶠ p in l, θ + p.1 • p.2 ∈ s) → Tendsto (fun p =>
    p.1⁻¹ * lpNorm (fun ω => sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
    sqrt ((P θ).rnDeriv μ ω).toReal -
    2⁻¹ * (A (p.1 • h) ω) * sqrt ((P θ).rnDeriv μ ω).toReal) 2 μ) l (𝓝 0)

-- APIs original definition implies this definition?

private lemma lemma1 {Ω : Type*} {mΩ : MeasurableSpace Ω} {m₁ m₂ μ : Measure Ω} [SigmaFinite μ]
    [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ) (hm₂ : m₂ ≪ μ) :
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

private lemma lemma2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {m₁ m₂ μ : Measure Ω} [SigmaFinite μ]
    [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ) (hm₂ : m₂ ≪ μ) :
    (∫ ω, ‖sqrt (m₁.rnDeriv μ ω).toReal +
      sqrt (m₂.rnDeriv μ ω).toReal‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ 2 := by
  sorry

private lemma lim1 {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ] {s : Set E} {θ h : E}
    {A : E →L[ℝ] (Ω →₂[P θ] ℝ)} (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => p.1⁻¹ * ∫ ω,
      (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - sqrt ((P θ).rnDeriv μ ω).toReal -
      2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
      (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) l
      (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 <| squeeze_zero' (g := fun p => ‖p.1‖⁻¹ *
    lpNorm (fun ω => sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
    sqrt ((P θ).rnDeriv μ ω).toReal -
    2⁻¹ * (A (p.1 • h) ω) * sqrt ((P θ).rnDeriv μ ω).toReal) 2 μ * 2) ?_ ?_ ?_
  · filter_upwards with p using norm_nonneg _
  · filter_upwards [he] with p hp
    simp only [norm_mul, norm_inv]
    nth_rw 1 [mul_assoc]
    gcongr
    calc
      ‖∫ ω, (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - sqrt ((P θ).rnDeriv μ ω).toReal -
        2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
        (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ‖
        ≤ ∫ ω, ‖(sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - sqrt ((P θ).rnDeriv μ ω).toReal -
          2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal)‖ *
          ‖(sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal
          + sqrt ((P θ).rnDeriv μ ω).toReal)‖ ∂μ := by
        grw [norm_integral_le_integral_norm]; simp
      _ ≤ (∫ ω, ‖(sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal - sqrt ((P θ).rnDeriv μ ω).toReal -
          2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal)‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ ω, ‖(sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal
          + sqrt ((P θ).rnDeriv μ ω).toReal)‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        refine integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two ?_ ?_
        · sorry
        · sorry
      _ ≤ _ := by
        gcongr
        · exact lpNorm_nonneg
        · rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp)]
          · simp
          · sorry
        · have := hprob _ hp
          have := hprob _ hθ
          exact lemma2 (hs _ hp) (hs _ hθ)
  · have := ((tendsto_zero_iff_abs_tendsto_zero _).1 <| hA h l hzero hh he).mul_const 2
    rw [zero_mul 2] at this
    exact this.congr fun p => by simp
