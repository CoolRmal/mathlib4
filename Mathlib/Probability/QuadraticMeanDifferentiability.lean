/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv


/-!
# Quadratic mean differentiability

-/

@[expose] public section

noncomputable section

open scoped Topology NNReal ENNReal

open Filter MeasureTheory Real

namespace QMD

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

/-- The difference of squares formula for two square root densities of probability measures. -/
private lemma integral_diff_sq_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {m₁ m₂ μ : Measure Ω}
    [SigmaFinite μ] [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ)
    (hm₂ : m₂ ≪ μ) :
    ∫ ω, (sqrt (m₁.rnDeriv μ ω).toReal - sqrt (m₂.rnDeriv μ ω).toReal) *
      (sqrt (m₁.rnDeriv μ ω).toReal + sqrt (m₂.rnDeriv μ ω).toReal) ∂μ = 0 := by
  rw [integral_congr_ae, integral_sub (Measure.integrable_toReal_rnDeriv (μ := m₁) (ν := μ))
      (Measure.integrable_toReal_rnDeriv (μ := m₂) (ν := μ)),
      Measure.integral_toReal_rnDeriv hm₁, Measure.integral_toReal_rnDeriv hm₂]
  · norm_num
  · filter_upwards with ω
    calc
      _ = sqrt (m₁.rnDeriv μ ω).toReal ^ 2 - sqrt (m₂.rnDeriv μ ω).toReal ^ 2 := by ring
      _ = (m₁.rnDeriv μ ω).toReal - (m₂.rnDeriv μ ω).toReal := by
        simp [sq_sqrt ENNReal.toReal_nonneg]

/-- A lemma saying that the `L²` norm of the sum of two square root densities is bounded above by
`2`. -/
private lemma integral_sq_sum_le_two {Ω : Type*} {mΩ : MeasurableSpace Ω} {m₁ m₂ μ : Measure Ω}
    [SigmaFinite μ] [IsProbabilityMeasure m₁] [IsProbabilityMeasure m₂] (hm₁ : m₁ ≪ μ)
    (hm₂ : m₂ ≪ μ) :
    (∫ ω, ‖sqrt (m₁.rnDeriv μ ω).toReal +
      sqrt (m₂.rnDeriv μ ω).toReal‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ 2 := by
  rw [← Real.sqrt_eq_rpow]
  nth_rw 2 [show 2 = √4 from by symm; rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num]
  apply Real.sqrt_le_sqrt
  calc
  _ ≤ ∫ ω, 2 * (m₁.rnDeriv μ ω).toReal + 2 * (m₂.rnDeriv μ ω).toReal ∂μ := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with ω using Real.rpow_nonneg (norm_nonneg _) _
    · refine Integrable.add ?_ ?_
      <;> exact Measure.integrable_toReal_rnDeriv.const_mul 2
    · filter_upwards with ω
      calc
        _ = (sqrt (m₁.rnDeriv μ ω).toReal + sqrt (m₂.rnDeriv μ ω).toReal) ^ 2 := by simp [sq_abs]
        _ ≤ 2 * (sqrt (m₁.rnDeriv μ ω).toReal) ^ 2 + 2 * (sqrt (m₂.rnDeriv μ ω).toReal) ^ 2 := by
          linarith [sq_nonneg (sqrt (m₁.rnDeriv μ ω).toReal - sqrt (m₂.rnDeriv μ ω).toReal)]
        _ = 2 * (m₁.rnDeriv μ ω).toReal + 2 * (m₂.rnDeriv μ ω).toReal := by
          simp [sq_sqrt ENNReal.toReal_nonneg]
  _ = 2 * ∫ ω, (m₁.rnDeriv μ ω).toReal ∂μ + 2 * ∫ ω, (m₂.rnDeriv μ ω).toReal ∂μ := by
    rw [integral_add, integral_const_mul, integral_const_mul]
    <;> exact Measure.integrable_toReal_rnDeriv.const_mul 2
  _ = 4 := by
    rw [Measure.integral_toReal_rnDeriv hm₁, Measure.integral_toReal_rnDeriv hm₂]
    norm_num

private lemma tendsto_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E] [Module ℝ E]
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
          · refine (AEStronglyMeasurable.sub ?_ ?_).sub (AEStronglyMeasurable.mul ?_ ?_)
            rotate_left 2
            · exact (Lp.stronglyMeasurable (A (p.1 • h))).aestronglyMeasurable.const_mul _
            all_goals exact ((Measure.measurable_rnDeriv
              _ _).aemeasurable.ennreal_toReal.sqrt).aestronglyMeasurable
        · have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
          have : IsProbabilityMeasure (P θ) := hprob _ hθ
          exact integral_sq_sum_le_two (hs _ hp) (hs _ hθ)
  · have := ((tendsto_zero_iff_abs_tendsto_zero _).1 <| hA h l hzero hh he).mul_const 2
    rw [zero_mul 2] at this
    exact this.congr fun p => by simp

private lemma tendsto_integral_score {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E]
    [Module ℝ E] [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ]
    {s : Set E} {θ h : E} {A : E →L[ℝ] (Ω →₂[P θ] ℝ)}
    (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    (hzero : Tendsto Prod.fst l (𝓝 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    Tendsto (fun p => ∫ ω, 2⁻¹ * A h ω * sqrt ((P θ).rnDeriv μ ω).toReal *
      (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) l
      (𝓝 <| ∫ ω, A h ω ∂P θ) := by
  sorry

/-- **Mean Zero Score**: . -/
theorem integral_score_eq_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] {P : E → Measure Ω} {μ : Measure Ω} [SigmaFinite μ] {s : Set E} {θ h : E}
    {A : E →L[ℝ] (Ω →₂[P θ] ℝ)} (hA : HasHadamardQuadraticMeanDerivWithinAt P μ s θ A) (hθ : θ ∈ s)
    (hprob : ∀ x ∈ s, IsProbabilityMeasure (P x)) (hs : ∀ x ∈ s, P x ≪ μ) {l : Filter (ℝ × E)}
    [l.NeBot] (hzero : Tendsto Prod.fst l (𝓝[≠] 0)) (hh : Tendsto Prod.snd l (𝓝 h))
    (he : ∀ᶠ p in l, θ + p.1 • p.2 ∈ s) :
    ∫ ω, A h ω ∂P θ = 0 := by
  refine tendsto_nhds_unique (zero_add (∫ ω, A h ω ∂P θ) ▸
    (tendsto_zero hA hθ hprob hs (tendsto_nhds_of_tendsto_nhdsWithin hzero) hh he).add
    (tendsto_integral_score hA hθ hprob hs (tendsto_nhds_of_tendsto_nhdsWithin hzero) hh he)) ?_
  apply EventuallyEq.tendsto (EventuallyEq.symm ?_)
  filter_upwards [he, (tendsto_nhdsWithin_iff.1 hzero).2] with p hp hn
  calc
    0 = p.1⁻¹ * 0 := by simp
    _ = p.1⁻¹ * (∫ ω, (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          sqrt ((P θ).rnDeriv μ ω).toReal) * (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) := by
        have : IsProbabilityMeasure (P (θ + p.1 • p.2)) := hprob _ hp
        have : IsProbabilityMeasure (P θ) := hprob _ hθ
        rw [integral_diff_sq_eq_zero (hs _ hp) (hs _ hθ)]
    _ = p.1⁻¹ * (∫ ω, (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          sqrt ((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal +
          2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) := by simp
    _ = p.1⁻¹ * (∫ ω, (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          sqrt ((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ +
          ∫ ω, 2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) := by
        simp only [add_mul]
        rw [integral_add]
        · sorry
        · sorry
    _ = p.1⁻¹ * (∫ ω, (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          sqrt ((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) +
          p.1⁻¹ * (∫ ω, 2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) := by simp [mul_add]
    _ = p.1⁻¹ * (∫ ω, (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal -
          sqrt ((P θ).rnDeriv μ ω).toReal - 2⁻¹ * A (p.1 • h) ω * sqrt ((P θ).rnDeriv μ ω).toReal) *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal + sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) +
          p.1⁻¹ * (∫ ω, 2⁻¹ * p.1 * A h ω * sqrt ((P θ).rnDeriv μ ω).toReal *
          (sqrt ((P (θ + p.1 • p.2)).rnDeriv μ ω).toReal +
          sqrt ((P θ).rnDeriv μ ω).toReal) ∂μ) := by
        have : IsProbabilityMeasure (P θ) := hprob _ hθ
        simp only [map_smul, add_right_inj, mul_eq_mul_left_iff, inv_eq_zero,
          fun ω => (mul_comm (sqrt ((P θ).rnDeriv μ ω).toReal) (2⁻¹ * (p.1 • A h) ω)).symm,
          fun ω => (mul_comm (sqrt ((P θ).rnDeriv μ ω).toReal) (2⁻¹ * p.1 * (A h ω))).symm]
        refine Or.inl (integral_congr_ae ?_)
        have := Lp.coeFn_smul p.1 (A h)
        filter_upwards with ω
    _ = _ := by
        simp only [map_smul, mul_comm 2⁻¹ p.1, add_right_inj, mul_assoc]
        rw [integral_const_mul_of_integrable (c := p.1), inv_mul_cancel_left₀ hn]
        sorry

end QMD
