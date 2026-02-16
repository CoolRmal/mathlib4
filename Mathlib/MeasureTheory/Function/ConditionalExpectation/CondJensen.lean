/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality. We follow the proof in
[Hytonen_VanNeerven_Veraar_Wies_2016].

## Main Statement

* `conditional_jensen`: in a Banach space `E` with finite measure `μ`, if `φ : E → ℝ` is a convex
  lower-semicontinuous function, then for any `f : α → E` such that `f` and `φ ∘ f` are integrable,
  we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`.

-/

@[expose] public section

open MeasureTheory Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- Conditional Jensen's inequality for hereditarily Lindelof Spaces. -/
private lemma conditional_jensen_of_hereditarilyLindelofSpace [HereditarilyLindelofSpace E]
    (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  obtain ⟨L, c, hLc⟩ := hφ_cvx.real_univ_sSup_of_nat_affine_eq hφ_cont
  have hp := ae_all_iff.2 fun i => (L i).comp_condExp_add_const_comm hm hf_int (c i)
  have hw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(L i) ∘ f + const α (c i) | m] a ≤ μ[φ ∘ f | m] a := by
    refine ae_all_iff.2 fun i => condExp_mono ?_ hφ_int ?_
    · exact ((L i).integrable_comp hf_int).add (integrable_const (c i))
    · filter_upwards with a
      simp only [Pi.add_apply, comp_apply, const_apply, ← congrFun hLc.2 (f a), iSup_apply]
      exact le_ciSup (α := ℝ) (bddAbove_def.2 ⟨φ (f a), fun r ⟨z, hz⟩ => hz ▸ hLc.1 z (f a)⟩) i
  filter_upwards [hp, hw] with a hp hw
  simpa [← hLc.2, iSup_congr hp] using ciSup_le hw

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a finite measure `μ`, if
`φ : X → ℝ` is a convex lower-semicontinuous function, then for any `f : α → X` such that `f` and
`φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  borelize E
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  let φY := φ ∘ Y.subtypeL
  have aeinY : ∀ᵐ (x : α) ∂μ, f x ∈ Y := by filter_upwards [htt] with a ha using
    (subset_trans Submodule.subset_span subset_closure) ha
  classical
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem1 : f =ᵐ[μ] fX := by filter_upwards [aeinY] with a ha; simp [fX, fY, ha, reduceDIte]
  have hfX_int : Integrable fX μ := Integrable.congr hf_int lem1
  have hfY_int : Integrable fY μ := by
    refine ⟨?_, hfX_int.2.mono (by simp [fX])⟩
    have hs : MeasurableSet (Y : Set E) := (Submodule.isClosed_topologicalClosure _).measurableSet
    have h_nonempty : (Y : Set E).Nonempty := Set.Nonempty.of_subtype
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset hs h_nonempty aeinY
    refine ⟨Set.codRestrict g Y hg2, (hg1.measurable.codRestrict hg2).stronglyMeasurable, ?_⟩
    filter_upwards [hg3] with a ha1
    have : g a ∈ Y := hg2 a
    simp_all [fY, Set.codRestrict]
  have lem2 : μ[f | m] =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] := calc
    _ =ᵐ[μ] μ[fX | m] := condExp_congr_ae lem1
    _ =ᵐ[μ] _ := (Y.subtypeL.comp_condExp_comm hfY_int).symm
  have lem3 : φ ∘ f =ᵐ[μ] φY ∘ fY := by filter_upwards [lem1] with a ha; simp [φY, ha, fX]
  calc
    φ ∘ μ[f | m]
      =ᵐ[μ] φY ∘ μ[fY | m] := by filter_upwards [lem2] with a ha; simp [φY, ha]
    _ ≤ᵐ[μ] μ[φY ∘ fY | m] := conditional_jensen_of_hereditarilyLindelofSpace hm
      (hφ_cvx.comp_linearMap Y.subtype) (hφ_cont.comp Y.subtypeL.cont) hfY_int (hφ_int.congr lem3)
    _ =ᵐ[μ] μ[φ ∘ f | m] := condExp_congr_ae lem3.symm

variable [FiniteDimensional ℝ E]

/-- **Conditional Jensen's inequality**: in a finite dimesnional Banach space `X` with a finite
measure `μ`, if `φ : X → ℝ` is a convex function, then for any `f : α → X` such that `f` and
`φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen_finite_dim (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  conditional_jensen hm hφ_cvx
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int
