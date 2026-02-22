/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

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

open MeasureTheory Function Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α}

/-- A measure is called semifinite if any measurable set with positive measure has a subset with
finite positive measure. -/
class SemiFinite (μ : Measure α) : Prop where
  exists_lt_top ⦃s : Set α⦄ (hms : MeasurableSet s) (hs : 0 < μ s) : ∃ t, t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤

/-- A measure is semifinite iff any measurable set with positive measure has a measurable subset
with finite positive measure. -/
theorem SemiFinite.iff :
    SemiFinite μ ↔ ∀ s, MeasurableSet s → 0 < μ s →
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤ where
  mp h s hms hs := by
    obtain ⟨t, ht⟩ := h.exists_lt_top hms hs
    refine ⟨s ∩ toMeasurable μ t, hms.inter ?_, inter_subset_left, ?_, ?_⟩
    · exact measurableSet_toMeasurable μ t
    · exact ht.2.1.trans_le (measure_mono (subset_inter ht.1 (subset_toMeasurable μ t)))
    · exact ((measure_toMeasurable t) ▸ ht.2.2).trans_le' (measure_mono inter_subset_right)
  mpr h := by
    constructor
    intro s hms hs
    obtain ⟨t, ht⟩ := h s hms hs
    exact ⟨t, ht.2⟩

/-- A measure is semifinite iff any null measurable set with positive measure has a subset with
finite positive measure. -/
theorem Semifinite.iff_nullMeasurable :
    SemiFinite μ ↔ ∀ s, NullMeasurableSet s μ → 0 < μ s → ∃ t, t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤ where
  mp h s hms hs := by
    obtain ⟨t, ht⟩ := h.exists_lt_top (measurableSet_toMeasurable μ s) (by simp [hs])
    have : μ (t ∩ s) = μ t :=
      measure_inter_conull' (μ.mono_null (by grind) (ae_eq_set.1 hms.toMeasurable_ae_eq).1)
    exact ⟨t ∩ s, inter_subset_right, this ▸ ht.2.1, this ▸ ht.2.2⟩
  mpr h := by
    constructor
    exact fun s hs hs' => h s hs.nullMeasurableSet hs'

theorem measure_eq_zero_of_measure_inter_finite_eq_zero [SemiFinite μ]
    {s : Set α} (hs : ∀ t, μ t < ⊤ → μ (s ∩ t) = 0) : μ s = 0 := by
  by_contra! hne
  obtain ⟨t, ht⟩ := SemiFinite.exists_lt_top (by positivity)
  have := Set.inter_eq_self_of_subset_right ht.1 ▸ hs t ht.2.2
  grind

instance [SigmaFinite μ] : SemiFinite μ where
  exists_lt_top s hs := by
    obtain ⟨n, hn⟩ := (μ.exists_measure_inter_spanningSets_pos s).2 hs
    refine ⟨s ∩ spanningSets μ n, Set.inter_subset_left, hn, ?_⟩
    exact (measure_spanningSets_lt_top μ n).trans_le' (measure_mono Set.inter_subset_right)

theorem ae_iff_ae_restrict [SemiFinite μ] {p : α → Prop}
    (hp : ∀ t, MeasurableSet t → μ t < ⊤ → ∀ᵐ a ∂(μ.restrict t), p a) :
    ∀ᵐ a ∂μ, p a := by
  simp_all only [ae_iff]
  refine measure_eq_zero_of_measure_inter_finite_eq_zero fun t ht => ?_
  simpa [← μ.restrict_apply' ht] using hp t ht ht'

/-- Conditional Jensen's inequality for hereditarily Lindelof Spaces. -/
private lemma conditional_jensen_of_hereditarilyLindelofSpace [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ Set.univ φ)
    (hφ_cont : LowerSemicontinuous φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
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

/-- Conditional Jensen's inequality for finite measures. -/
private theorem conditional_jensen_of_finite [IsFiniteMeasure μ] (hm : m ≤ mα)
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

theorem condExp_restrict_ae_eq_restrict {s : Set α} (hm : m ≤ mα) [SemiFinite (μ.trim hm)]
    (hs_m : MeasurableSet[m] s) (hf_int : Integrable f μ) :
    (μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m] := by
  sorry

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a semifinite measure `μ`, if
`φ : X → ℝ` is a convex lower-semicontinuous function, then for any `f : α → X` such that `f` and
`φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen (hm : m ≤ mα) [SemiFinite μ]
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  refine ae_iff_ae_restrict ?_ fun t ht ht' => ?_
  · sorry
  · have := Restrict.isFiniteMeasure μ (hs := fact_iff.2 ht')
    have := conditional_jensen_of_finite (μ := μ.restrict t) hm hφ_cvx hφ_cont hf_int.restrict hφ_int.restrict

variable [FiniteDimensional ℝ E]

/-- **Conditional Jensen's inequality**: in a finite dimesnional Banach space `X` with a finite
measure `μ`, if `φ : X → ℝ` is a convex function, then for any `f : α → X` such that `f` and
`φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen_finite_dim [SemiFinite μ] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  conditional_jensen hm hφ_cvx
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int
