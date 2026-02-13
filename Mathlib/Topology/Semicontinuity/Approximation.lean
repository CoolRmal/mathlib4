/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Approximation to convex functions

In this file we show that a convex lower-semicontinuous function is the upper envelope of a family
of continuous affine functions.

## Main Statement

*

## References

*

-/

@[expose] public section

open Function Set RCLike ContinuousLinearMap

variable {𝕜 E : Type*} {s : Set E} {φ : E → ℝ} [RCLike 𝕜]

theorem ContinuousLinearMap.coprod_comp_inl_inr {R M M₁ M₂ : Type*}
    [Semiring R] [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂] [AddCommMonoid M]
    [Module R M] [ContinuousAdd M] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [ContinuousAdd M₂] (f : M × M₁ →L[R] M₂) :
    (f ∘L .inl R M M₁).coprod (f ∘L .inr R M M₁) = f := by
  sorry

theorem pos_of_mul_lt_lt {R : Type*} [Semiring R] [LinearOrder R] {a b c : R} [ExistsAddOfLE R]
    [PosMulStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R]
    (h : a * b < a * c) (hbc : b < c) :
    0 < a := by
  rcases lt_trichotomy 0 a with (ha | ha | ha)
  · exact ha
  · subst ha; simp_all
  · grind [mul_lt_mul_of_neg_left hbc ha]

theorem ConvexOn.convex_re_epigraph [AddCommMonoid E] [Module ℝ E] (hφcv : ConvexOn ℝ s φ) :
    Convex ℝ { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  have lem : { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } =
    ((LinearMap.id : E →ₗ[ℝ] E).prodMap reLm)⁻¹' { p : E × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2 } := by simp
  exact lem ▸ hφcv.convex_epigraph.linear_preimage _

variable [TopologicalSpace E]

theorem LowerSemicontinuousOn.isClosed_re_epigraph (hsc : IsClosed s)
    (hφ_cont : LowerSemicontinuousOn φ s) :
    IsClosed  { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  let A := { p : E × EReal | p.1 ∈ s ∧ φ p.1 ≤ p.2 }
  have hC : { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
    = (Prod.map id ((Real.toEReal ∘ re) : 𝕜 → EReal))⁻¹' A := by simp [A]
  refine hC.symm ▸ IsClosed.preimage ?_ ?_
  · exact continuous_id.prodMap <| continuous_coe_real_ereal.comp reCLM.cont
  · exact (lowerSemicontinuousOn_iff_isClosed_epigraph hsc).1
      (continuous_coe_real_ereal.comp_lowerSemicontinuousOn hφ_cont (EReal.coe_strictMono.monotone))

variable [AddCommGroup E] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset is the
supremum of a family of functions that are the restrictions to `s` of continuous affine linear
functions in `E`. -/
theorem ConvexOn.sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    sSup {f | f ≤ s.restrict φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ),
    f = s.restrict (re ∘ l) + const s c} = s.restrict φ := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
  have hl {x : s} {a} (hax : a < φ x) : ∃ f : {f | f ≤ s.restrict φ ∧
    ∃ (l : StrongDual 𝕜 E) (c : ℝ), f = s.restrict (re ∘ l) + const s c}, f.1 x = a := by
    obtain ⟨L, ⟨b, hLb⟩⟩ := geometric_hahn_banach_point_closed (𝕜 := 𝕜) hφcv.convex_re_epigraph
      (hφc.isClosed_re_epigraph hsc) (by simp [A, hax] : (x.1, ofReal a) ∉ A)
    let u := L.comp (.inl 𝕜 E 𝕜)
    let c := (re (L (0, 1)))⁻¹
    refine ⟨⟨s.restrict (re ∘ (- c • u)) + const s (c * re (u x) + a), fun z => ?_, ?_⟩, ?_⟩
    · have hv (v : 𝕜) : v * L (0, 1) = L (0, v) := by rw [← smul_eq_mul, ← map_smul]; simp
      have hine {w : E} (h : w ∈ s) : re (L (x, 0)) + re (L (0, 1)) * a
        < re (L (w, 0)) + re (L (0, 1)) * φ w := by
        have hw := hLb.1.trans (hLb.2 _ (by simp [A, h] : (w, ofReal (φ w)) ∈ A))
        rw [← coprod_comp_inl_inr L] at hw
        simpa [← hv (ofReal a), ← hv (ofReal (φ w)), mul_comm a, mul_comm (φ w)] using hw
      have hc : 0 < c := inv_pos.2 (pos_of_mul_lt_lt (lt_of_add_lt_add_left (hine x.2)) hax)
      simpa [smul_re, u, c, mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (inv_pos.1 hc))]
        using mul_le_mul_of_nonneg_left (hine z.2).le hc.le
    · exact ⟨- c • u, c * re (u x) + a, rfl⟩
    · simp [u, c, smul_re]
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · choose f hf using hl (show φ x - 1 < φ x from by grind)
    exact ⟨φ x - 1, hf ▸ mem_range_self _⟩
  · exact hf ▸ f.2.1 x
  · obtain ⟨z, hz⟩ := exists_between hr
    obtain ⟨f, hf⟩ := hl hz.2
    exact ⟨z, hf ▸ mem_range_self _, hz.1⟩

theorem Convex.sSup_countable_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    IsLUB {f : E → ℝ | ∃ (l : StrongDual ℝ E) (c : ℝ), f = l + const E c ∧ f ≤ φ} φ := by
  sorry

/-- Suppose `E` is hereditarily Lindelöf. A function `φ : E → ℝ` that is convex and
lower-semicontinuous on a closed convex subset is the supremum of a countable family of functions
that are the restrictions to `s` of continuous affine linear functions in `E`. -/
theorem ConvexOn.isLUB_countable_affine [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hscv : Convex ℝ s) (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ 𝓕 : Set (s → ℝ), 𝓕.Countable ∧ IsLUB 𝓕 (s.restrict φ) ∧ ∀ f ∈ 𝓕,
    ∃ (l : StrongDual ℝ E) (c : ℝ), f = s.restrict l + const s c := by
  sorry

theorem Convex.isLUB_countable_affine [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ 𝓕 : Set (E → ℝ), 𝓕.Countable ∧ IsLUB 𝓕 φ ∧ ∀ f ∈ 𝓕,
    ∃ (l : StrongDual ℝ E) (c : ℝ), f = l + const E c := by
  sorry

#min_imports
