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
public import Mathlib.Topology.Semicontinuity.Lindelof

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

@[simp]
theorem ContinuousLinearMap.coprod_comp_inl_inr {R M M₁ M₂ : Type*}
    [Semiring R] [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂] [AddCommMonoid M]
    [Module R M] [ContinuousAdd M] [AddCommMonoid M₁] [Module R M₁] [ContinuousAdd M₁]
    [AddCommMonoid M₂] [Module R M₂] [ContinuousAdd M₂] (f : M × M₁ →L[R] M₂) :
    (f ∘L .inl R M M₁).coprod (f ∘L .inr R M M₁) = f := by
  rw [← ContinuousLinearMap.comp_coprod, ContinuousLinearMap.coprod_inl_inr, comp_id]

theorem pos_of_mul_lt_lt {R : Type*} [Semiring R] [LinearOrder R] {a b c : R} [ExistsAddOfLE R]
    [PosMulStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R]
    (h : a * b < a * c) (hbc : b < c) :
    0 < a := by
  rcases lt_trichotomy 0 a with (ha | ha | ha)
  · exact ha
  · subst ha; simp_all
  · grind [mul_lt_mul_of_neg_left hbc ha]

variable {𝕜 E : Type*} {s : Set E} {φ : E → ℝ} [RCLike 𝕜]

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

/-- This is an auxiliary lemma used in the proof of ConvexOn.sSup_affine_eq. -/
lemma exists_affine {x : s} {a} (hax : a < φ x) (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ f : {f | f ≤ s.restrict φ ∧
    ∃ (l : StrongDual 𝕜 E) (c : ℝ), f = s.restrict (re ∘ l) + const s c}, f.1 x = a := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
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
      simpa [-coprod_comp_inl_inr, ← hv (ofReal a), ← hv (ofReal (φ w)), mul_comm a,
        mul_comm (φ w)] using hw
    have hc : 0 < c := inv_pos.2 (pos_of_mul_lt_lt (lt_of_add_lt_add_left (hine x.2)) hax)
    simpa [smul_re, u, c, mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (inv_pos.1 hc))]
      using mul_le_mul_of_nonneg_left (hine z.2).le hc.le
  · exact ⟨- c • u, c * re (u x) + a, rfl⟩
  · simp [u, c, smul_re]

/-- A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset is the
supremum of a family of functions that are the restrictions to `s` of continuous affine linear
functions in `E`. -/
theorem ConvexOn.sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    sSup {f | f ≤ s.restrict φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ),
    f = s.restrict (re ∘ l) + const s c} = s.restrict φ := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨f, hf⟩ := exists_affine (𝕜 := 𝕜) (show φ x - 1 < φ x from by grind) hsc hφc hφcv
    exact ⟨φ x - 1, hf ▸ mem_range_self _⟩
  · exact hf ▸ f.2.1 x
  · obtain ⟨z, hz⟩ := exists_between hr
    obtain ⟨f, hf⟩ := exists_affine (𝕜 := 𝕜) hz.2 hsc hφc hφcv
    exact ⟨z, hf ▸ mem_range_self _, hz.1⟩

lemma sSup_comp {α β γ : Type*} [ConditionallyCompleteLattice γ] (f : α ≃ β) {s : Set (β → γ)}
    (hs : s.Nonempty) (hbdd : BddAbove s) :
    (sSup s) ∘ f = sSup ((fun g => g ∘ f) '' s) := by
  refine OrderIso.map_csSup' ⟨⟨(fun g => g ∘ f), (fun h => h ∘ f.symm),
    by grind, by grind⟩, ?_⟩ hs hbdd
  simp only [Equiv.coe_fn_mk]
  refine ⟨fun hp => fun x => ?_, fun hq => fun x => hq (f x)⟩
  rw [← EquivLike.apply_coe_symm_apply f x]
  exact hp (f.symm x)

theorem ConvexOn.univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    sSup {f | f ≤ φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) + const E c} = φ := by
  let 𝓕 := {f | f ≤ φ ∘ Subtype.val ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) ∘ Subtype.val +
    const univ c}
  have := hφcv.sSup_affine_eq (𝕜 := 𝕜) isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφc)
  simp only [restrict_eq] at this
  calc
  _ = sSup ((fun g => g ∘ (Equiv.Set.univ E).symm) '' 𝓕) := by
    congr
    ext f
    refine ⟨fun ⟨hp, l, c, hlc⟩ => ⟨f ∘ Subtype.val, ⟨fun x => hp (Subtype.val x), ⟨l, c, ?_⟩⟩, ?_⟩,
      fun ⟨a, ⟨⟨h, ⟨l, c, hlc⟩⟩, hb⟩⟩ => ⟨fun x => ?_, ⟨l, c, ?_⟩⟩⟩
    · ext x
      simpa using congrFun hlc x
    · ext x; simp
    · simpa using hb ▸ h ⟨x, trivial⟩
    · subst hlc
      simpa using hb.symm
  _ = sSup 𝓕 ∘ (Equiv.Set.univ E).symm := by
    refine (sSup_comp (Equiv.Set.univ E).symm ?_ ?_).symm
    · obtain ⟨f, hf⟩ := exists_affine (𝕜 := 𝕜) (by grind : φ 0 - 1 < φ (⟨0, @mem_univ E 0⟩ : univ))
        isClosed_univ (lowerSemicontinuousOn_univ_iff.2 hφc) hφcv
      exact ⟨f, f.2⟩
    · exact (bddAbove_def.2 ⟨φ ∘ Subtype.val, fun y hy => hy.1⟩)
  _ = φ ∘ Subtype.val ∘ (Equiv.Set.univ E).symm :=
    congrArg (fun g => g ∘ (Equiv.Set.univ E).symm) this
  _ = φ := by ext; simp

/-- Suppose `E` is hereditarily Lindelöf. A function `φ : E → ℝ` that is convex and
that are the restrictions to `s` of continuous affine linear functions in `E`. -/
theorem ConvexOn.sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ 𝓕' : Set (s → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = s.restrict φ ∧ ∀ f ∈ 𝓕',
    ∃ (l : StrongDual 𝕜 E) (c : ℝ), f = s.restrict (re ∘ l) + const s c := by
  let 𝓕 := {f | f ≤ s.restrict φ ∧
    ∃ (l : StrongDual 𝕜 E) (c : ℝ), f = s.restrict (re ∘ l) + const s c}
  have hl : IsLUB 𝓕 (s.restrict φ) := by sorry
  have hr : ∀ f ∈ 𝓕, LowerSemicontinuous f := by sorry
  obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
  refine ⟨𝓕', h𝓕'.2.1, IsLUB.csSup_eq ?_ ?_, fun f => ?_⟩
  sorry

theorem ConvexOn.univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ 𝓕 : Set (E → ℝ), 𝓕.Countable ∧ IsLUB 𝓕 φ ∧ ∀ f ∈ 𝓕,
    ∃ (l : StrongDual ℝ E) (c : ℝ), f = l + const E c := by
  sorry

#min_imports
