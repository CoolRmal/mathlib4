/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Semicontinuity.Lindelof

/-!
# Approximation to convex functions

In this file we show that a convex lower-semicontinuous function is the upper envelope of a family
of continuous affine linear functions. We follow the proof in [bourbaki1987].

## Main Statement

* `sSup_affine_eq` : A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed
  convex subset `s` is the supremum of a family of functions that are the restrictions to `s` of
  continuous affine linear functions.
* `sSup_of_countable_affine_eq` : Suppose `E` is a `HereditarilyLindelofSpace`. A function
  `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset `s` is the supremum
  of a family of countably many functions that are the restrictions to `s` of continuous affine
  linear functions.

-/

@[expose] public section

open scoped Topology

open Function Set RCLike ContinuousLinearMap Filter

namespace ConvexOn

variable {𝕜 E F : Type*} {s : Set E} {φ : E → ℝ} [RCLike 𝕜]

theorem convex_re_epigraph [AddCommMonoid E] [Module ℝ E] (hφcv : ConvexOn ℝ s φ) :
    Convex ℝ { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  have lem : { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } =
    ((LinearMap.id : E →ₗ[ℝ] E).prodMap reLm)⁻¹' { p : E × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2 } := by simp
  exact lem ▸ hφcv.convex_epigraph.linear_preimage _

variable [TopologicalSpace E]

theorem _root_.LowerSemicontinuousOn.isClosed_re_epigraph (hsc : IsClosed s)
    (hφ_cont : LowerSemicontinuousOn φ s) :
    IsClosed  { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 } := by
  let A := { p : E × EReal | p.1 ∈ s ∧ φ p.1 ≤ p.2 }
  have hC : { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
    = (Prod.map id ((Real.toEReal ∘ re) : 𝕜 → EReal))⁻¹' A := by simp [A]
  refine hC.symm ▸ IsClosed.preimage ?_ ?_
  · exact continuous_id.prodMap <| continuous_coe_real_ereal.comp reCLM.cont
  · exact (lowerSemicontinuousOn_iff_isClosed_epigraph hsc).1
      (continuous_coe_real_ereal.comp_lowerSemicontinuousOn hφ_cont (EReal.coe_strictMono.monotone))

section RCLike

variable [AddCommGroup E] [Module ℝ E] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] {c : ConvexCone ℝ E}

/-- Let `φ : E → ℝ` be a positively homogeneous function on a pointed convex cone `c`. If
`l : E →L[𝕜] 𝕜` and `b : ℝ` satisfy `re ∘ l + b ≤ φ` on `c`, then `re ∘ l ≤ φ` on `c` and `b ≤ 0`.
This is an auxiliary lemma used in the proof of `convexCone_sSup_linear_eq.` -/
lemma _root_.linear_le_and_nonpos_of_affine_le (hcp : c.Pointed)
    (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) {l : E →L[𝕜] 𝕜} {b : ℝ}
    (hlb : c.carrier.restrict (re ∘ l) + const c.carrier b ≤ c.carrier.restrict φ) :
    c.carrier.restrict (re ∘ l) ≤ c.carrier.restrict φ ∧ b ≤ 0 := by
  refine ⟨fun z => ?_, ?_⟩
  · suffices ∀ᶠ μ in atTop, re (l z) + b / μ ≤ φ z from
      have ht : Tendsto (fun μ => re (l z) + b / μ) atTop (𝓝 (re (l z))) := by
        simpa using (tendsto_id.const_div_atTop b).const_add (re (l z))
      le_of_tendsto_of_tendsto ht (tendsto_const_nhds) this
    filter_upwards [hph z z.2, Ioi_mem_atTop 0] with μ hμ he
    have : μ ≠ 0 := by grind
    calc
    _ = (re (l (μ • z)) + b) / μ := by simp [field, real_smul_eq_coe_mul]
    _ ≤ φ (μ • z) / μ := by
      gcongr
      · grind
      have := hlb ⟨μ • z.1, c.smul_mem' (by norm_cast) z.2⟩
      simp_all
    _ = φ z := by simp [field, hμ]
  · calc
    _ = (re ∘ l) 0 + b := by simp
    _ ≤ φ 0 := hlb ⟨0, hcp⟩
    _ = 0 := by
      obtain ⟨n, hn⟩ := ((hph 0 hcp).and (Ioi_mem_atTop 1)).exists
      have : (n - 1) * φ 0 = 0 := by simp at hn; grind
      grind

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

/-- Let `φ : E → ℝ` be a convex and lower-semicontinuous function on a closed convex subset `s`. For
any point `x ∈ s` and `a < φ x`, there exists a continuous affine linear function `f` in `E` such
that `f ≤ φ` on `s` and `f x = a`. This is an auxiliary lemma used in the proof of
`ConvexOn.sSup_affine_eq.` -/
lemma exists_affine_le_of_lt {x : E} {a : ℝ} (hx : x ∈ s) (hax : a < φ x) (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ (l : E →L[𝕜] 𝕜) (c : ℝ),
      s.restrict (re ∘ l) + const s c ≤ s.restrict φ ∧ re (l x) + c = a := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
  obtain ⟨L, ⟨b, hLb⟩⟩ := geometric_hahn_banach_point_closed (𝕜 := 𝕜) hφcv.convex_re_epigraph
    (hφc.isClosed_re_epigraph hsc) (by simp [A, hax] : (x, ofReal a) ∉ A)
  let u := L.comp (.inl 𝕜 E 𝕜)
  let c := (re (L (0, 1)))⁻¹
  refine ⟨- c • u, c * re (u x) + a, fun z => ?_, ?_⟩
  · have hv (v : 𝕜) : v * L (0, 1) = L (0, v) := by rw [← smul_eq_mul, ← map_smul]; simp
    have hine {w : E} (h : w ∈ s) : re (L (x, 0)) + re (L (0, 1)) * a
      < re (L (w, 0)) + re (L (0, 1)) * φ w := by
      have hw := hLb.1.trans (hLb.2 _ (by simp [A, h] : (w, ofReal (φ w)) ∈ A))
      rw [← coprod_comp_inl_inr L] at hw
      simpa [-coprod_comp_inl_inr, ← hv (ofReal a), ← hv (ofReal (φ w)), mul_comm a,
        mul_comm (φ w)] using hw
    have hc : 0 < c := inv_pos.2 (pos_of_right_mul_lt_le (lt_of_add_lt_add_left (hine hx)) hax.le)
    simpa [smul_re, u, c, mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (inv_pos.1 hc))]
      using mul_le_mul_of_nonneg_left (hine z.2).le hc.le
  · simp [u, c, smul_re]

/-- A function `φ : E → ℝ` that is convex and lower-semicontinuous on a closed convex subset `s` is
the supremum of a family of functions that are the restrictions to `s` of continuous affine linear
functions in `E`. -/
theorem sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    sSup {f | f ≤ s.restrict φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = s.restrict (re ∘ l) + const s c} =
      s.restrict φ := by
  let A := { p : E × 𝕜 | p.1 ∈ s ∧ φ p.1 ≤ re p.2 }
  ext x
  rw [sSup_apply]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun r ⟨f, hf⟩ => ?_) (fun r hr => ?_)
  · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 (show φ x - 1 < φ x from by grind)
      hsc hφc hφcv
    exact ⟨φ x - 1, hlc.2 ▸ ⟨⟨s.restrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩, rfl⟩⟩
  · exact hf ▸ f.2.1 x
  · obtain ⟨z, hz⟩ := exists_between hr
    obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) x.2 hz.2 hsc hφc hφcv
    exact ⟨z, hlc.2 ▸ ⟨⟨s.restrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩, rfl⟩, hz.1⟩

/-- A function `φ : E → ℝ` that is convex, lower-semicontinuous, and positively homogeneous
on a closed, convex, and pointed cone `c` is the supremum of a family of functions that are the
restrictions to `s` of continuous linear forms in `E`. -/
theorem convexCone_sSup_linear_eq (hsc : IsClosed c.carrier)
    (hcp : c.Pointed) (hφc : LowerSemicontinuousOn φ c)
    (hφcv : ConvexOn ℝ c φ) (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    sSup {f | f ≤ c.carrier.restrict φ ∧ ∃ l : E →L[𝕜] 𝕜, f = c.carrier.restrict (re ∘ l)} =
      c.carrier.restrict φ := by
  refine trans ?_ (hφcv.sSup_affine_eq (𝕜 := 𝕜) hsc hφc)
  ext x
  refine csSup_eq_csSup_of_forall_exists_le (fun r ⟨f, hf⟩ => ⟨f.1 x, ?_⟩) (fun r ⟨f, hf⟩ => ?_)
  · refine ⟨⟨⟨f.1, f.2.1, ?_⟩, by simp⟩, by subst hf; rfl⟩
    obtain ⟨l, hl⟩ := f.2.2
    exact ⟨l, 0, by simp [hl]⟩
  · obtain ⟨l, b, hlb⟩ := f.2.2
    have := linear_le_and_nonpos_of_affine_le hcp hph (hlb ▸ f.2.1)
    refine ⟨re (l x), ⟨⟨c.carrier.restrict (re ∘ l), this.1, ⟨l, rfl⟩⟩, rfl⟩, ?_⟩
    simpa [← hf, hlb] using this.2

/-- The countable version of `sSup_affine_eq`. -/
theorem sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ 𝓕' : Set (s → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = s.restrict φ ∧
      ∀ f ∈ 𝓕', f ≤ s.restrict φ ∧
      ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = s.restrict (re ∘ l) + const s c := by
  by_cases! hs : s.Nonempty
  · let 𝓕 := {f | f ≤ s.restrict φ ∧
      ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = s.restrict (re ∘ l) + const s c}
    have hl : IsLUB 𝓕 (s.restrict φ) := by
      refine (hφcv.sSup_affine_eq (𝕜 := 𝕜) hsc hφc) ▸ isLUB_csSup ?_ ?_
      · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) hs.some_mem
          (by grind : φ hs.some - 1 < φ (⟨hs.some, hs.some_mem⟩ : s)) hsc hφc hφcv
        exact ⟨s.restrict (re ∘ l) + const s c, hlc.1, l, c, rfl⟩
      · exact (bddAbove_def.2 ⟨φ ∘ Subtype.val, fun y hy => hy.1⟩)
    have hr (f) (hf : f ∈ 𝓕) : LowerSemicontinuous f := by
      obtain ⟨l, c, hlc⟩ := hf.2
      exact Continuous.lowerSemicontinuous (hlc ▸ by fun_prop)
    obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
    refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
    by_contra!
    grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x : s => φ x - 1) ⟨hs.some, hs.some_mem⟩]
  · use ∅; simp [restrict_def]; grind

/-- The countable version of `convexCone_sSup_linear_eq`. -/
theorem convexCone_sSup_of_countable_linear_eq [HereditarilyLindelofSpace E]
    (hsc : IsClosed c.carrier) (hcp : c.Pointed) (hφc : LowerSemicontinuousOn φ c)
    (hφcv : ConvexOn ℝ c φ) (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ 𝓕' : Set (c → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = c.carrier.restrict φ ∧
      ∀ f ∈ 𝓕', f ≤ c.carrier.restrict φ ∧ ∃ l : E →L[𝕜] 𝕜, f = c.carrier.restrict (re ∘ l) := by
  by_cases! hc : c.carrier.Nonempty
  · let 𝓕 := {f | f ≤ c.carrier.restrict φ ∧ ∃ l : E →L[𝕜] 𝕜, f = c.carrier.restrict (re ∘ l)}
    have hl : IsLUB 𝓕 (c.carrier.restrict φ) := by
      refine (hφcv.convexCone_sSup_linear_eq (𝕜 := 𝕜) hsc hcp hφc hph) ▸ isLUB_csSup ?_ ?_
      · obtain ⟨l, b, hlb⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) hc.some_mem
          (by grind : φ hc.some - 1 < φ (⟨hc.some, hc.some_mem⟩ : c.carrier)) hsc hφc hφcv
        refine ⟨c.carrier.restrict (re ∘ l), ?_, l, rfl⟩
        exact (linear_le_and_nonpos_of_affine_le hcp hph hlb.1).1
      · exact (bddAbove_def.2 ⟨φ ∘ Subtype.val, fun y hy => hy.1⟩)
    have hr (f) (hf : f ∈ 𝓕) : LowerSemicontinuous f := by
      obtain ⟨l, hll⟩ := hf.2
      exact Continuous.lowerSemicontinuous (hll ▸ by fun_prop)
    obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
    refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
    by_contra!
    grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x : c => φ x - 1) ⟨hc.some, hc.some_mem⟩]
  · use ∅
    have := isEmpty_coe_sort.2 hc
    simp [restrict_def]
    grind

/-- The sequential version of `sSup_of_countable_affine_eq`. -/
theorem sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ (l : ℕ → E →L[𝕜] 𝕜) (c : ℕ → ℝ),
      (∀ i, s.restrict (re ∘ (l i)) + const s (c i) ≤ s.restrict φ) ∧
      ⨆ i, s.restrict (re ∘ (l i)) + const s (c i) = s.restrict φ := by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.sSup_of_countable_affine_eq (𝕜 := 𝕜) hsc hφc
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : ℕ) : ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f i = s.restrict (re ∘ l) + const s c := by simp_all
    choose l c hlc using this
    refine ⟨l, c, fun i => (hlc i) ▸ (h𝓕'.2.2 (f i) (hf ▸ mem_range_self i)).1, ?_⟩
    calc
    _ = ⨆ i, f i := by congr with i x; exact congrFun (hlc i).symm x
    _ = _ := by rw [← sSup_range, ← hf, h𝓕'.2.1]
  · by_cases! hsφ : s.restrict φ = 0
    · have := congrFun hsφ
      refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩
      · simp_all [restrict_def]
      · ext; simp_all
    · obtain ⟨x, hx⟩ := Function.ne_iff.1 hsφ
      have : s = ∅ := by have := congrFun h𝓕'.2.1 x; simp_all
      grind

/-- The sequential version of `convexCone_sSup_of_countable_linear_eq`. -/
theorem convexCone_sSup_of_nat_linear_eq [HereditarilyLindelofSpace E] (hsc : IsClosed c.carrier)
    (hcp : c.Pointed) (hφc : LowerSemicontinuousOn φ c) (hφcv : ConvexOn ℝ c φ)
    (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ l : ℕ → E →L[𝕜] 𝕜,  (∀ i, c.carrier.restrict (re ∘ (l i)) ≤ c.carrier.restrict φ) ∧
      ⨆ i, c.carrier.restrict (re ∘ (l i)) = c.carrier.restrict φ := by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.convexCone_sSup_of_countable_linear_eq (𝕜 := 𝕜) hsc hcp hφc hph
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : ℕ) : ∃ (l : E →L[𝕜] 𝕜), f i = c.carrier.restrict (re ∘ l) := by simp_all
    choose l hl using this
    refine ⟨l, fun i => (hl i) ▸ (h𝓕'.2.2 (f i) (hf ▸ mem_range_self i)).1, ?_⟩
    calc
    _ = ⨆ i, f i := by congr with i x; exact congrFun (hl i).symm x
    _ = _ := by rw [← sSup_range, ← hf, h𝓕'.2.1]
  · by_cases! hsφ : c.carrier.restrict φ = 0
    · refine ⟨fun _ => 0, fun i => ?_, ?_⟩
      · simp [hsφ, restrict_def]; rfl
      · ext x
        have := congrFun hsφ x
        simp_all
    · obtain ⟨x, hx⟩ := Function.ne_iff.1 hsφ
      have : c.carrier = ∅ := by have := congrFun h𝓕'.2.1 x; simp_all
      grind

/-- A function `φ : E → ℝ` that is convex and lower-semicontinuous is the supremum of a family of
of continuous affine linear functions. -/
theorem univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
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
    · ext x; simpa using congrFun hlc x
    · ext; simp
    · simpa using hb ▸ h ⟨x, trivial⟩
    · subst hlc; simpa using hb.symm
  _ = sSup 𝓕 ∘ (Equiv.Set.univ E).symm := by ext x; rw [sSup_image', sSup_eq_iSup']; simp
  _ = φ ∘ Subtype.val ∘ (Equiv.Set.univ E).symm :=
    congrArg (fun g => g ∘ (Equiv.Set.univ E).symm) this
  _ = φ := by ext; simp

/-- A function `φ : E → ℝ` that is convex, lower-semicontinuous, and positively homogeneous is the
supremum of a family of continuous linear forms in `E`. -/
theorem univ_sSup_linear_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ)
    (hph : ∀ x, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    sSup {f | f ≤ φ ∧ ∃ l : E →L[𝕜] 𝕜, f = re ∘ l} = φ := by
  refine trans ?_ (hφcv.univ_sSup_affine_eq (𝕜 := 𝕜) hφc)
  ext x
  refine csSup_eq_csSup_of_forall_exists_le (fun r ⟨f, hf⟩ => ⟨f.1 x, ?_⟩) (fun r ⟨f, hf⟩ => ?_)
  · refine ⟨⟨⟨f.1, f.2.1, ?_⟩, by simp⟩, by subst hf; rfl⟩
    obtain ⟨l, hl⟩ := f.2.2
    exact ⟨l, by simp [hl]⟩
  · obtain ⟨l, b, hlb⟩ := f.2.2
    have hp : ∀ x ∈ (⊤ : ConvexCone ℝ E), ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x := by simp [hph]
    have hq : ((⊤ : ConvexCone ℝ E) : Set E).restrict (⇑re ∘ ⇑l) + const (⊤ : ConvexCone ℝ E) b ≤
      ((⊤ : ConvexCone ℝ E) : Set E).restrict φ := by
      intro x
      have := congrFun hlb x ▸ f.2.1 x
      simp_all
    have := linear_le_and_nonpos_of_affine_le ConvexCone.mem_top hp hq
    refine ⟨re (l x), ⟨⟨re ∘ l, fun x => this.1 ⟨x, mem_univ x⟩, ⟨l, rfl⟩⟩, rfl⟩, ?_⟩
    simpa [← hf, hlb] using this.2

/-- The countable version of `univ_sSup_affine_eq`. -/
theorem univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ 𝓕' : Set (E → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧
      ∀ f ∈ 𝓕', f ≤ φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) + const E c := by
  let 𝓕 := {f | f ≤ φ ∧ ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f = (re ∘ l) + const E c}
  have hl : IsLUB 𝓕 φ := by
    refine (hφcv.univ_sSup_affine_eq (𝕜 := 𝕜) hφc) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨l, c, hlc⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) (@mem_univ E 0)
        (by grind : φ 0 - 1 < φ (⟨0, @mem_univ E 0⟩ : univ)) isClosed_univ
        (lowerSemicontinuousOn_univ_iff.2 hφc) hφcv
      exact ⟨(re ∘ l) + const E c, fun x => hlc.1 ⟨x, mem_univ x⟩, ⟨l, c, rfl⟩⟩
    · exact (bddAbove_def.2 ⟨φ, fun y hy => hy.1⟩)
  have hr (f) (hf : f ∈ 𝓕) : LowerSemicontinuous f := by
    obtain ⟨l, c, hlc⟩ := hf.2
    exact Continuous.lowerSemicontinuous (hlc ▸ by fun_prop)
  obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
  refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
  by_contra!
  grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x => φ x - 1) 0]

/-- The countable version of `univ_sSup_linear_eq`. -/
theorem univ_sSup_of_countable_linear_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ)
    (hph : ∀ x, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ 𝓕' : Set (E → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧ ∀ f ∈ 𝓕', f ≤ φ ∧
      ∃ l : E →L[𝕜] 𝕜, f = re ∘ l := by
  let 𝓕 := {f | f ≤ φ ∧ ∃ l : E →L[𝕜] 𝕜, f = re ∘ l}
  have hl : IsLUB 𝓕 φ := by
    refine (hφcv.univ_sSup_linear_eq (𝕜 := 𝕜) hφc hph) ▸ isLUB_csSup ?_ ?_
    · obtain ⟨l, b, hlb⟩ := exists_affine_le_of_lt (𝕜 := 𝕜) (@mem_univ E 0)
        (by grind : φ 0 - 1 < φ (⟨0, @mem_univ E 0⟩ : univ)) isClosed_univ
        (lowerSemicontinuousOn_univ_iff.2 hφc) hφcv
      refine ⟨re ∘ l, fun x => ?_, l, rfl⟩
      have hp : ∀ x ∈ (⊤ : ConvexCone ℝ E), ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x := by simp [hph]
      have hq : ((⊤ : ConvexCone ℝ E) : Set E).restrict (⇑re ∘ ⇑l) + const (⊤ : ConvexCone ℝ E) b ≤
        ((⊤ : ConvexCone ℝ E) : Set E).restrict φ := by
        intro x
        grind [hlb.1 ⟨x, mem_univ x⟩]
      grind [(linear_le_and_nonpos_of_affine_le ConvexCone.mem_top hp hq).1 ⟨x, mem_univ x⟩]
    · exact (bddAbove_def.2 ⟨φ, fun y hy => hy.1⟩)
  have hr (f) (hf : f ∈ 𝓕) : LowerSemicontinuous f := by
    obtain ⟨l, hll⟩ := hf.2
    exact Continuous.lowerSemicontinuous (hll ▸ by fun_prop)
  obtain ⟨𝓕', h𝓕'⟩ := exists_countable_lowerSemicontinuous_isLUB hr hl
  refine ⟨𝓕', h𝓕'.2.1, h𝓕'.2.2.csSup_eq ?_, fun f hf => h𝓕'.1 hf⟩
  by_contra!
  grind [(isLUB_empty_iff.1 (this ▸ h𝓕'.2.2)) (fun x => φ x - 1) 0]

/-- The sequential version of `univ_sSup_of_countable_affine_eq`. -/
theorem univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ (l : ℕ → E →L[𝕜] 𝕜) (c : ℕ → ℝ), (∀ i, re ∘ (l i) + const E (c i) ≤ φ)
      ∧ ⨆ i, re ∘ (l i) + const E (c i) = φ := by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.univ_sSup_of_countable_affine_eq (𝕜 := 𝕜) hφc
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : ℕ) : ∃ (l : E →L[𝕜] 𝕜) (c : ℝ), f i = re ∘ l + const E c := by simp_all
    choose l c hlc using this
    refine ⟨l, c, fun i => (hlc i) ▸ (h𝓕'.2.2 (f i) (hf ▸ mem_range_self i)).1, ?_⟩
    calc
    _ = ⨆ i, f i := by congr with i x; exact congrFun (hlc i).symm x
    _ = _ := by rw [← sSup_range, ← hf, h𝓕'.2.1]
  · refine ⟨fun _ => 0, fun _ => 0, fun i x => ?_, ?_⟩
    · simp_all [← congrFun h𝓕'.2.1 x]
    · ext x
      simp_all [← congrFun h𝓕'.2.1 x]

/-- The sequential version of `univ_sSup_of_nat_linear_eq`. -/
theorem univ_sSup_of_nat_linear_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ)
    (hph : ∀ x, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ l : ℕ → E →L[𝕜] 𝕜, (∀ i, re ∘ (l i) ≤ φ) ∧ ⨆ i, re ∘ (l i) = φ := by
  obtain ⟨𝓕', h𝓕'⟩ := hφcv.univ_sSup_of_countable_linear_eq (𝕜 := 𝕜) hφc hph
  by_cases! he : 𝓕'.Nonempty
  · obtain ⟨f, hf⟩ := h𝓕'.1.exists_eq_range he
    have (i : ℕ) : ∃ l : E →L[𝕜] 𝕜, f i = re ∘ l:= by simp_all
    choose l hl using this
    refine ⟨l, fun i => (hl i) ▸ (h𝓕'.2.2 (f i) (hf ▸ mem_range_self i)).1, ?_⟩
    calc
    _ = ⨆ i, f i := by congr with i x; exact congrFun (hl i).symm x
    _ = _ := by rw [← sSup_range, ← hf, h𝓕'.2.1]
  · refine ⟨fun _ => 0, fun i x => ?_, ?_⟩
    · simp_all [← congrFun h𝓕'.2.1 x]
    · ext x
      simp_all [← congrFun h𝓕'.2.1 x]

end RCLike

section Real

variable [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] {c : ConvexCone ℝ E}

/-- The real version of `sSup_affine_eq`. -/
theorem real_sSup_affine_eq (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    sSup {f | f ≤ s.restrict φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = s.restrict l + const s c} =
      s.restrict φ :=
  sSup_affine_eq (𝕜 := ℝ) hsc hφc hφcv

/-- The real version of `convexCone_sSup_linear_eq`. -/
theorem real_convexCone_sSup_linear_eq (hsc : IsClosed c.carrier)
    (hcp : c.Pointed) (hφc : LowerSemicontinuousOn φ c)
    (hφcv : ConvexOn ℝ c φ) (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    sSup {f | f ≤ c.carrier.restrict φ ∧ ∃ l : E →L[ℝ] ℝ, f = c.carrier.restrict l} =
      c.carrier.restrict φ :=
  convexCone_sSup_linear_eq hsc hcp hφc hφcv hph

/-- The real version of `sSup_of_countable_affine_eq`. -/
theorem real_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ 𝓕' : Set (s → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = s.restrict φ ∧
      ∀ f ∈ 𝓕', f ≤ s.restrict φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = s.restrict l + const s c :=
  sSup_of_countable_affine_eq (𝕜 := ℝ) hsc hφc hφcv

/-- The real version of `convexCone_sSup_of_countable_linear_eq`. -/
theorem real_convexCone_sSup_of_countable_linear_eq [HereditarilyLindelofSpace E]
    (hsc : IsClosed c.carrier) (hpc : c.Pointed) (hφc : LowerSemicontinuousOn φ c)
    (hφcv : ConvexOn ℝ c φ) (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ 𝓕' : Set (c → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = c.carrier.restrict φ ∧
      ∀ f ∈ 𝓕', f ≤ c.carrier.restrict φ ∧ ∃ l : E →L[ℝ] ℝ, f = c.carrier.restrict l :=
  convexCone_sSup_of_countable_linear_eq hsc hpc hφc hφcv hph

/-- The real version of `sSup_of_nat_affine_eq`. -/
theorem real_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E] (hsc : IsClosed s)
    (hφc : LowerSemicontinuousOn φ s) (hφcv : ConvexOn ℝ s φ) :
    ∃ (l : ℕ → E →L[ℝ] ℝ) (c : ℕ → ℝ),
      (∀ i, s.restrict (l i) + const s (c i) ≤ s.restrict φ) ∧
      ⨆ i, s.restrict (l i) + const s (c i) = s.restrict φ :=
  sSup_of_nat_affine_eq (𝕜 := ℝ) hsc hφc hφcv

/-- The real version of `convexCone_sSup_of_nat_linear_eq`. -/
theorem real_convexCone_sSup_of_nat_linear_eq [HereditarilyLindelofSpace E]
    (hsc : IsClosed c.carrier) (hpc : c.Pointed) (hφc : LowerSemicontinuousOn φ c)
    (hφcv : ConvexOn ℝ c φ) (hph : ∀ x ∈ c, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ l : ℕ → E →L[ℝ] ℝ, (∀ i, c.carrier.restrict (l i) ≤ c.carrier.restrict φ) ∧
      ⨆ i, c.carrier.restrict (l i) = c.carrier.restrict φ :=
  convexCone_sSup_of_nat_linear_eq hsc hpc hφc hφcv hph

/-- The real version of `univ_sSup_affine_eq`. -/
theorem real_univ_sSup_affine_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    sSup {f | f ≤ φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = l + const E c} = φ :=
  univ_sSup_affine_eq (𝕜 := ℝ) hφc hφcv

/-- The real version of `univ_sSup_linear_eq`. -/
theorem real_univ_sSup_linear_eq (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ)
    (hph : ∀ x, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    sSup {f | f ≤ φ ∧ ∃ l : E →L[ℝ] ℝ, f = l} = φ :=
  univ_sSup_linear_eq hφc hφcv hph

/-- The real version of `univ_sSup_of_countable_affine_eq`. -/
theorem real_univ_sSup_of_countable_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ 𝓕' : Set (E → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧
      ∀ f ∈ 𝓕', f ≤ φ ∧ ∃ (l : E →L[ℝ] ℝ) (c : ℝ), f = l + const E c :=
  univ_sSup_of_countable_affine_eq (𝕜 := ℝ) hφc hφcv

/-- The real version of `univ_sSup_of_countable_linear_eq`. -/
theorem real_univ_sSup_of_countable_linear_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ)
    (hph : ∀ x, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ 𝓕' : Set (E → ℝ), 𝓕'.Countable ∧ sSup 𝓕' = φ ∧ ∀ f ∈ 𝓕', f ≤ φ ∧ ∃ l : E →L[ℝ] ℝ, f = l :=
  univ_sSup_of_countable_linear_eq hφc hφcv hph

/-- The real version of `univ_sSup_of_nat_affine_eq`. -/
theorem real_univ_sSup_of_nat_affine_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ) :
    ∃ (l : ℕ → E →L[ℝ] ℝ) (c : ℕ → ℝ), (∀ i, (l i) + const E (c i) ≤ φ) ∧
      ⨆ i, (l i) + const E (c i) = φ :=
  univ_sSup_of_nat_affine_eq (𝕜 := ℝ) hφc hφcv

/-- The real version of `univ_sSup_of_nat_linear_eq`. -/
theorem real_univ_sSup_of_nat_linear_eq [HereditarilyLindelofSpace E]
    (hφc : LowerSemicontinuous φ) (hφcv : ConvexOn ℝ univ φ)
    (hph : ∀ x, ∀ᶠ μ in atTop, φ (μ • x) = μ * φ x) :
    ∃ l : ℕ → E →L[ℝ] ℝ, (∀ i, l i ≤ φ) ∧ ⨆ i, (l i).toFun = φ :=
  univ_sSup_of_nat_linear_eq hφc hφcv hph

end Real

end ConvexOn
