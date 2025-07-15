import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Compactness.PseudometrizableLindelof

open MeasureTheory
open ProbabilityTheory
open TopologicalSpace
open Set
open Metric
open ContinuousLinearMap
open scoped ENNReal

namespace RCLike

-- Lemma 1.2.9 convex set as intersection of countably many half spaces
theorem separable_Inter_halfSpaces_eq {𝕜 E : Type*} {s : Set E}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeparableSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : s.Nonempty) :
  ∃ (L : ℕ → E →L[𝕜] 𝕜) (c : ℕ → ℝ),
  ⋂ (i : ℕ), {x | re ((L i) x) - c i ≥ 0} = s
  ∧ (sᶜ.Nonempty → ∀ i, ∃ x, (re ∘ L i) x ≠ 0) := by
  cases (eq_empty_or_nonempty sᶜ) with
  | inl hsc =>
    exists (fun i ↦ 0)
    exists (fun i ↦ 0)
    simp only [zero_apply, map_zero, sub_self, le_refl, setOf_true, iInter_univ]
    constructor
    · exact (compl_empty_iff.mp hsc).symm
    · rw [nonempty_iff_ne_empty]
      intro ha ; have := ha hsc
      exact False.elim this
  | inr hsc =>
    have nonemptys := Nonempty.to_subtype hsc
    have issepsc : IsSeparable sᶜ := IsSeparable.of_separableSpace sᶜ
    have sepsc : SeparableSpace ↑sᶜ := IsSeparable.separableSpace issepsc
    let f := denseSeq ↑sᶜ
    have φc : ∀ (i : ℕ), ∃ (φ : E →L[𝕜] 𝕜) (c : ℝ),
      (∀ a ∈ ball ↑(f i) (infDist ↑(f i) s), re (φ a) < c) ∧ ∀ b ∈ s, c ≤ re (φ b) := by
        intro i
        have di : Disjoint (ball ↑(f i) (infDist ↑(f i) s)) s := disjoint_ball_infDist
        apply geometric_hahn_banach_open (convex_ball ↑(f i)  (infDist ↑(f i) s)) isOpen_ball hs₁ di
    choose L c hLc using φc
    exists L
    exists c
    constructor
    · ext x
      simp only [ge_iff_le, sub_nonneg, mem_iInter, mem_setOf_eq]
      constructor
      · apply Function.mtr
        simp only [not_forall, not_le]
        intro hx
        have pos : 0 < (infDist x s) / 2 := by
          apply div_pos
          exact (IsClosed.notMem_iff_infDist_pos hs₂ hs₃).mp hx
          exact Nat.ofNat_pos
        have hfi : ∃ (i : ℕ), dist ↑(f i) x < ((infDist x s) / 2) := by
          simp only [← mem_compl_iff] at hx
          have : ((ball ⟨x, hx⟩ ((infDist x s) / 2)) ∩ (range f)).Nonempty := by
            apply Dense.inter_open_nonempty (denseRange_denseSeq ↑sᶜ)
            exact isOpen_ball; exact nonempty_ball.mpr pos
          simp only [nonempty_def] at this
          rcases this with ⟨b, hb⟩
          simp only [mem_inter_iff, mem_ball, mem_range] at hb
          rcases hb.2 with ⟨i, hi⟩; use i
          rw (config := {occs := .pos [1]}) [← hi] at hb ; exact hb.1
        rcases hfi with ⟨i, hi⟩
        rw [dist_comm] at hi
        have hfix : infDist ↑(f i) s ≥  ((infDist x s) / 2) := by
          apply le_of_not_gt
          intro hp
          rcases ((infDist_lt_iff hs₃).mp hp) with ⟨y, hy1, hy2⟩
          have hxy : dist x y < infDist x s :=
            calc
              dist x y ≤ dist x ↑(f i) + dist ↑(f i) y := dist_triangle x ↑(f i) y
              _ < (infDist x s) / 2 + (infDist x s) / 2 := add_lt_add hi hy2
              _ = infDist x s := by simp only [add_halves]
          exact notMem_of_dist_lt_infDist hxy hy1
        have hxfi : x ∈ (ball ↑(f i) (infDist ↑(f i) s)) := by
          rw [mem_ball]
          calc
            dist x ↑(f i) < (infDist x s) / 2 := hi
            _ ≤ infDist ↑(f i) s := hfix
        exists i; apply (hLc i).1; exact hxfi
      · intro hx i
        exact ((hLc i).2 x hx)
    · intro ha j
      cases (le_or_gt (c j) 0) with
      | inl hl =>
        use f j; apply ne_of_lt; apply lt_of_lt_of_le
        · have : (⇑re ∘ ⇑(L j)) ↑(f j) < c j := by
            apply (hLc j).1; apply mem_ball_self
            have : ↑(f j) ∈ sᶜ := (f j).property
            exact (IsClosed.notMem_iff_infDist_pos hs₂ hs₃).mp this
          exact this
        · exact hl
      | inr hr =>
        simp only [nonempty_def] at hs₃
        rcases hs₃ with ⟨x, hxs⟩; use x
        apply ne_of_gt; apply lt_of_lt_of_le
        · exact hr
        · have : c j ≤ (⇑re ∘ ⇑(L j)) x := by
            apply (hLc j).2; exact hxs
          exact this

-- Lemma 1.2.9 for Product Spaces
theorem separable_prod_Inter_halfSpaces_eq {𝕜 E F : Type*} {s : Set (E × F)}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeparableSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SeparableSpace F] [Module 𝕜 F] [ContinuousSMul 𝕜 F]
  (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : s.Nonempty) :
  ∃ (L : ℕ → E →L[𝕜] 𝕜) (T : ℕ → F →L[𝕜] 𝕜) (c : ℕ → ℝ),
  ⋂ (i : ℕ), {(x, y) | re ((L i) x) + re ((T i) y) - c i ≥ 0} = s
  ∧ (sᶜ.Nonempty → ∀ i, ∃ (x : E), ∃ (y : F), (re ∘ L i) x + (re ∘ T i) y ≠ 0):= by
  have lem1 : ∃ (LT : ℕ → (E × F) →L[𝕜] 𝕜) (c : ℕ → ℝ), ⋂ (i : ℕ), {x | re ((LT i) x) - c i ≥ 0} = s
    ∧ (sᶜ.Nonempty → ∀ i, ∃ x, (re ∘ LT i) x ≠ 0) :=
    separable_Inter_halfSpaces_eq hs₁ hs₂ hs₃
  rcases lem1 with ⟨LT, c, eq1, eq2⟩
  exists fun i ↦ ((LT i).comp (inl 𝕜 E F))
  exists fun i ↦ ((LT i).comp (inr 𝕜 E F))
  exists c
  have lem2 : ∀ (x : E), ∀ (y : F), (x, y) = (x, 0) + (0, y) := by
    intro x y; simp only [Prod.mk_add_mk, add_zero, zero_add]
  have lem3 : ∀ i, ∀ (x : E), ∀ (y : F), re ((LT i) (x, 0)) + re ((LT i) (0, y))
     = re ((LT i) (x, y)) := by
    intro i x y; simp only [lem2 x y, (LT i).map_add, re.map_add]
  constructor
  · rw [← eq1]; apply iInter_congr; intro i; ext ⟨x, y⟩
    simp only [coe_comp', Function.comp_apply, inl_apply, inr_apply, ge_iff_le, sub_nonneg,
      mem_setOf_eq]
    rw [lem3]
  · intro hsc i; rcases (eq2 hsc i) with ⟨z, hz⟩
    use z.1; use z.2; simp only [coe_comp', Function.comp_apply, inl_apply, inr_apply, lem3]
    exact hz

-- Lemma 1.2.10
theorem convexfun_eq_sup_affine {𝕜 E : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeparableSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {φ : E → ℝ} (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ) :
  ∃ (L : ℕ → E →L[𝕜] 𝕜) (c : ℕ → ℝ),
  ∀ x, BddAbove (Set.range (fun i ↦ (re ((L i) x) + c i)))
  ∧ (⨆ (i : ℕ), re ((L i) x) + c i = φ x) := by
  let C := {(x, (s : 𝕜)) | φ x ≤ re s}
  have hC₁ : Convex ℝ C := by
    let D := {(x, (s : ℝ)) | φ x ≤ s}
    have hC : C = (LinearMap.prodMap (LinearMap.id : E →ₗ[ℝ] E) reLm)⁻¹' D := by
      simp_all only [preimage_setOf_eq, LinearMap.prodMap_apply, LinearMap.id_coe,
        id_eq, reLm_coe, C, D]
    rw [hC]
    apply Convex.linear_preimage
    have p := ConvexOn.convex_epigraph hφ_cvx
    simp_all only [mem_univ, true_and, D]
  have hC₂ : IsClosed C := by
    let A := {(x, (s : EReal)) | φ x ≤ s}
    have hC : C = (Prod.map (id: E → E) ((Real.toEReal ∘ re) : 𝕜 → EReal))⁻¹' A := by
      simp_all only [preimage_setOf_eq, Prod.map_fst, id_eq, Prod.map_snd, Function.comp_apply,
      EReal.coe_le_coe_iff, C, A]
    rw [hC]
    have M : Monotone Real.toEReal := by
      intro a b hab
      rw [EReal.coe_le_coe_iff]
      exact hab
    have hφ : LowerSemicontinuous (Real.toEReal ∘ φ) := Continuous.comp_lowerSemicontinuous
      continuous_coe_real_ereal hφ_cont M
    have a : IsClosed A := LowerSemicontinuous.isClosed_epigraph hφ
    have p : Continuous (Real.toEReal ∘ re) := Continuous.comp continuous_coe_real_ereal
      (reCLM : 𝕜 →L[ℝ] ℝ).cont
    exact IsClosed.preimage (Continuous.prodMap continuous_id p) a
  have hC₃ : C.Nonempty := by
    have lem : (0, ↑ (φ 0)) ∈ C := by
      simp only [mem_setOf_eq, ofReal_re, le_refl, C]
    exact nonempty_of_mem lem
  rcases (separable_prod_Inter_halfSpaces_eq (𝕜 := 𝕜) hC₁ hC₂ hC₃) with ⟨L, T, c, hLTc1, hLTc2⟩
  have lem1 : ∀ i, ∀ y, (T i) y = ((T i) 1) * y := by
    intro i y
    have lem11 : (T i) y = (T i) (y • 1) := by simp only [smul_eq_mul, mul_one]
    rw [lem11, mul_comm, map_smul, smul_eq_mul]
  have lem2 :  ∀ (x : E) (y : 𝕜), re y ≥ φ x →
  ∀ i, c i ≤ re ((L i) x) + re ((T i) 1) * (re y) - im ((T i) 1) * im (y) := by
    intro x y
    intro hy i
    have hy2 : (x, y) ∈ C := by simp only [mem_setOf_eq, C]; exact hy
    rw [add_sub_assoc, ← mul_re, ← lem1 i]
    simp only [← hLTc1, ge_iff_le, sub_nonneg, mem_iInter, mem_setOf_eq, C] at hy2
    exact (hy2 i)
  have lem3 : ∀ i, 0 = im ((T i) 1) := by
    cases (@I_eq_zero_or_im_I_eq_one 𝕜 (by infer_instance)) with
    | inl hI0 =>
      intro i ; rw [← I_im', hI0] ; simp only [map_zero, zero_mul]
    | inr hI1 =>
      intro i
      by_contra ht
      let z : 𝕜 := ↑(φ 0) + I * ↑((c i - re ((T i) 1) * (φ 0) - 1) / -im ((T i) 1))
      have rez : re z = φ 0 := by
        simp only [z, map_add, ofReal_re, mul_re, I_re, zero_mul,
          ofReal_im, mul_zero, sub_self, add_zero]
      have imz : im z = (c i - re ((T i) 1) * (φ 0) - 1) / -im ((T i) 1) := by
        simp only [z, hI1, map_add, ofReal_im, mul_im, I_re, mul_zero,
          ofReal_re, one_mul, zero_add]
      have lem31 : c i ≤ c i - 1 :=
        calc
          c i ≤ re ((L i) 0) + re ((T i) 1) * (re z) - im ((T i) 1) * im (z) :=
                by apply (lem2 0 z); simp only [z, rez, le_rfl]
            _ = re ((T i) 1) * (φ 0) -
              im ((T i) 1) * ((c i - re ((T i) 1) * (φ 0) - 1) / -im ((T i) 1)) :=
                by simp only [map_zero, zero_add, rez, imz]
            _ = re ((T i) 1) * (φ 0) +
              im ((T i) 1) * ((c i - re ((T i) 1) * (φ 0) - 1) / im ((T i) 1)) :=
                by linarith
            _ = re ((T i) 1) * (φ 0) +
              im ((T i) 1) / im ((T i) 1) * (c i - re ((T i) 1) * (φ 0) - 1) :=
                by rw [mul_comm_div]
            _ = re ((T i) 1) * (φ 0) + 1 * (c i - re ((T i) 1) * (φ 0) - 1) :=
                by rw [div_self] ; rw [ne_comm, ne_eq]; exact ht
            _ = c i - 1 := by linarith
      have lem32 : c i > c i - 1 := by simp only [sub_lt_self_iff, zero_lt_one]
      exact not_lt_of_ge lem31 lem32
  have lem4 : ∀ i, 0 < re ((T i) 1) := by
    intro i; apply lt_of_not_ge; intro h
    rw [le_iff_eq_or_lt] at h
    cases h with
    | inl h1 =>
      have lem411 : ∀ x, c i ≤ re ((L i) x) := by
        intro x
        have : re (@ofReal 𝕜 (by infer_instance) (φ x)) ≥ φ x := by simp only [ofReal_re, le_rfl]
        have := (lem2 x ↑(φ x)) this i
        simp only [h1, ← lem3 i, zero_mul, add_zero, sub_zero] at this; exact this
      have lem412: ∀ (y : 𝕜), re ((T i) y) = 0 := by
            intro y; rw [lem1 i, mul_re, h1, ← lem3 i, zero_mul, zero_mul, sub_zero]
      have CcNonempty : Cᶜ.Nonempty := by
          rw [nonempty_def]; use (0, @ofReal 𝕜 (by infer_instance) (φ 0 - 1))
          simp only [mem_compl_iff, C, mem_setOf_eq, ofReal_re]; linarith
      have P1 := hLTc2 CcNonempty i; simp only [← not_forall] at P1
      have P2 : ∀ (x : E) (y : 𝕜), (re ∘ L i) x + (re ∘ T i) y = 0 := by
        have P21: ∀ (x : E), re ((L i) x) = 0 := by
          have ge1 : {n | 1 ≤ n} ∈ Filter.atTop := by
            simp only [Filter.mem_atTop_sets]
            use 1; intro b hb; exact hb
          intro x; apply le_antisymm
          · have : ∀ᶠ (n : ℕ) in Filter.atTop, re ((L i) x) ≤ - c i / n := by
              filter_upwards [ge1] with n hn
              have := lem411 ((-(n : 𝕜) • x))
              calc
                re ((L i) x) = re ((L i) (((-((n : ℝ) : 𝕜))⁻¹ * -((n : ℝ) : 𝕜)) • x)) := by
                  rw (config := {occs := .pos [1]}) [← (one_smul 𝕜 x)]
                  rw [inv_mul_cancel₀]
                  simp only [ne_eq, neg_eq_zero, ofReal_natCast, Nat.cast_eq_zero]
                  have : n > 0 := by linarith
                  exact (ne_of_gt this)
                _ = (-(n : ℝ))⁻¹ * re ((L i) ((-(n : 𝕜)) • x)) := by
                  rw [← smul_smul, map_smul, smul_eq_mul]
                  rw (config := {occs := .pos [1]}) [← ofReal_neg, ← ofReal_inv]
                  rw [re_ofReal_mul, ofReal_natCast]
                _ ≤ c i / -n := by
                  rw [inv_mul_eq_div, div_le_div_right_of_neg]; exact this
                  simp only [Left.neg_neg_iff, Nat.cast_pos]; linarith
                _ = - c i / n := by rw [div_neg, neg_div]
            apply ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (- c i)) this
          · have : ∀ᶠ (n : ℕ) in Filter.atTop, c i / n ≤ re ((L i) x) := by
              filter_upwards [ge1] with n hn; have := lem411 ((n : 𝕜) • x)
              calc
                c i / n ≤ re ((L i) ((n : 𝕜) • x)) / n := by
                  rw [div_le_div_iff_of_pos_right]; exact this
                  simp only [Nat.cast_pos]; linarith
                _ = re ((n : ℝ) * ((L i) x)) / n := by
                  rw [map_smul, smul_eq_mul, ← ofReal_natCast]
                _ = n * re ((L i) x) / n := by
                  rw [re_ofReal_mul]
                _ = re ((L i) x) := by
                  rw [mul_div_right_comm, div_self, one_mul]
                  apply ne_of_gt; simp only [Nat.cast_pos]; linarith
            apply le_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (c i)) this
        simp only [Function.comp_apply, P21, lem412, add_zero, implies_true]
      apply P1 P2
    | inr h2 =>
      let m := max ((c i) / re ((T i) 1) + 1) (φ 0)
      have lem421 : re (@ofReal 𝕜 (by infer_instance) m) ≥ φ 0 :=
        by simp only [ofReal_re, ge_iff_le, m, le_max_right]
      have lem422 : c i ≤ re ((T i) 1) * m := by
        have : c i ≤ re ((L i) 0) + re ((T i) 1) * re (@ofReal 𝕜 (by infer_instance) m)
        - im ((T i) 1) * im (@ofReal 𝕜 (by infer_instance) m) := (lem2 0 ↑m) lem421 i
        simp only [map_zero, ofReal_re, zero_add, ofReal_im, mul_zero, sub_zero] at this
        exact this
      have lem423 : c i < c i := by
        apply lt_of_le_of_lt lem422
        rw [← div_lt_iff_of_neg' h2]
        have : (c i) / re ((T i) 1) < ((c i) / re ((T i) 1) + 1) := by linarith
        apply lt_of_lt_of_le this
        simp only [m, le_max_left]
      exact lt_irrefl (c i) lem423
  have lem5 : ∀ i, (T i) 1 = ↑ (re ((T i) 1)) := by
    intro i
    apply Eq.trans (re_add_im ((T i) 1)).symm
    rw [← lem3 i]
    simp only [map_zero, zero_mul, add_zero]
  exists (fun i ↦ -((T i) 1)⁻¹ • (L i))
  exists (fun i ↦ c i / re ((T i) 1))
  let f := fun (y : E) ↦ (fun i ↦ re (( -((T i) 1)⁻¹ • L i) y) + c i / re ((T i) 1))
  have hf : ∀ y, BddAbove (Set.range (f y)) := by
    intro y
    have : ∀ i, f y i ≤ φ y := by
      have : re (@ofReal 𝕜 (by infer_instance) (φ y)) ≥ φ y := by simp only [ofReal_re, le_rfl]
      have := (lem2 y (φ y)) this
      simp only [ofReal_re, ofReal_im, mul_zero, sub_zero] at this
      intro i
      calc
        f y i = re (( -((T i) 1)⁻¹ • L i) y) + c i / re ((T i) 1) := by simp only [f]
            _ ≤ re (( -((T i) 1)⁻¹ • L i) y) + (re ((L i) y) + re ((T i) 1) * φ y) / re ((T i) 1) :=
              by
                apply add_le_add_left
                rw [div_eq_mul_inv, div_eq_mul_inv]
                apply mul_le_mul_of_nonneg_right (this i)
                apply le_of_lt (inv_pos.mpr (lem4 i))
            _ = re (( -((T i) 1)⁻¹ • L i) y) + re ((L i) y) / re ((T i) 1)
                + re ((T i) 1) * φ y / re ((T i) 1) := by rw [add_div, add_assoc]
            _ = re (-((T i) 1)⁻¹ * L i y) + re ((L i) y) / re ((T i) 1)
                + re ((T i) 1) / re ((T i) 1) * φ y :=
              by
                simp only [coe_smul', Pi.smul_apply, smul_eq_mul]
                rw [mul_div_right_comm]
            _ = - (re (L i y) / re ((T i) 1))  + re ((L i) y) / re ((T i) 1)
                + 1 * φ y :=
              by
                rw (config := {occs := .pos [1]}) [lem5 i]
                rw [← ofReal_inv, ← ofReal_neg, re_ofReal_mul, mul_comm]
                rw [← inv_neg, ← div_eq_mul_inv, div_neg, div_self]
                exact (ne_of_gt (lem4 i))
            _ = φ y := by rw [neg_add_cancel, zero_add, one_mul]
    use φ y; intro z hz; rcases (mem_range.mp hz) with ⟨i, hfi⟩
    rw [← hfi] ; exact this i
  intro x; simp only; constructor
  · exact hf x
  · have lem6 : ∀ (x : E), ∀ (s : 𝕜), iSup (f x) ≤ re s ↔ φ x ≤ re s := by
      intro x s
      constructor
      · intro hxs
        have : (x,s) ∈ C := by
          rw [← hLTc1]
          simp only [ge_iff_le, sub_nonneg, mem_iInter, mem_setOf_eq]
          have hi : ∀i, (f x) i ≤ re s := by apply (ciSup_le_iff (hf x)).mp ; use hxs
          intro i
          calc
            c i = c i / re ((T i) 1) * re ((T i) 1) :=
              by
                rw [← mul_div_right_comm, mul_div_assoc, div_self, mul_one]
                exact (ne_of_gt (lem4 i))
            _ = (- re ( -((T i) 1)⁻¹ • L i x) + re ( -((T i) 1)⁻¹ • L i x)
              + c i / re ((T i) 1)) * re ((T i) 1) := by rw [neg_add_cancel, zero_add]
            _ = - re ( -((T i) 1)⁻¹ • L i x) * re ((T i) 1) + (re ( -((T i) 1)⁻¹ • L i x)
              + c i / re ((T i) 1)) * re ((T i) 1) := by linarith
            _ = re ((L i) x) +  (re ( -((T i) 1)⁻¹ • L i x)
              + c i / re ((T i) 1)) * re ((T i) 1) :=
              by
                rw (config := {occs := .pos [1]}) [lem5 i]
                simp only [smul_eq_mul, ← ofReal_inv, ← ofReal_neg]
                rw [re_ofReal_mul]
                rw (config := {occs := .pos [2]}) [neg_mul]
                rw [neg_neg, mul_comm (re ((T i) 1))⁻¹, inv_mul_cancel_right₀]
                exact (ne_of_gt (lem4 i))
            _ ≤ re ((L i) x) +  re s * re ((T i) 1) :=
              by
                simp only [f] at hi
                have : re ((-((T i) 1)⁻¹ • L i) x) + c i / re ((T i) 1) ≤ re s := hi i
                have : (re ( -((T i) 1)⁻¹ • L i x)
                  + c i / re ((T i) 1)) * re ((T i) 1) ≤ re s * re ((T i) 1) :=
                    mul_le_mul_of_nonneg_right this (le_of_lt (lem4 i))
                apply add_le_add_left this
            _ = re ((L i) x) + re ((T i) s) :=
              by
                rw [lem1 i s]
                rw (config := { occs := .neg [1]}) [lem5 i]
                rw [re_ofReal_mul, mul_comm]
        use this
      · intro hxs; apply ciSup_le; intro i
        have : (x,s) ∈ C := hxs
        rw [← hLTc1, mem_iInter] at this
        have := this i
        simp only [mem_setOf_eq] at this
        calc
          re (-((T i) 1)⁻¹ • L i  x) + c i / re ((T i) 1) = - re ((L i) x) / re ((T i) 1)
          + c i / re ((T i) 1) :=
            by
              rw (config := {occs := .pos [1]}) [lem5 i]
              simp only [smul_eq_mul, ← ofReal_inv, ← ofReal_neg]
              rw [re_ofReal_mul, neg_mul, ← div_eq_inv_mul, ← neg_div]
          _ = (- re ((L i) x) + c i) / re ((T i) 1) :=
            by
              rw [div_add_div_same]
          _ ≤ re ((T i) s) / re ((T i) 1) :=
            by
              apply (div_le_div_iff_of_pos_right (lem4 i)).mpr
              linarith only [this]
          _ = re s :=
            by
              rw [lem1 i s]
              rw (config := {occs := .pos [1]}) [lem5 i]
              rw [re_ofReal_mul, mul_div_right_comm]
              rw [div_eq_mul_inv, mul_inv_cancel₀, one_mul]
              exact (ne_of_gt (lem4 i))
    apply le_antisymm
    · rw [← @ofReal_re 𝕜 (by infer_instance) (φ x)]
      apply (lem6 x (φ x)).mpr
      simp only [ofReal_re, le_refl]
    · rw [← @ofReal_re 𝕜 (by infer_instance) (⨆ i, re ((-((T i) 1)⁻¹ • L i) x)
        + c i / re ((T i) 1))]
      apply (lem6 x (ofReal (⨆ i, re ((-((T i) 1)⁻¹ • L i) x) + c i / re ((T i) 1)))).mp
      simp only [ofReal_re, f, le_refl]

-- Conditional expectation commutes with bounded linear functional
theorem condExpL1_comp_ContinuousLinearMap {α E F : Type*}
  [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [CompleteSpace F] [NormedSpace ℝ F]
  {m mα : MeasurableSpace α} (hm : m ≤ mα) {μ : Measure α} [SigmaFinite (μ.trim hm)]
  {f : α → E} (hf_int : Integrable f μ) (T : E →L[ℝ] F) :
  ∀ᵐ x ∂μ,(T ∘ μ[f | m]) x = μ[T ∘ f | m] x := by
  apply ae_eq_condExp_of_forall_setIntegral_eq
  · exact integrable_comp T hf_int
  · intro s ms hs
    apply Integrable.integrableOn
    exact integrable_comp T integrable_condExp
  · intro s ms hs
    simp only [Function.comp_apply]; apply Eq.trans
    · exact ContinuousLinearMap.integral_comp_comm T (Integrable.restrict integrable_condExp)
    · apply Eq.trans
      · apply congrArg T; apply setIntegral_condExp hm hf_int ms
      · exact (ContinuousLinearMap.integral_comp_comm T (Integrable.restrict hf_int)).symm
  · apply Continuous.comp_aestronglyMeasurable T.cont
    apply AEStronglyMeasurable.congr
    · exact aestronglyMeasurable_condExpL1 (f := f)
    · exact (condExp_ae_eq_condExpL1 hm f).symm

-- Conditional expectation commutes with affine functions
theorem condexpL1_comp_affine {α 𝕜 E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [RCLike 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    {m mα : MeasurableSpace α} (hm : m ≤ mα) {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → E} (hf_int : Integrable f μ) (T : E →L[𝕜] 𝕜) (a : ℝ) :
    ∀ᵐ x ∂μ, re (T (μ[f | m] x)) + a = μ[re ∘ T ∘ f + (fun y ↦ a) | m] x := by
    let g := @reCLM 𝕜 (by infer_instance)
    let h := restrictScalars ℝ T
    have reTf_int : Integrable ((re ∘ T) ∘ f) μ := integrable_comp (comp g h) hf_int
    have hp : ∀ᵐ x ∂μ, (re ∘ T) (μ[f | m] x) + a =
      (μ[(re ∘ T) ∘ f | m] + μ[(fun y ↦ a) | m]) x := by
      simp only [Pi.add_apply]
      filter_upwards [condExpL1_comp_ContinuousLinearMap hm hf_int (comp g h)] with b hb
      simp only [coe_comp', g, h, coe_restrictScalars', reCLM_apply] at hb
      simp only [condExp_const hm a, hb.symm, Function.comp_apply]
    exact ae_eq_trans hp (ae_eq_symm ((condExp_add reTf_int (integrable_const a)) m))

-- Conditional Jensen (assume that X is separable)
theorem condJensenSep {α X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SeparableSpace X]
  {m mα : MeasurableSpace α} (hm : m ≤ mα) {μ : Measure α} [IsFiniteMeasure μ]
  {φ : X → ℝ} (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
  {f : α → X} (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
  ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  rcases (convexfun_eq_sup_affine (𝕜 := ℝ) hφ_cvx hφ_cont) with ⟨L, c, hp⟩
  have py : ∀ᵐ a ∂μ, ∀ i : ℕ, re ((L i) (μ[f | m] a)) + c i
    = μ[re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i)) | m] a := by
    rw [ae_all_iff]; intro i; apply condexpL1_comp_affine hm hf_int (L i) (c i)
  have pz : ∀ᵐ a ∂μ, ∀ i : ℕ, (re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i))) a ≤ (φ ∘ f) a := by
    rw [ae_all_iff]; intro i; filter_upwards with a
    rw [Function.comp_apply, ← (hp (f a)).2, Pi.add_apply, Function.comp_apply, Function.comp_apply]
    apply le_ciSup (hp (f a)).1 i
  have pw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i))) | m] a
    ≤ μ[φ ∘ f | m] a := by
    rw [ae_all_iff]; intro i; apply condExp_mono
    · let g := @reCLM ℝ (by infer_instance)
      have reLif_int : Integrable (fun (a : α) ↦ (re ∘ (L i)) (f a)) μ
        := integrable_comp (comp g (L i)) hf_int
      exact Integrable.add reLif_int (integrable_const (c i))
    · exact hφ_int
    · exact ae_all_iff.mp pz i
  filter_upwards [py, pw] with a
  intro hy hw
  rw [← (hp (μ[f | m] a)).right]
  apply ciSup_le
  intro i
  rw [hy i]
  apply hw i

lemma stronglyMeasurable_g' {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] {f : Ω → X}
  (hf : StronglyMeasurable f) {Y : Set X} (h_subset : Set.range f ⊆ Y) [SecondCountableTopology Y] :
  StronglyMeasurable (fun ω ↦ (⟨f ω, h_subset (Set.mem_range_self ω)⟩ : Y)) := by
  borelize X
  have hf' := hf.measurable
  have h_meas : Measurable (fun ω ↦ (⟨f ω, h_subset (Set.mem_range_self ω)⟩ : Y)) := hf'.subtype_mk
  exact h_meas.stronglyMeasurable

-- Conditional Jensen
theorem condJensen {α X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {m mα : MeasurableSpace α} (hm : m ≤ mα) {μ : Measure α} [IsFiniteMeasure μ]
  {φ : X → ℝ} (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
  {f : α → X} (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
  ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  have sep := AEStronglyMeasurable.isSeparable_ae_range (Integrable.aestronglyMeasurable hf_int)
  rcases sep with ⟨t, ht, htt⟩
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := by
    apply IsClosed.completeSpace_coe
    apply Submodule.isClosed_topologicalClosure
  have issepY : IsSeparable Y.carrier := (IsSeparable.closure (IsSeparable.span ht))
  have : SeparableSpace Y :=
    IsSeparable.separableSpace issepY
  have : SecondCountableTopology Y :=
    IsSeparable.secondCountableTopology issepY
  let φY := φ ∘ Y.subtypeL
  have hφY_cvx : ConvexOn ℝ Set.univ φY := by
    apply ConvexOn.comp_linearMap hφ_cvx Y.subtype
  have hφ_cont : LowerSemicontinuous φY := by
    apply LowerSemicontinuous.comp_continuous hφ_cont
    exact Y.subtypeL.cont
  have tsubY : ∀ x ∈ t, x ∈ Y.carrier := by
    simp only [← Set.subset_def]
    apply subset_trans Submodule.subset_span subset_closure
  have aeinY : ∀ᵐ (x : α) ∂μ, f x ∈ Y.carrier := by
    filter_upwards [htt] with a ha; exact tsubY (f a) ha
  classical
  let fY : α → Y := fun a =>
    if h : f a ∈ Y.carrier
    then ⟨f a, h⟩
    else ⟨0, Y.zero_mem⟩
  let fX : α → X := Y.subtypeL ∘ fY
  have lem1 : f =ᶠ[ae μ] fX := by
    filter_upwards [aeinY] with a ha
    simp only [fX, Function.comp_apply, fY, ha, reduceDIte, Submodule.subtypeL_apply]
  have hfX_int : Integrable fX μ := Integrable.congr hf_int lem1
  let borelX : MeasurableSpace X := borel X
  let borelY : MeasurableSpace ↥Y := borel Y
  have : BorelSpace X := by constructor; simp only [borelX]
  have : BorelSpace ↥Y := by constructor; simp only [borelY]
  have hfY_int : Integrable fY μ := by
    constructor
    · have hs : MeasurableSet Y.carrier := by
        apply IsClosed.measurableSet
        apply Submodule.isClosed_topologicalClosure
      have h_nonempty : Y.carrier.Nonempty := by use 0; exact Y.zero_mem
      have lem := AEStronglyMeasurable.exists_stronglyMeasurable_range_subset
        hf_int.1 hs h_nonempty aeinY
      rcases lem with ⟨g, hg1, hg2, hg3⟩
      let g' := fun (a : α) ↦ (⟨g a, hg2 a⟩ : Y)
      have : StronglyMeasurable g' := stronglyMeasurable_g' hg1 (Set.range_subset_iff.mpr hg2)
      have : fY =ᶠ[ae μ] g' := by
        filter_upwards [hg3, aeinY] with a ha1 ha2
        simp only [fY, g', ha2, reduceDIte, Subtype.mk.injEq]
        exact ha1
      use g'
    · apply HasFiniteIntegral.mono hfX_int.2
      simp only [fX, Function.comp_apply, Submodule.coe_norm,
        Submodule.subtypeL_apply, le_refl, Filter.eventually_true]
  have lem2 : φ ∘ f =ᶠ[ae μ] φY ∘ fY := by
    filter_upwards [lem1] with a ha
    simp only [φY, Function.comp_apply, ha, fX]
  have hφYfY_int : Integrable (φY ∘ fY) μ := Integrable.congr hφ_int lem2
  have lem3 : ∀ᵐ a ∂μ, μ[f | m] a = μ[fX | m] a := condExp_congr_ae lem1
  have lem4 : ∀ᵐ a ∂μ, μ[f | m] a = Y.subtypeL (μ[fY | m] a) := by
    apply ae_eq_trans
    · exact lem3
    · simp only [fX]
      exact ae_eq_symm (condExpL1_comp_ContinuousLinearMap hm hfY_int Y.subtypeL)
  have lem5 : ∀ᵐ a ∂μ, φ (μ[f | m] a) = φY (μ[fY | m] a) := by
    filter_upwards [lem4] with a ha
    simp only [φY, Function.comp_apply, ha]
  have lem6 : ∀ᵐ a ∂μ, φ (μ[fY | m] a) ≤ μ[φY ∘ fY | m] a :=
    condJensenSep hm hφY_cvx hφ_cont hfY_int hφYfY_int
  have lem7 : μ[φY ∘ fY | m] =ᶠ[ae μ] μ[φ ∘ f | m] := condExp_congr_ae lem2.symm
  filter_upwards [lem5, lem6, lem7] with a ha1 ha2 ha3
  calc
    φ (μ[f|m] a) = φY (μ[fY | m] a) := ha1
    _ ≤ μ[φY ∘ fY | m] a := ha2
    _ = μ[φ ∘ f | m] a := ha3

end RCLike
