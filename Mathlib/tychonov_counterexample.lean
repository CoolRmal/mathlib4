/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Tychonov's Solution to Heat Equations
This file shows that the infinite series given by Tychonov is a solution to the heat equation.
We first prove some estimates of this series by using Cauchy's integral formula to justify the
uniform convergence of this series. We then prove a lemma that allows us to differentiate an
infinite series. Finally, we prove that there are uncountably many solutions to heat equations
on the set `ℝ × Set.Ioi 0` satisfying the zero initial condition.

Main Lemmas that can probably go into Mathlib.

Reference: Fritz John PDE.
-/

noncomputable section
open InnerProductSpace Metric Complex ContDiff
open scoped Real NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A definition of classical solutions to the 1D heat equation on the set `U × (0,∞)`. -/
def IsClassical1DHeatSolution (U : Set ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, ContDiffOn ℝ 1 (fun t : ℝ ↦ u x t) (Set.Ioi 0)) ∧
  (∀ t, 0 < t → ContDiffOn ℝ 2 (fun x : ℝ ↦ u x t) U) ∧
  ∀ x ∈ U, ∀ t, 0 < t → deriv (fun s ↦ u x s) t - Δ (fun y ↦ u y t) x = 0

/-- An auxillary function. -/
def g (α : ℝ) (t : ℝ) := if 0 < t then rexp (- t ^ (- α)) else 0

/-- An auxillary constant. -/
def θ (α : ℝ) : ℝ := (2 * Real.cos 1) ^ (1 / α) - 1

lemma cosonegehalf : Real.cos 1 > 1 / 2 := by
  rw [gt_iff_lt]
  refine lt_of_eq_of_lt (b:= 1 - 1 ^ 2 / 2) ?_ ?_
  · rw [one_pow]; exact (sub_self_div_two 1).symm
  · exact Real.one_sub_sq_div_two_lt_cos (one_ne_zero)

lemma lem0 : 0 ≤ 2 * Real.cos 1 := mul_nonneg (by linarith) (le_of_lt Real.cos_one_pos)

lemma onelepi : 1 ≤ π := LE.le.trans (by linarith) Real.two_le_pi

lemma cos1lt1 : Real.cos 1 < 1 := by
  rw (config := {occs := .neg [1]}) [← Real.cos_zero]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (refl 0) onelepi (by linarith)

lemma θpos {α : ℝ} (hα : 1 < α) : 0 < θ α := by
  unfold θ
  rw [sub_pos]
  rw (config := {occs := .pos [1]}) [← Real.one_rpow (1 / α)]
  rw [Real.rpow_lt_rpow_iff]
  · rw (config := {occs := .pos [1]}) [← mul_one_div_cancel (a := 2) (by linarith)]
    rw [mul_lt_mul_iff_right₀ (by linarith), ← gt_iff_lt]
    exact cosonegehalf
  · linarith
  · exact lem0
  · simp [inv_pos]; linarith

lemma compare {α : ℝ} (hα : 1 < α) : θ α * (1 - θ α)⁻¹ < Real.sin (1 / α) := by sorry

lemma cos1upperbound {α : ℝ} (hα : 1 < α) : 0 ≤ (2 * Real.cos 1) ^ (1 / α) := by
  have : 0 < 1 / α := by simp [inv_pos]; linarith
  rw [← Real.zero_rpow (x := 1 / α), Real.rpow_le_rpow_iff]
  · exact lem0
  · linarith
  · exact lem0
  · exact this
  · linarith

lemma θle1 {α : ℝ} (hα : 1 < α) : θ α < 1 := by
    unfold θ
    rw [tsub_lt_iff_left, one_add_one_eq_two,
      ← Real.rpow_lt_rpow_iff (x := (2 * Real.cos 1) ^ (1 / α)) (y := 2) (z := α)]
    all_goals try linarith [cos1upperbound hα]
    · rw [← Real.rpow_mul, ← mul_comm α, mul_one_div_cancel, Real.rpow_one]
      · have : 2 * Real.cos 1 < 2 := by
          rw (config := {occs := .neg [1]}) [← mul_one 2]
          rw [mul_lt_mul_iff_of_pos_left (by linarith)]
          exact cos1lt1
        exact LT.lt.trans this (Real.self_lt_rpow_of_one_lt (by linarith) hα)
      · linarith
      · exact lem0
    · rw [← Real.rpow_le_rpow_iff (z := α), ← Real.rpow_mul, ← mul_comm α,
        mul_one_div_cancel, Real.rpow_one, Real.one_rpow]
      all_goals try linarith [cos1upperbound hα]
      · exact (div_le_iff₀' (by linarith)).1 (le_of_lt (α := ℝ) (gt_iff_lt.1 cosonegehalf))
      · exact lem0

lemma θrepos {α : ℝ} (hα : 1 < α) : ∀ ψ : ℝ, 0 < (1 + θ α * (cexp (I * ψ))).re := by
  intro ψ
  simp [mul_comm I, exp_ofReal_mul_I_re]
  suffices -1 < θ α * Real.cos ψ from by linarith
  apply lt_of_lt_of_le (b := - θ α) ?_ ?_
  · simp [θle1 hα]
  · rw [← mul_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.neg_one_le_cos ψ) (le_of_lt (θpos hα))

lemma θlowerbound {α : ℝ} (hα : 1 < α) :
    ∀ ψ : ℝ, √(normSq (1 + ↑(θ α) * cexp (I * ↑ψ))) ≥ 1 - θ α := by
  intro ψ
  simp [normSq, mul_comm I, ← pow_two, add_sq, mul_pow, add_assoc, add_assoc, ← mul_add,
    - tsub_le_iff_right]
  apply LE.le.trans (b := √(1 - 2 * (θ α) + (θ α) ^ 2))
  · rw [← mul_one 2]
    rw (config := {occs := .pos [2]}) [← one_pow 2]
    have : 0 ≤ 1 - θ α := by linarith [θle1 hα]
    rw [← sub_sq 1 (θ α), Real.sqrt_sq this]
  · refine Real.sqrt_le_sqrt ?_
    rw [sub_eq_add_neg, add_assoc, add_le_add_iff_left, add_le_add_iff_right,
      neg_mul_eq_mul_neg, mul_le_mul_iff_right₀ (by linarith)]
    rw (config := {occs := .pos [1]}) [← mul_one (θ α)]
    rw [neg_mul_eq_mul_neg, mul_le_mul_iff_right₀ (θpos hα)]
    exact Real.neg_one_le_cos ψ

lemma θnezero {α : ℝ} (hα : 1 < α) : ∀ ψ : ℝ, 1 + θ α * (cexp (I * ψ)) ≠ 0 := by
  intro ψ
  rw [← Complex.normSq_pos, ← Real.sqrt_pos]
  exact lt_of_lt_of_le (by linarith [θle1 hα]) (ge_iff_le.1 (θlowerbound hα ψ))

lemma abs_of_odd_function {f : ℝ → ℝ} (hf1 : ∀ x, f (-x) = -f x)
    (hf2 : ∀ x, 0 ≤ x → 0 ≤ f x) (x : ℝ) : |f x| = f |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg (hf2 x hx), abs_of_nonneg hx]
  · rw [abs_of_nonpos (a := f x), abs_of_neg]
    · exact (hf1 x).symm
    · simpa using hx
    · rw [← neg_neg x, hf1 (-x)]; simp
      exact hf2 (-x) (neg_nonneg_of_nonpos (le_of_lt (not_le.1 hx)))

lemma re_ge_half {α : ℝ} (hα : 1 < α) : ∀ ψ : ℝ,
    ((1 + θ α * (cexp (I * ψ))) ^ (- α : ℂ)).re ≥ 1 / 2 := by
  intro ψ; norm_cast
  rw [cpow_ofReal_re (1 + θ α * (cexp (I * ψ))) (- α)]
  have lem1 : Real.cos ((1 + ↑(θ α) * cexp (I * ↑ψ)).arg * -α) ≥ Real.cos 1 := by
    rw [← Real.cos_abs, ge_iff_le]
    refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ onelepi ?_
    · exact abs_nonneg ((1 + ↑(θ α) * cexp (I * ↑ψ)).arg * -α)
    · simp only [arg, le_of_lt (θrepos hα ψ)]
      simp [abs_of_odd_function Real.arcsin_neg, abs_of_pos (by linarith : 0 < α)]
      rw [← le_div_iff₀ (by linarith), Real.arcsin_le_iff_le_sin']
      refine LE.le.trans ?_ (le_of_lt (compare hα))
      · rw [mul_div_assoc, abs_mul, abs_of_pos (θpos hα)]
        refine (mul_le_mul_iff_of_pos_left (θpos hα)).2 ?_
        rw [abs_div, div_le_iff₀]
        · apply LE.le.trans (abs_im_le_norm (cexp (I * ↑ψ)))
          simp [mul_comm I, le_inv_mul_iff₀ (by linarith [θle1 hα] : 0 < 1 - θ α),
            -tsub_le_iff_right]
          rw [norm_def, ← ge_iff_le, ← mul_comm I]
          exact θlowerbound hα ψ
        · simp [θnezero hα ψ]
      · simp; constructor
        · have : 0 < α ⁻¹ := inv_pos.2 (by linarith)
          refine LE.le.trans ?_ (le_of_lt this)
          simp [le_of_lt Real.pi_div_two_pos]
        · exact lt_of_lt_of_le (b := 1) (inv_lt_one_of_one_lt₀ hα) Real.one_le_pi_div_two
  have lem2 : ‖1 + ↑(θ α) * cexp (I * ↑ψ)‖ ≤ 1 + θ α := by
    simp [norm_def, normSq, mul_comm I, ← pow_two, add_sq, mul_pow, add_assoc, add_assoc, ← mul_add]
    apply LE.le.trans (b := √(1 + 2 * (θ α) + (θ α) ^ 2))
    · refine Real.sqrt_le_sqrt ?_
      rw [add_assoc, add_le_add_iff_left, add_le_add_iff_right,
        mul_le_mul_iff_right₀ (by linarith)]
      rw (config := {occs := .neg [1]}) [← mul_one (θ α)]
      rw [mul_le_mul_iff_right₀]
      · exact Real.cos_le_one ψ
      · exact θpos hα
    · rw [← mul_one 2]
      rw (config := {occs := .pos [1]}) [← one_pow 2]
      have : 0 ≤ 1 + θ α := LE.le.trans (le_of_lt (θpos hα)) (by linarith)
      rw [← add_sq 1, Real.sqrt_sq this]
  calc
    ‖1 + ↑(θ α) * cexp (I * ↑ψ)‖ ^ (-α) * Real.cos ((1 + ↑(θ α) * cexp (I * ↑ψ)).arg * -α) ≥
      ‖1 + ↑(θ α) * cexp (I * ↑ψ)‖ ^ (-α) * Real.cos 1 := mul_le_mul_of_nonneg_left
        lem1 (Real.rpow_nonneg (norm_nonneg (1 + ↑(θ α) * cexp (I * ↑ψ))) (-α))
    _ ≥ (1 + θ α) ^ (-α) * Real.cos 1 := by
        refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ?_ ?_ ?_) ?_
        · rw [norm_pos_iff]; exact θnezero hα ψ
        · exact lem2
        · linarith
        · exact le_of_lt Real.cos_one_pos
    _ ≥ 1 / 2 := by
        unfold θ
        simp only [one_div, add_sub_cancel, ge_iff_le]
        rw [← div_le_iff₀, div_eq_mul_inv, ← mul_inv, Real.rpow_neg, ← Real.rpow_mul,
          inv_mul_cancel₀, Real.rpow_one]
        · linarith
        · exact lem0
        · exact Real.rpow_nonneg lem0 α⁻¹
        · exact Real.cos_one_pos

lemma mul_cpow {x z : ℝ} {y : ℂ} (hx : 0 < x) (hy : y ≠ 0) :
    (x * y) ^ (z : ℂ) = (x ^ z : ℝ) * (y ^ (z : ℂ)) := by
  have xnezero : x ≠ (0 : ℂ) := ofReal_ne_zero.2 (by linarith)
  simp [← cpow_eq_pow, cpow, ← cpow_eq_pow, cpow, hy, xnezero, mul_comm (x : ℂ),
    log_mul_ofReal x hx, add_mul, exp_add]
  rw [Real.rpow_def_of_pos hx, Real.exp, ofReal_exp_ofReal_re, ofReal_mul]

/-- Complex Version of `g`. -/
def cg (α : ℝ) (z : ℂ) := cexp (- z ^ (- α : ℂ))

/-- `cg = g` for positive real numbers. -/
theorem cg_eq_g (α : ℝ) (t : ℝ) (ht : 0 < t) : cg α (t : ℂ) = g α t := by
  simp [cg, g, ht, ofReal_cpow (le_of_lt ht)]

/-- `cg` is differentiable. -/
theorem cgDiff (α : ℝ) : DifferentiableOn ℂ (cg α) {z : ℂ | 0 < z.re} := by
  let g : ℂ → ℂ := fun z => z ^ (- α : ℂ)
  let h : ℂ → ℂ := fun z => -z
  have : cg α = cexp ∘ h ∘ g := by ext x; simp [cg, g, h]
  rw [this]
  intro x hx
  refine DifferentiableWithinAt.comp (t := Set.univ) x ?_ ?_ ?_
  · simp [differentiableWithinAt_univ]
  · refine DifferentiableWithinAt.comp (t := Set.univ) x (by fun_prop) ?_ ?_
    · refine DifferentiableWithinAt.cpow_const (by fun_prop) ?_
      · simp_all [slitPlane]
    · intro x hx; simp
  · intro x hx; simp

/-- If `cf : ℂ → ℂ` is differentiable on `{z : ℂ | 0 < z.re}`, then its `n`-th derivative is also
differentiable on `{z : ℂ | 0 < z.re}`. -/
theorem iteratedDeriv_Diff {cf : ℂ → ℂ} (n : ℕ) (hcf : DifferentiableOn ℂ cf {z : ℂ | 0 < z.re}) :
    DifferentiableOn ℂ (iteratedDeriv n cf) {z : ℂ | 0 < z.re} := by
  induction n with
  | zero => simp [iteratedDeriv_zero, hcf]
  | succ n ih =>
    simp [iteratedDeriv_succ]
    refine DifferentiableOn.deriv ?_ ?_
    · exact ih
    · exact isOpen_lt continuous_const Complex.continuous_re

/-- If `cf : ℂ → ℂ` is differentiable on `{z : ℂ | 0 < z.re}` and `cf x = f x` for some `f : ℝ → ℝ`
and all `x : ℝ`, then `f` is differentiable on the positive real axis. -/
theorem restrict_Diff {cf : ℂ → ℂ} {f : ℝ → ℝ} (hcff : ∀ x : ℝ, 0 < x → cf (x : ℂ) = f x) :
    DifferentiableOn ℂ cf {z : ℂ | 0 < z.re} → DifferentiableOn ℝ f (Set.Ioi 0) := by
  intro ih
  have h_restrict : DifferentiableOn ℝ (fun x : ℝ => cf (x : ℂ)) (Set.Ioi 0) :=
    DifferentiableOn.comp (ih.restrictScalars ℝ)
    (Complex.ofRealCLM.differentiable.differentiableOn) fun x hx => by simpa using hx
  have h_diff_f : DifferentiableOn ℝ (fun x : ℝ => (cf x).re) (Set.Ioi 0) :=
    reCLM.differentiable.comp_differentiableOn h_restrict
  exact h_diff_f.congr fun x hx => by rw [hcff x hx] ; norm_num

/-- If `cf : ℂ → ℂ` is differentiable on `{z : ℂ | 0 < z.re}` and `cf x = f x` for some `f : ℝ → ℝ`
and all `x : ℝ`, then the `n`-th derivative of `f` is differentiable on the positive real axis.
Moreover, the two notions of `n`-th derivatives coincides on the positive real axis. -/
theorem iteratedDeriv_restrict_eq {cf : ℂ → ℂ} {f : ℝ → ℝ} (n : ℕ)
    (hcf : DifferentiableOn ℂ cf {z : ℂ | 0 < z.re}) (hcff : ∀ x : ℝ, 0 < x → cf (x : ℂ) = f x) :
    (∀ t : ℝ, 0 < t → iteratedDeriv n cf (t : ℂ) = iteratedDeriv n f t) ∧
    DifferentiableOn ℝ (iteratedDeriv n f) (Set.Ioi 0) := by
  induction n with
  | zero =>
    simp [iteratedDeriv_zero]; constructor
    · exact hcff
    · exact restrict_Diff hcff hcf
  | succ n ih =>
    have : ∀ (t : ℝ), 0 < t → (iteratedDeriv (n + 1) cf) ↑t =
      ↑((iteratedDeriv (n + 1) f) t) := by
      simp [iteratedDeriv_succ]; intro t ht
      have deriv_eq : deriv (iteratedDeriv n cf) (t : ℂ) =
        deriv (fun x : ℝ => iteratedDeriv n cf (x : ℂ)) t := by
        have chain : deriv (iteratedDeriv n cf ∘ (fun x : ℝ => x : ℝ → ℂ)) t =
          deriv (iteratedDeriv n cf) (t : ℂ) * deriv (fun x : ℝ => x : ℝ → ℂ) t := by
          have memt : (t : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp [ht]
          have := (iteratedDeriv_Diff n hcf) t memt
          have : derivWithin (iteratedDeriv n cf ∘ (fun x : ℝ => x : ℝ → ℂ)) (Set.Ioi 0) t =
            derivWithin (iteratedDeriv n cf) {z : ℂ | 0 < z.re} (t : ℂ) *
            derivWithin (fun x : ℝ => x : ℝ → ℂ) (Set.Ioi 0) t := by
            refine derivWithin_comp t this ?_ ?_
            · exact Complex.ofRealCLM.differentiableAt.differentiableWithinAt
            · simp [Set.MapsTo]
          rw [derivWithin_of_isOpen, derivWithin_of_isOpen, derivWithin_of_isOpen] at this
          · exact this
          · exact isOpen_Ioi
          · simp [ht]
          · exact isOpen_lt continuous_const Complex.continuous_re
          · exact memt
          · exact isOpen_Ioi
          · simp [ht]
        convert chain.symm using 1
        erw [Complex.ofRealCLM.deriv]
        norm_num
      have derivnf : HasDerivAt (iteratedDeriv n f) (deriv (iteratedDeriv n f) t) t := by
        have : Set.Ioi 0 ∈ nhds t := Ioi_mem_nhds ht
        convert HasDerivWithinAt.hasDerivAt (hasDerivWithinAt_derivWithin_iff.2 (ih.2 t ht))
          this using 1
        exact (derivWithin_of_isOpen isOpen_Ioi (by simp [ht])).symm
      convert HasDerivAt.deriv (HasDerivAt.ofReal_comp <| derivnf) using 1
      rw [deriv_eq, ← derivWithin_of_isOpen (isOpen_Ioi (a := 0)),
        ← derivWithin_of_isOpen (isOpen_Ioi (a := 0)), derivWithin_congr]
      · intro x hx; exact ih.1 x hx
      · exact ih.1 t ht
      repeat simp [ht]
    constructor
    · exact this
    · exact restrict_Diff this (iteratedDeriv_Diff (n + 1) hcf)

/-- `iteratedDeriv n cg = iteratedDeriv n g` for positive real numbers. -/
theorem iteratedDeriv_cg_eq_iteratedDeriv_g {t : ℝ} (α : ℝ) (n : ℕ) (ht : 0 < t) :
    iteratedDeriv n (cg α) (t : ℂ) = iteratedDeriv n (g α) t :=
    (iteratedDeriv_restrict_eq n (cgDiff α) (cg_eq_g α)).1 t ht

/-- `cg` is differenitable on a ball and continuous on its closure. -/
theorem cgDiffContOnCl {α t : ℝ} (ht : 0 < t) (hα : 1 < α) :
    DiffContOnCl ℂ (cg α) (ball (t : ℂ) ((θ α) * t)) := by
  let g : ℂ → ℂ := fun z => z ^ (- α : ℂ)
  let h : ℂ → ℂ := fun z => -z
  have : cg α = cexp ∘ h ∘ g := by ext x; simp [cg, g, h]
  rw [this]
  have (x : ℂ) (hx : x ∈ closure (ball (↑t) (θ α * t))) : 0 < x.re := by
    have : x = x - t + t := by simp
    rw [this, add_re, ofReal_re]
    apply lt_add_of_neg_add_lt
    simp only [add_zero]
    suffices |-(x - ↑t).re| < t from (abs_lt.1 this).2
    simp only [abs_neg]
    rw [closure_ball, closedBall] at hx
    simp [Complex.dist_eq] at hx
    refine lt_of_le_of_lt (abs_re_le_norm (x - t)) (lt_of_le_of_lt hx ?_)
    rw (config := {occs := .neg [1]}) [← one_mul t]
    exact mul_lt_mul_of_pos_right (θle1 hα) ht
    exact ne_of_gt (mul_pos (θpos hα) ht)
  constructor
  · refine DifferentiableOn.mono (cgDiff α) ?_
    intro x hx
    exact this x (subset_closure hx)
  · refine ContinuousOn.comp (t := Set.univ) (by fun_prop) ?_ ?_
    · refine ContinuousOn.comp (t := Set.univ) (by fun_prop) ?_ ?_
      · refine ContinuousOn.cpow_const (by fun_prop) ?_
        intro x hx; simp [slitPlane]; apply Or.inl; exact this x hx
      · intro x hx; simp
    · intro x hx; simp

lemma estimate_on_sphere_of_g {α t : ℝ} (hα : 1 < α) (ht : 0 < t) :
    ∀ z ∈ sphere (t : ℂ) (θ α * t), ‖cg α z‖ ≤ rexp (- t ^ (- α) / 2) := by
  intro z (hz : ‖z - t‖ = θ α * t); rw [cg, norm_exp]
  refine Real.exp_le_exp_of_le (x := (-z ^ (- α : ℂ)).re) (y := (-t ^ (-α) / 2)) ?_
  have : ∃ ψ : ℝ, z = t * (1 + θ α * (cexp (I * ψ))) := by
    have := (norm_mul_exp_arg_mul_I (z - t)).symm
    use (z - t).arg
    simp [hz, sub_eq_iff_eq_add', mul_comm (θ α), ← mul_comm I (z - t).arg, mul_assoc,
      ← mul_one_add (t : ℂ)] at this
    exact this
  obtain ⟨ψ, hψ⟩ := this
  calc
    (-z ^ (- α : ℂ)).re =  - ((t ^ (- α) : ℝ) * (1 + θ α * (cexp (I * ψ))) ^ (- α : ℂ)).re := by
      rw [hψ, neg_re]; norm_cast; rw [mul_cpow ht]; exact θnezero hα ψ
    _ = - t ^ (- α) * ((1 + θ α * (cexp (I * ψ))) ^ (- α : ℂ)).re := by
      simp [re_ofReal_mul (t ^ (- α)) ((1 + θ α * (cexp (I * ψ))) ^ (- α : ℂ))]
    _ ≤ - t ^ (-α) / 2 := by
      refine mul_le_mul_of_nonpos_left ?_ ?_
      · simpa using re_ge_half hα ψ
      · have h : 0 < t ^ (- α) := Real.rpow_pos_of_pos ht (- α)
        linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Cauchy's integral formula for `n`-th order derivatives. -/
theorem iteratedDeriv_eq_smul_circleIntegral {R : ℝ} {c : ℂ} {n : ℕ} {f : ℂ → E}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) : iteratedDeriv n f c = n.factorial  •
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z := by
  lift R to ℝ≥0 using hR.le
  rw [iteratedDeriv, ← (hf.hasFPowerSeriesOnBall hR).factorial_smul, cauchyPowerSeries]
  simp

/-- Cauchy's estimate for `n`-th order derivatives. -/
theorem norm_iteratedDeriv_le_aux {c : ℂ} {R C : ℝ} {n : ℕ} {f : ℂ → E}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  have : ∀ z ∈ sphere c R, ‖(z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ C / (R ^ n  * R) :=
    fun z (hz : ‖z - c‖ = R) => by
    have := (div_le_div_iff_of_pos_right (mul_pos (pow_pos hR n) hR)).2 (hC z hz)
    simp [norm_smul, norm_pow, norm_inv, hz, ← div_eq_inv_mul, ← div_mul_eq_div_div, mul_comm R]
    exact this
  calc
    ‖iteratedDeriv n f c‖ = ‖n.factorial • (2 * π * I : ℂ)⁻¹ •
      ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ :=
      congr_arg norm (iteratedDeriv_eq_smul_circleIntegral hR hf)
    _ ≤ n.factorial * (R * (C / (R ^ n * R))) := by
      simp only [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
      have := (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le this)
      refine mul_le_mul_of_nonneg_left this (?_ : (0 : ℝ) ≤ n.factorial)
      exact_mod_cast ((Nat.factorial_pos n).le)
    _ = n.factorial * C / R ^ n := by
      grind

/-- Apply Cauchy's estimate to `g`. -/
theorem CauchyEstimate_of_g {α t : ℝ} (hα : 1 < α) (ht : 0 < t) (n : ℕ) :
    |iteratedDeriv n (g α) t| ≤ n.factorial * rexp (- t ^ (- α) / 2) / (θ α * t) ^ n := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← iteratedDeriv_cg_eq_iteratedDeriv_g (α := α) n ht]
  exact norm_iteratedDeriv_le_aux (mul_pos (θpos hα) ht) (cgDiffContOnCl ht hα)
    (estimate_on_sphere_of_g hα ht)

/-- Tychonov's counterexample. -/
def u α x t := ∑' (i : ℕ), iteratedDeriv i (g α) t * ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i)

lemma lem_fac (i : ℕ) : (i.factorial : ℝ) ^ 2 ≤ (2 * i).factorial := by
  norm_cast
  rw [sq, two_mul]
  exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

lemma lem_fac' (i : ℕ) : (i.factorial : ℝ) *  ((i + 1).factorial : ℝ) ≤ (2 * i).factorial := by
  induction i with
  | zero => simp
  | succ i ih =>
    norm_num [Nat.factorial_succ, Nat.mul_succ] at *
    nlinarith [sq ( i : ℝ )]

/-- Absolutely convergence of the sequence obtained from Cauchy's estimate. -/
theorem dom_seq (x t α : ℝ) : (Summable fun (i : ℕ) =>
    rexp (- t ^ (- α) / 2) * (i.factorial : ℝ)⁻¹ * (θ α * t) ^ (- i : ℝ) * |x| ^ (2 * i)) := by
  have : Summable (fun i : ℕ => (i.factorial : ℝ)⁻¹ * (1 / (θ α * t) * |x|^2) ^ i) := by
    have : Summable (fun i : ℕ => (1 / (θ α * t) * |x|^2) ^ i / (i.factorial : ℝ)) := by
      exact Real.summable_pow_div_factorial _
    exact this.congr fun i => by ring
  convert this.mul_left (Real.exp (- t ^ (-α) / 2)) using 2
  norm_num
  ring_nf
  norm_num [pow_mul']

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma DifferentiableAt_of_isOpen (f : E → F) {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    DifferentiableAt 𝕜 f x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [DifferentiableAt, DifferentiableWithinAt]; constructor
  · intro hf; obtain ⟨f', hf'⟩ := hf; use f'; exact ((hasFDerivWithinAt_of_isOpen hs hx).2 hf')
  · intro hf; obtain ⟨f', hf'⟩ := hf; use f'; exact ((hasFDerivWithinAt_of_isOpen hs hx).1 hf')

/-- The infinite series used to define `u` is pointwise summable. -/
theorem summable_u {t α : ℝ} (x : ℝ) (ht : 0 < t) (hα : 1 < α) :
    Summable fun n ↦ iteratedDeriv n (g α) t * (↑(2 * n).factorial)⁻¹ * x ^ (2 * n) := by
  simp [← summable_norm_iff]
  refine Summable.of_nonneg_of_le ?_ ?_ (dom_seq x t α)
  · intro; refine norm_nonneg _
  · intro n; simp
    calc
      |iteratedDeriv n (g α) t| * (↑(2 * n).factorial)⁻¹ * |x| ^ (2 * n) ≤ n.factorial *
      rexp (- t ^ (-α) / 2) / (θ α * t) ^ n * (↑(2 * n).factorial)⁻¹ * |x| ^ (2 * n) := by
        rw [mul_assoc, mul_assoc]; gcongr; exact CauchyEstimate_of_g hα ht n
      _ ≤ rexp (- t ^ (-α) / 2) / (θ α * t) ^ n *
        (n.factorial * (↑(2 * n).factorial)⁻¹) * |x| ^ (2 * n) := by field_simp; simp
      _ ≤ rexp (-t ^ (-α) / 2) * (↑n.factorial)⁻¹ * ((θ α * t) ^ n)⁻¹ * |x| ^ (2 * n) := by
        field_simp; rw [mul_div_assoc, mul_div_assoc]
        refine mul_le_mul_of_nonneg_right (lem_fac n) (div_nonneg (by positivity) ?_)
        refine pow_nonneg ?_ n
        exact le_of_lt (mul_pos (θpos hα) ht)

lemma lowerboundK {K : Set ℝ} (hK : K ⊆ Set.Ioi 0) (hCK : IsCompact K) :
    ∃ a > 0, ∀ x ∈ K, a ≤ x := by
  by_cases hK_empty : K = ∅
  · exact ⟨1, by norm_num, by simp +decide [hK_empty]⟩
  · obtain ⟨w, hw⟩ := hCK.exists_isLeast ( Set.nonempty_iff_ne_empty.mpr hK_empty)
    exact ⟨w, hK hw.1, fun x hx => hw.2 hx⟩

lemma upperboundK {K : Set ℝ} (hCK : IsCompact K) : ∃ a > 0, ∀ x ∈ K, x ≤ a := by
  by_cases hK_empty : K = ∅
  · exact ⟨1, by norm_num, by simp +decide [hK_empty]⟩
  · sorry

/-- Calculating the time derivative of `u`. Need to verify locally uniform convergence. -/
theorem deriv_u_t {x t α : ℝ} (ht : 0 < t) (hα : 1 < α) :
    deriv (fun t ↦ u α x t) t = ∑' (i : ℕ), iteratedDeriv (i + 1) (g α) t *
    ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i) := by
  unfold u
  rw [← derivWithin_of_isOpen (isOpen_Ioi (a := 0)), derivWithin_tsum (isOpen_Ioi (a := 0))]
  · congr; ext n
    rw [derivWithin_of_isOpen (isOpen_Ioi (a := 0)) (by simp [ht]), iteratedDeriv_succ]; simp
  · simp [ht]
  · intro y hy; exact summable_u x hy hα
  · unfold SummableLocallyUniformlyOn HasSumLocallyUniformlyOn
    use (fun t => ∑' (n : ℕ), derivWithin (fun t ↦ iteratedDeriv n (g α) t * (↑(2 * n).factorial)⁻¹
      * x ^ (2 * n)) (Set.Ioi 0) t)
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_Ioi (a := 0))]
    intro K hK hCK
    obtain ⟨a, ha⟩ := lowerboundK hK hCK
    let v : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹ * (1 / (θ α * a) * |x|^2) ^ n / (θ α * a)
    refine tendstoUniformlyOn_tsum (u := v) (s := K) ?_ ?_
    · have h_summable : Summable (fun n : ℕ => (1 / (θ α * a) * |x|^2)^n / (n.factorial: ℝ)) := by
        exact Real.summable_pow_div_factorial _;
      convert h_summable.div_const (θ α * a) using 2 ; ring!
    · intro n z hz
      rw [derivWithin_of_isOpen (isOpen_Ioi (a := 0))]
      · simp [← iteratedDeriv_succ]
        have h (r : ℝ) (hr : 0 < r) : 0 ≤ 1 / (θ α * r) * |x| ^ 2 :=
          mul_nonneg (one_div_nonneg.2 (le_of_lt (mul_pos (θpos hα) hr))) (by positivity)
        have hh (r : ℝ) (hr : 0 < r): 0 ≤ (1 / (θ α * r) * |x| ^ 2) ^ n := by
          exact pow_nonneg (h r hr) n
        calc
        |iteratedDeriv (n + 1) (g α) z| * (↑(2 * n).factorial)⁻¹ * |x| ^ (2 * n) ≤
          (n + 1).factorial * rexp (- z ^ (- α) / 2) / (θ α * z) ^ (n + 1) *
          (↑(2 * n).factorial)⁻¹ * |x| ^ (2 * n) := by
            gcongr; exact CauchyEstimate_of_g hα (hK hz) (n + 1)
          _ ≤ rexp (- z ^ (- α) / 2) * (n.factorial : ℝ)⁻¹ * (1 / (θ α * z) * |x|^2) ^ n
            / (θ α * z) := by
            field_simp; rw [mul_comm, ← mul_assoc, mul_div_assoc, mul_div_assoc]
            refine mul_le_mul (lem_fac' n) ?_ ?_ ?_
            · ring_nf; exact le_refl _
            · refine div_nonneg (by positivity) ?_
              refine pow_nonneg ?_ (n + 1)
              exact le_of_lt (mul_pos (θpos hα) (hK hz))
            · positivity
          _ ≤ (n.factorial : ℝ)⁻¹ * (1 / (θ α * z) * |x|^2) ^ n / (θ α * z) := by
            gcongr
            · exact le_of_lt (mul_pos (θpos hα) (hK hz))
            · exact hh z (hK hz)
            · rw [← one_mul (n.factorial : ℝ)⁻¹]; gcongr
              · simp [Real.exp_le_one_iff]
                suffices 0 ≤ z ^ (-α) / 2 from by linarith
                exact div_nonneg (Real.rpow_nonneg (le_of_lt (hK hz)) (-α)) (by positivity)
              · simp
          _ ≤ (n.factorial : ℝ)⁻¹ * (1 / (θ α * a) * |x|^2) ^ n / (θ α * a) := by
            rw [mul_div_assoc, mul_div_assoc]
            refine mul_le_mul_of_nonneg_left (a := (n.factorial : ℝ)⁻¹) ?_ (by positivity)
            gcongr
            · exact hh a ha.1
            · exact mul_pos (θpos hα) ha.1
            · exact h z (hK hz)
            · exact mul_pos (θpos hα) ha.1
            · exact le_of_lt (θpos hα)
            · exact ha.2 z hz
            · exact le_of_lt (θpos hα)
            · exact ha.2 z hz
          _ ≤ v n := by simp [v]
      · exact hK hz
  · intro n r hr
    simp [mul_assoc]
    refine DifferentiableAt.mul_const (𝔸 := ℝ) (𝕜 := ℝ) (E := ℝ) ?_ ?_
    have := (iteratedDeriv_restrict_eq n (cgDiff α) (cg_eq_g α)).2 r hr
    rw [← DifferentiableAt_of_isOpen] at this
    · exact this
    · exact isOpen_Ioi
    · exact hr
  · simp [ht]

lemma dom_seq' (x t α : ℝ) : (Summable fun (i : ℕ) =>
    rexp (- t ^ (- α) / 2) * (i.factorial : ℝ)⁻¹ * (θ α * t) ^ (- (i + 1) : ℝ)
    * |x| ^ (2 * i)) := by
  suffices h_factor : Summable (fun i : ℕ => ((Nat.factorial i)⁻¹ : ℝ) * (θ α * t) ^
    (-((i : ℝ) + 1)) * |x| ^ (2 * i)) by
    convert h_factor.mul_left ( Real.exp ( -t ^ ( -α ) / 2 ) ) using 2 ; ring
  have h_exp_series : Summable (fun i : ℕ => (|x|^2 / (θ α * t)) ^ i / (Nat.factorial i : ℝ)) := by
    exact Real.summable_pow_div_factorial _;
  convert h_exp_series.mul_left ((θ α * t)⁻¹) using 2 ;norm_cast ; norm_num ; ring_nf
  norm_num [ pow_mul' ]

/-- The infinite series obtained by termwise differentiating `u` is pointwise summable. -/
theorem summable_u' {t α : ℝ} (x : ℝ) (ht : 0 < t) (hα : 1 < α) :
    Summable fun b ↦ iteratedDeriv (b + 1) (g α) t * (↑(2 * b).factorial)⁻¹ * x ^ (2 * b):= by
  simp [← summable_norm_iff]
  refine Summable.of_nonneg_of_le ?_ ?_ (dom_seq' x t α)
  · intro; refine norm_nonneg _
  · intro n; simp only [norm_mul, Real.norm_eq_abs, abs_abs, norm_inv, RCLike.norm_natCast,
      norm_pow]
    calc
      |iteratedDeriv (n + 1) (g α) t| * (↑(2 * n).factorial)⁻¹ * |x| ^ (2 * n) ≤ (n + 1).factorial *
      rexp (- t ^ (-α) / 2) / (θ α * t) ^ (n + 1) * (↑(2 * n).factorial)⁻¹ * |x| ^ (2 * n) := by
        rw [mul_assoc, mul_assoc]; gcongr; exact CauchyEstimate_of_g hα ht (n + 1)
      _ ≤ rexp (- t ^ (-α) / 2) / (θ α * t) ^ (n + 1) *
        ((n + 1).factorial * (↑(2 * n).factorial)⁻¹) * |x| ^ (2 * n) := by field_simp; simp
      _ ≤ rexp (-t ^ (-α) / 2) * (↑n.factorial)⁻¹ *
        ((θ α * t) ^ (-(n + 1) : ℝ)) * |x| ^ (2 * n) := by
        field_simp; rw [mul_assoc, mul_comm (|x| ^ (2 * n)), ← mul_assoc, mul_div_assoc,
          mul_comm ((n + 1).factorial : ℝ), div_eq_mul_inv, mul_assoc (b := |x| ^ (2 * n))]
        rw (config := {occs := .neg [0]}) [Real.rpow_neg]
        · gcongr
          · refine mul_nonneg (by positivity) ?_; simp
            exact pow_nonneg (le_of_lt (mul_pos (θpos hα) ht)) (n + 1)
          · exact lem_fac' n
          · norm_cast; exact pow_pos (mul_pos (θpos hα) ht) (n + 1)
          · norm_cast
        · exact le_of_lt (mul_pos (θpos hα) ht)

/-- Calculating the space derivative of `u`. Need to verify locally uniform convergence. -/
theorem deriv2_u_x {x t α : ℝ} (ht : 0 < t) (hα : 1 < α) :
    iteratedDeriv 2 (fun x ↦ u α x t) x =
    ∑' (i : ℕ), iteratedDeriv (i + 1) (g α) t * ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i) := by
  unfold u
  have eq : ∀ i : ℕ, iteratedDeriv (i + 1) (g α) t * (↑(2 * (i + 1)).factorial)⁻¹ *
    (2 * (i + 1) * ((2 * (i + 1) - 1) * x ^ (2 * (i + 1) - 1 - 1))) =
    iteratedDeriv (i + 1) (g α) t * (↑(2 * i).factorial)⁻¹ * x ^ (2 * i) := by
    intro i
    calc
      iteratedDeriv (i + 1) (g α) t * (↑(2 * (i + 1)).factorial)⁻¹ *
        (2 * (i + 1) * ((2 * (i + 1) - 1) * x ^ (2 * (i + 1) - 1 - 1)))
        = iteratedDeriv (i + 1) (g α) t * (↑(2 * (i + 1)).factorial)⁻¹ *
        (2 * (i + 1) * ((2 * i + 1) * x ^ (2 * i))) := by
          simp; apply Or.inl; apply Or.inl; grind
      _ = iteratedDeriv (i + 1) (g α) t * ((↑(2 * (i + 1)).factorial)⁻¹ *
        (2 * (i + 1)) * (2 * i + 1)) * x ^ (2 * i) := by ring
      _ = iteratedDeriv (i + 1) (g α) t * (↑(2 * i).factorial)⁻¹ * x ^ (2 * i) := by
          congr; field_simp; norm_cast
          rw [mul_assoc, ← Nat.factorial_succ]
          have : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
          simp [this, ← Nat.factorial_succ]
  rw [← iteratedDerivWithin_of_isOpen isOpen_univ, iteratedDerivWithin_tsum 2 isOpen_univ]
  · simp [iteratedDerivWithin_univ, iteratedDeriv_eq_iterate (n := 2)]
    rw [← Summable.sum_add_tsum_nat_add' (k := 1)]
    · simp; congr; ext i; exact eq i
    · simp [summable_congr eq (L := SummationFilter.unconditional ℕ)]
      exact summable_u' x ht hα
  · simp
  · intro z hz; exact summable_u z ht hα
  · intro k hk1 hk2
    unfold SummableLocallyUniformlyOn HasSumLocallyUniformlyOn
    simp [iteratedDerivWithin_univ]
    have : k = 1 ∨ k = 2 := by interval_cases k; all_goals simp
    by_cases h1 : k = 1
    · sorry
    · simp_all
      use (fun b => ∑' (i : ℕ), iteratedDeriv (i + 1) (g α) t * ((2 * i).factorial : ℝ)⁻¹
        * b ^ (2 * i))
      refine TendstoLocallyUniformlyOn.congr (F := fun (I : Finset ℕ) (b : ℝ) =>
        ∑ i ∈ I, iteratedDeriv (i + 1) (g α) t * (↑(2 * i).factorial)⁻¹ * b ^ (2 * i)) ?_ ?_
      · simp [tendstoLocallyUniformlyOn_iff_forall_isCompact]
        intro K hK
        obtain ⟨a, ha⟩ := upperboundK hK
        let v : ℕ → ℝ := fun n => rexp (- t ^ (- α) / 2) * (n.factorial : ℝ)⁻¹ *
          (θ α * t) ^ (- (n + 1) : ℝ) * |a| ^ (2 * n)
        refine tendstoUniformlyOn_tsum (u := v) ?_ ?_
        · exact dom_seq' a t α
        · sorry
      · intro I; simp [Set.EqOn]; intro r; congr; ext n
        simp? [iteratedDeriv_eq_iterate]
        sorry
  · intro n k r hk hr
    rw [iteratedDerivWithin_univ]
    fun_prop
  · simp

/-- Showing that `u` is a classical solution to the heat equation. -/
theorem isClassical1DHeatSolution_u {α : ℝ} (hα : 1 < α) :
    IsClassical1DHeatSolution (Set.univ : Set ℝ) (u α) := by
  unfold IsClassical1DHeatSolution
  constructor
  · intro x; sorry
  · constructor
    · intro t ht; sorry
    · intro x hx t ht
      rw [laplacian_eq_iteratedDeriv_real, deriv_u_t ht hα , deriv2_u_x ht hα ]
      ring

#min_imports
