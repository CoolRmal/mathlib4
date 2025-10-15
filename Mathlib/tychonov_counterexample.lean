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
-/

noncomputable section
open InnerProductSpace Metric Complex ContDiff
open scoped Real NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A definition of classical solutions to the 1D heat equation. -/
def IsClassical1DHeatSolution (U : Set ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun xt : ℝ × ℝ ↦ u xt.1 xt.2) (U ×ˢ Set.Ioi 0)
    ∧ ∀ x ∈ U, ∀ t, 0 < t → deriv (fun s ↦ u x s) t - Δ (fun y ↦ u y t) x = 0

/-- An auxillary function. -/
def g (α : ℝ) (t : ℝ) := if 0 < t then rexp (- t ^ (- α)) else 0

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

/-- An auxillary constant. -/
def θ (α : ℝ) : ℝ := (2 * Real.cos 1) ^ (1 / α) - 1

/-- Complex Version of `g`. -/
def cg (α : ℝ) (z : ℂ) := cexp (- z ^ (- α : ℂ))

/-- `cg = g` for positive real numbers. -/
lemma cg_eq_g {α t : ℝ} (ht : 0 < t) : cg α (t : ℂ) = g α t := by
  simp [cg, g, ht, ofReal_cpow (le_of_lt ht)]

lemma cgnDiff {α t : ℝ} (ht : 0 < t) (n : ℕ) : ∃ g' : ℂ,
    HasDerivAt (iteratedDeriv n (cg α)) g' (t : ℂ) := by sorry

/-- If `cg` is differentiable, then `g` is differentiable. -/
lemma cg_iff_ghasiteratedDeriv {α t : ℝ} (ht : 0 < t) (n : ℕ) (g' : ℂ) :
    HasDerivAt (iteratedDeriv n (cg α)) g' (t : ℂ) →
    HasDerivAt (iteratedDeriv n (fun y => (g α y : ℂ))) g' t := by sorry

/-- `iteratedDeriv n cg = iteratedDeriv n g` for positive real numbers. -/
lemma iteratedDeriv_cg_eq_iteratedDeriv_g {α t : ℝ} (ht : 0 < t) (n : ℕ) :
    iteratedDeriv n (cg α) (t : ℂ) = iteratedDeriv n (g α) t := by
  induction n with
  | zero => simp [iteratedDeriv_zero, cg_eq_g ht]
  | succ n ih =>
    obtain ⟨g', hg'⟩ := cgnDiff ht n
    rw [iteratedDeriv_succ, iteratedDeriv_succ, HasDerivAt.deriv hg']
    sorry

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

/-- `cg` is differenitable on a ball and continuous on its closure. -/
lemma cgDiffContOnCl {α t : ℝ} (ht : 0 < t) (hα : 1 < α) :
    DiffContOnCl ℂ (cg α) (ball (t : ℂ) ((θ α) * t)) := by
  let g : ℂ → ℂ := fun z => z ^ (- α : ℂ)
  let h : ℂ → ℂ := fun z => -z
  have : cg α = cexp ∘ h ∘ g := by ext x; simp [cg, g, h]
  rw [this]
  constructor
  · intro x hx
    have pg: DifferentiableWithinAt ℂ g (ball (t : ℂ) ((θ α) * t)) t := by
      sorry
    have ph : DifferentiableWithinAt ℂ h Set.univ t := by
      sorry
    refine DifferentiableWithinAt.comp (t := Set.univ) x ?_ ?_ ?_
    · sorry
    · refine DifferentiableWithinAt.comp (t := Set.univ) x ?_ ?_ ?_
      · fun_prop
      · refine DifferentiableWithinAt.cpow_const ?_ ?_
        · fun_prop
        · simp [slitPlane]
          apply Or.inl
          have : x = x - t + t := by simp
          rw [this, add_re, ofReal_re]
          apply lt_add_of_neg_add_lt
          simp only [add_zero]
          suffices |-(x - ↑t).re| < t from (abs_lt.1 this).2
          simp only [abs_neg]
          simp [Complex.dist_eq] at hx
          refine lt_of_le_of_lt (abs_re_le_norm (x - t)) (LT.lt.trans hx ?_)
          rw (config := {occs := .neg [1]}) [← one_mul t]
          exact mul_lt_mul_of_pos_right (θle1 hα) ht
      · intro x hx; simp
    · sorry
  · sorry

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

lemma CauchyEstimate_of_g {α t : ℝ} (hα : 1 < α) (ht : 0 < t) (n : ℕ) :
    |iteratedDeriv n (g α) t| ≤ n.factorial * rexp (- t ^ (- α) / 2) / (θ α * t) ^ n := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← iteratedDeriv_cg_eq_iteratedDeriv_g (α := α) ht n]
  exact norm_iteratedDeriv_le_aux (mul_pos (θpos hα) ht) (cgDiffContOnCl ht hα)
    (estimate_on_sphere_of_g hα ht)

lemma smooth_φ (α : ℝ) : ContDiffOn ℝ ∞ (g α) (Set.Ioi 0) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  sorry

/-- Tychonov's counterexample. -/
def u α x t := ∑' (i : ℕ), iteratedDeriv i (g α) t * ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i)

lemma lem_fac (i : ℕ) : (i.factorial) * ((2 * i).factorial : ℝ)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := by
  sorry

lemma dom_seq (x t α : ℝ) : (∀ ψ : ℝ, (1 + θ α * cexp (Complex.I * ψ)).re ^ (- α) > 1 / 2) ∧
    (Summable fun (i : ℕ) => rexp (- t ^ (- α) / 2) * (i.factorial : ℝ)⁻¹ *
     ((θ α) * t) ^ (- (i + 1) : ℝ) * |x| ^ (2 * i)) := by
  sorry

lemma φ_estimate (α t : ℝ) (i : ℕ) :
    |iteratedDeriv i (g α) t| ≤ rexp (- t ^ (- α) / 2) * ((θ α) * t) ^ (- i : ℝ)
    * (i.factorial : ℝ) := by
  sorry

lemma deriv_u_t {x t α : ℝ} (ht : 0 < t) :
    deriv (fun t ↦ u α x t) t = ∑' (i : ℕ), iteratedDeriv (i + 1) (g α) t *
    ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i) := by
  unfold u
  sorry

lemma deriv_u_x {x t α : ℝ} (ht : 0 < t) :
    deriv (fun x ↦ u α x t) x = ∑' (i : ℕ), iteratedDeriv (i + 1) (g α) t *
    ((2 * i + 1).factorial : ℝ)⁻¹ * x ^ (2 * i + 1) := by
  unfold u
  sorry

lemma deriv2_u_x {x t α : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (fun x ↦ u α x t) x =
    ∑' (i : ℕ), iteratedDeriv (i + 1) (g α) t * ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i) := by
  sorry

lemma condDiff_two_u {α : ℝ} :
    ContDiffOn ℝ 2 (fun xt : ℝ × ℝ ↦ @u α xt.1 xt.2) (Set.univ ×ˢ Set.Ioi 0) := by
  simp_rw [u]
  rintro ⟨x, t⟩ ht
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at ht
  sorry

theorem isClassical1DHeatSolution_u {α : ℝ} :
    IsClassical1DHeatSolution (Set.univ : Set ℝ) (u α) := by
  constructor
  · exact condDiff_two_u
  · intros x hx t ht
    rw [laplacian_eq_iteratedDeriv_real, deriv2_u_x ht, deriv_u_t ht]
    simp

#min_imports
