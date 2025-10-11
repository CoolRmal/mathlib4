import Mathlib

noncomputable section
open InnerProductSpace
open scoped Real ContDiff Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A definition of classical solutions to the 1D heat equation. -/
def IsClassical1DHeatSolution (U : Set ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun xt : ℝ × ℝ ↦ u xt.1 xt.2) (U ×ˢ Set.Ioi 0)
    ∧ ∀ x ∈ U, ∀ t, 0 < t → deriv (fun s ↦ u x s) t - Δ (fun y ↦ u y t) x = 0

def φ (α : ℝ) (t : ℝ) := if 0 < t then rexp (- t ^ (- α)) else 0

variable {f : ℂ → ℂ} {z : ℂ} {U : Set ℂ} {n : ℕ} (hf : DifferentiableOn ℂ f U)

theorem citeratedDeriv_eq_iteratedDeriv {r : ℝ} (hr : 0 < r) (hzr : Metric.closedBall z r ⊆ U) :
    iteratedDeriv n f z =
    n.factorial * (2 * π * Complex.I : ℂ)⁻¹ • ∮ w in C(z, r), (z - w)⁻¹ ^ n • (z - w)⁻¹ • f z := by
  unfold iteratedDeriv
  sorry

lemma smooth_φ (α : ℝ) : ContDiffOn ℝ ∞ (φ α) (Set.Ioi 0) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  sorry

/-- Tychonov's counterexample. -/
def u α x t := ∑' (i : ℕ), iteratedDeriv i (φ α) t * ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i)


lemma lem_fac (i : ℕ) : ((i + 1).factorial) * ((2 * i).factorial : ℝ)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := by
  sorry

def θ (α : ℝ) : ℝ := 2 ^ α⁻¹ - 1

lemma dom_seq (x t α : ℝ) : (∀ ψ : ℝ, (1 + θ α * cexp (Complex.I * ψ)).re ^ (- α) > 1 / 2) ∧
    (Summable fun (i : ℕ) => rexp (- t ^ (- α) / 2) * (i.factorial : ℝ)⁻¹ *
     ((θ α) * t) ^ (- (i + 1) : ℝ) * |x| ^ (2 * i)) := by
  sorry

lemma φ_estimate (α t : ℝ) (i : ℕ) :
    |iteratedDeriv i (φ α) t| ≤ rexp (- t ^ (- α) / 2) * ((θ α) * t) ^ (- i : ℝ)
    * (i.factorial : ℝ) := by
  sorry

lemma deriv_u_t {x t α : ℝ} (ht : 0 < t) :
    deriv (fun t ↦ u α x t) t = ∑' (i : ℕ), iteratedDeriv (i + 1) (φ α) t *
    ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i) := by
  unfold u
  sorry

lemma deriv_u_x {x t α : ℝ} (ht : 0 < t) :
    deriv (fun x ↦ u α x t) x = ∑' (i : ℕ), iteratedDeriv (i + 1) (@φ α) t *
    ((2 * i + 1).factorial : ℝ)⁻¹ * x ^ (2 * i + 1) := by
  unfold u
  sorry

lemma deriv2_u_x {x t α : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (fun x ↦ u α x t) x =
    ∑' (i : ℕ), iteratedDeriv (i + 1) (φ α) t * ((2 * i).factorial : ℝ)⁻¹ * x ^ (2 * i) := by
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
