/-
Copyright (c) 2026 The mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Probability.Noncommutative.Basic

/-!
# Semicircular moments in noncommutative probability

This file provides a compact API for semicircular distributions in the algebraic,
noncommutative-probability sense.  The moment convention follows the semicircle-distribution
development in `FredRaj3/SemicircleLaw`: odd centered moments vanish, and the even moments are
given by Catalan numbers.

For a variance parameter `v`, the `2 * n`th moment is `v ^ n * catalan n`, and the
`2 * n + 1`st moment is zero.

## Main definitions

* `ProbabilityTheory.Noncommutative.semicircularMoment`: the Catalan moment sequence with variance
  parameter `v`.
* `ProbabilityTheory.Noncommutative.HasSemicircularMoments`: an element has the semicircular moment
  sequence.
* `ProbabilityTheory.Noncommutative.IsSemicircular`: the standard variance-one specialization.
* `ProbabilityTheory.Noncommutative.HasSelfAdjointSemicircularDistribution`: the star-probability
  version, requiring self-adjointness as well as the semicircular moments.
-/

@[expose] public section

namespace ProbabilityTheory
namespace Noncommutative

universe u v

variable {𝕜 : Type u} {A : Type v}

/-- The centered semicircular moment sequence with variance `variance`.

Odd moments are zero.  The moment of order `2 * n` is
`variance ^ n * catalan n`. -/
def semicircularMoment {𝕜 : Type u} [Semiring 𝕜] (variance : 𝕜) (n : ℕ) : 𝕜 :=
  if Even n then variance ^ (n / 2) * (catalan (n / 2) : 𝕜) else 0

section SemicircularMoment

variable [Semiring 𝕜] (variance : 𝕜) {n : ℕ}

theorem semicircularMoment_of_even (hn : Even n) :
    semicircularMoment variance n = variance ^ (n / 2) * (catalan (n / 2) : 𝕜) := by
  simp [semicircularMoment, hn]

@[simp]
theorem semicircularMoment_of_not_even (hn : ¬ Even n) :
    semicircularMoment variance n = 0 := by
  simp [semicircularMoment, hn]

@[simp]
theorem semicircularMoment_zero : semicircularMoment variance 0 = 1 := by
  simp [semicircularMoment]

@[simp]
theorem semicircularMoment_two_mul (n : ℕ) :
    semicircularMoment variance (2 * n) = variance ^ n * (catalan n : 𝕜) := by
  have hdiv : (2 * n) / 2 = n := by
    exact Nat.mul_div_right n (by decide : 0 < 2)
  simp [semicircularMoment, hdiv]

@[simp]
theorem semicircularMoment_two_mul_add_one (n : ℕ) :
    semicircularMoment variance (2 * n + 1) = 0 := by
  simp [semicircularMoment]

@[simp]
theorem semicircularMoment_one : semicircularMoment variance 1 = 0 := by
  simp [semicircularMoment]

@[simp]
theorem semicircularMoment_two : semicircularMoment variance 2 = variance := by
  simpa using semicircularMoment_two_mul variance 1

theorem semicircularMoment_four : semicircularMoment variance 4 = variance ^ 2 * (2 : 𝕜) := by
  simpa [catalan_two] using semicircularMoment_two_mul variance 2

end SemicircularMoment

/-- The standard centered semicircular moment sequence, with variance one. -/
def standardSemicircularMoment (𝕜 : Type u) [Semiring 𝕜] (n : ℕ) : 𝕜 :=
  semicircularMoment (1 : 𝕜) n

section StandardSemicircularMoment

variable [Semiring 𝕜]

@[simp]
theorem standardSemicircularMoment_zero : standardSemicircularMoment 𝕜 0 = 1 := by
  simp [standardSemicircularMoment]

@[simp]
theorem standardSemicircularMoment_two_mul (n : ℕ) :
    standardSemicircularMoment 𝕜 (2 * n) = (catalan n : 𝕜) := by
  simp [standardSemicircularMoment]

@[simp]
theorem standardSemicircularMoment_two_mul_add_one (n : ℕ) :
    standardSemicircularMoment 𝕜 (2 * n + 1) = 0 := by
  simp [standardSemicircularMoment]

end StandardSemicircularMoment

section ProbabilitySpace

variable [CommSemiring 𝕜] [Semiring A] [Algebra 𝕜 A]

/-- An element has centered semicircular moments with variance `variance`. -/
def HasSemicircularMoments (φ : ProbabilitySpace 𝕜 A) (a : A) (variance : 𝕜) : Prop :=
  ∀ n : ℕ, moment φ a n = semicircularMoment variance n

/-- An element is standard semicircular if its moments are the variance-one semicircular moments. -/
def IsSemicircular (φ : ProbabilitySpace 𝕜 A) (a : A) : Prop :=
  HasSemicircularMoments φ a 1

namespace HasSemicircularMoments

variable {φ : ProbabilitySpace 𝕜 A} {a : A} {variance : 𝕜}

theorem moment_eq (h : HasSemicircularMoments φ a variance) (n : ℕ) :
    moment φ a n = semicircularMoment variance n :=
  h n

theorem even_moment (h : HasSemicircularMoments φ a variance) (n : ℕ) :
    moment φ a (2 * n) = variance ^ n * (catalan n : 𝕜) := by
  rw [moment_eq h, semicircularMoment_two_mul]

theorem odd_moment (h : HasSemicircularMoments φ a variance) (n : ℕ) :
    moment φ a (2 * n + 1) = 0 := by
  rw [moment_eq h, semicircularMoment_two_mul_add_one]

theorem expectation_eq_zero (h : HasSemicircularMoments φ a variance) : φ a = 0 := by
  simpa using odd_moment h 0

theorem second_moment (h : HasSemicircularMoments φ a variance) : moment φ a 2 = variance := by
  simpa using even_moment h 1

theorem fourth_moment (h : HasSemicircularMoments φ a variance) :
    moment φ a 4 = variance ^ 2 * (2 : 𝕜) := by
  simpa [catalan_two] using even_moment h 2

end HasSemicircularMoments

namespace IsSemicircular

variable {φ : ProbabilitySpace 𝕜 A} {a : A}

theorem hasSemicircularMoments (h : IsSemicircular φ a) : HasSemicircularMoments φ a 1 :=
  h

theorem moment_eq (h : IsSemicircular φ a) (n : ℕ) :
    moment φ a n = standardSemicircularMoment 𝕜 n := by
  change moment φ a n = semicircularMoment (1 : 𝕜) n
  exact HasSemicircularMoments.moment_eq (hasSemicircularMoments h) n

theorem even_moment (h : IsSemicircular φ a) (n : ℕ) :
    moment φ a (2 * n) = (catalan n : 𝕜) := by
  simpa using HasSemicircularMoments.even_moment (hasSemicircularMoments h) n

theorem odd_moment (h : IsSemicircular φ a) (n : ℕ) : moment φ a (2 * n + 1) = 0 :=
  HasSemicircularMoments.odd_moment (hasSemicircularMoments h) n

theorem expectation_eq_zero (h : IsSemicircular φ a) : φ a = 0 :=
  HasSemicircularMoments.expectation_eq_zero (hasSemicircularMoments h)

theorem second_moment (h : IsSemicircular φ a) : moment φ a 2 = 1 := by
  simpa using HasSemicircularMoments.second_moment (hasSemicircularMoments h)

theorem fourth_moment (h : IsSemicircular φ a) : moment φ a 4 = 2 := by
  simpa using HasSemicircularMoments.fourth_moment (hasSemicircularMoments h)

end IsSemicircular

end ProbabilitySpace

section StarProbabilitySpace

variable [CommSemiring 𝕜] [Preorder 𝕜] [Star 𝕜] [Semiring A] [StarRing A]
    [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- A self-adjoint semicircular element in a star-probability space. -/
def HasSelfAdjointSemicircularDistribution (φ : StarProbabilitySpace 𝕜 A) (a : A)
    (variance : 𝕜) : Prop :=
  IsSelfAdjoint a ∧ HasSemicircularMoments φ.toProbabilitySpace a variance

namespace HasSelfAdjointSemicircularDistribution

variable {φ : StarProbabilitySpace 𝕜 A} {a : A} {variance : 𝕜}

theorem isSelfAdjoint (h : HasSelfAdjointSemicircularDistribution φ a variance) :
    IsSelfAdjoint a :=
  h.1

theorem hasSemicircularMoments (h : HasSelfAdjointSemicircularDistribution φ a variance) :
    HasSemicircularMoments φ.toProbabilitySpace a variance :=
  h.2

theorem even_moment (h : HasSelfAdjointSemicircularDistribution φ a variance) (n : ℕ) :
    moment φ.toProbabilitySpace a (2 * n) = variance ^ n * (catalan n : 𝕜) :=
  HasSemicircularMoments.even_moment (hasSemicircularMoments h) n

theorem odd_moment (h : HasSelfAdjointSemicircularDistribution φ a variance) (n : ℕ) :
    moment φ.toProbabilitySpace a (2 * n + 1) = 0 :=
  HasSemicircularMoments.odd_moment (hasSemicircularMoments h) n

theorem expectation_eq_zero (h : HasSelfAdjointSemicircularDistribution φ a variance) :
    φ a = 0 := by
  simpa using HasSemicircularMoments.expectation_eq_zero (hasSemicircularMoments h)

/-- Positivity of the square of a self-adjoint semicircular element. -/
theorem square_nonneg (h : HasSelfAdjointSemicircularDistribution φ a variance) :
    0 ≤ φ (a * a) := by
  have ha : star a = a := isSelfAdjoint h
  simpa [ha] using φ.mul_star_nonneg a

end HasSelfAdjointSemicircularDistribution

end StarProbabilitySpace

end Noncommutative
end ProbabilityTheory
