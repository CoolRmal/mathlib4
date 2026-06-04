/-
Copyright (c) 2026 The mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Noncommutative probability spaces

This file contains a small algebraic API for noncommutative probability spaces.  A
noncommutative probability space is a unital algebra equipped with a normalized linear functional,
called its state.  A star-probability space additionally has a star operation compatible with
scalar multiplication via `StarModule`, and asks that the state is nonnegative on elements of the
form `a * star a`.

The definitions are intentionally algebraic: no topology or measure theory is assumed.

## Main definitions

* `ProbabilityTheory.Noncommutative.ProbabilitySpace`: a unital algebra with a normalized state.
* `ProbabilityTheory.Noncommutative.StarProbabilitySpace`: a `StarModule` version with a positive
  state.
* `ProbabilityTheory.Noncommutative.moment`: moments of an element with respect to the state.
* `ProbabilityTheory.Noncommutative.IsCentered`: centered noncommutative random variables.
-/

@[expose] public section

namespace ProbabilityTheory
namespace Noncommutative

universe u v

variable {𝕜 : Type u} {A : Type v}

/-- A noncommutative probability space over `𝕜` is a unital `𝕜`-algebra `A` equipped with a
normalized linear functional `state : A →ₗ[𝕜] 𝕜`.

The elements of `A` play the role of noncommutative random variables, and `state` plays the role of
expectation. -/
structure ProbabilitySpace (𝕜 : Type u) (A : Type v) [CommSemiring 𝕜] [Semiring A]
    [Algebra 𝕜 A] where
  /-- The state, or expectation functional. -/
  state : A →ₗ[𝕜] 𝕜
  /-- The state is normalized on the unit. -/
  state_one : state 1 = 1

namespace ProbabilitySpace

variable [CommSemiring 𝕜] [Semiring A] [Algebra 𝕜 A]

instance instCoeFun : CoeFun (ProbabilitySpace 𝕜 A) (fun _ ↦ A → 𝕜) where
  coe φ := fun a ↦ φ.state a

/-- Elements of the algebra, regarded as noncommutative random variables. -/
abbrev RandomVariable (_φ : ProbabilitySpace 𝕜 A) : Type v := A

/-- Expectation with respect to a noncommutative probability space. -/
def expect (φ : ProbabilitySpace 𝕜 A) (a : A) : 𝕜 :=
  φ a

@[simp]
theorem expect_eq_coe (φ : ProbabilitySpace 𝕜 A) (a : A) : φ.expect a = φ a :=
  rfl

@[simp]
theorem map_one (φ : ProbabilitySpace 𝕜 A) : φ (1 : A) = 1 :=
  φ.state_one

@[simp]
theorem map_zero (φ : ProbabilitySpace 𝕜 A) : φ (0 : A) = 0 :=
  φ.state.map_zero

theorem map_add (φ : ProbabilitySpace 𝕜 A) (a b : A) :
    φ (a + b) = φ a + φ b :=
  φ.state.map_add a b

@[simp]
theorem map_smul (φ : ProbabilitySpace 𝕜 A) (r : 𝕜) (a : A) :
    φ (r • a) = r • φ a :=
  φ.state.map_smul r a

theorem map_sum {ι : Type*} (φ : ProbabilitySpace 𝕜 A) (s : Finset ι) (f : ι → A) :
    φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  simp

end ProbabilitySpace

/-- The `n`th moment of a noncommutative random variable `a`. -/
def moment [CommSemiring 𝕜] [Semiring A] [Algebra 𝕜 A] (φ : ProbabilitySpace 𝕜 A)
    (a : A) (n : ℕ) : 𝕜 :=
  φ (a ^ n)

section ProbabilitySpace

variable [CommSemiring 𝕜] [Semiring A] [Algebra 𝕜 A]
variable (φ : ProbabilitySpace 𝕜 A) (a : A) {n : ℕ}

@[simp]
theorem moment_zero : moment φ a 0 = 1 := by
  simp [moment]

@[simp]
theorem moment_one : moment φ a 1 = φ a := by
  simp [moment]

@[simp]
theorem moment_one_variable (n : ℕ) : moment φ (1 : A) n = 1 := by
  simp [moment]

@[simp]
theorem moment_zero_variable_of_ne_zero (hn : n ≠ 0) : moment φ (0 : A) n = 0 := by
  simp [moment, hn]

/-- A noncommutative random variable is centered if its expectation is zero. -/
def IsCentered (φ : ProbabilitySpace 𝕜 A) (a : A) : Prop :=
  φ a = 0

@[simp]
theorem isCentered_zero : IsCentered φ (0 : A) := by
  simp [IsCentered]

theorem isCentered_iff : IsCentered φ a ↔ φ a = 0 :=
  Iff.rfl

end ProbabilitySpace

/-- A star-probability space is a noncommutative probability space whose algebra is a star algebra
over `𝕜`, with the star compatible with scalar multiplication via `StarModule`, and whose state is
nonnegative on `a * star a`. -/
structure StarProbabilitySpace (𝕜 : Type u) (A : Type v) [CommSemiring 𝕜] [Preorder 𝕜]
    [Star 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] extends
    ProbabilitySpace 𝕜 A where
  /-- Positivity of the state on elements of the form `a * star a`. -/
  map_mul_star_nonneg : ∀ a : A, 0 ≤ state (a * star a)

namespace StarProbabilitySpace

variable [CommSemiring 𝕜] [Preorder 𝕜] [Star 𝕜] [Semiring A] [StarRing A]
    [Algebra 𝕜 A] [StarModule 𝕜 A]

instance instCoe : Coe (StarProbabilitySpace 𝕜 A) (ProbabilitySpace 𝕜 A) where
  coe φ := φ.toProbabilitySpace

instance instCoeFun : CoeFun (StarProbabilitySpace 𝕜 A) (fun _ ↦ A → 𝕜) where
  coe φ := fun a ↦ φ.state a

@[simp]
theorem map_one (φ : StarProbabilitySpace 𝕜 A) : φ (1 : A) = 1 :=
  φ.state_one

@[simp]
theorem map_zero (φ : StarProbabilitySpace 𝕜 A) : φ (0 : A) = 0 :=
  φ.state.map_zero

theorem map_add (φ : StarProbabilitySpace 𝕜 A) (a b : A) :
    φ (a + b) = φ a + φ b :=
  φ.state.map_add a b

@[simp]
theorem map_smul (φ : StarProbabilitySpace 𝕜 A) (r : 𝕜) (a : A) :
    φ (r • a) = r • φ a :=
  φ.state.map_smul r a

/-- Positivity of a state on `a * star a`. -/
theorem mul_star_nonneg (φ : StarProbabilitySpace 𝕜 A) (a : A) :
    0 ≤ φ (a * star a) :=
  φ.map_mul_star_nonneg a

/-- Positivity of a state on `star a * a`, obtained by applying positivity to `star a`. -/
theorem star_mul_nonneg (φ : StarProbabilitySpace 𝕜 A) (a : A) :
    0 ≤ φ (star a * a) := by
  simpa using φ.map_mul_star_nonneg (star a)

/-- Positivity after scalar multiplication, with `StarModule` rewriting the adjoint of `r • a`. -/
theorem smul_mul_star_smul_nonneg (φ : StarProbabilitySpace 𝕜 A) (r : 𝕜) (a : A) :
    0 ≤ φ ((r • a) * (star r • star a)) := by
  simpa using φ.map_mul_star_nonneg (r • a)

end StarProbabilitySpace

end Noncommutative
end ProbabilityTheory
