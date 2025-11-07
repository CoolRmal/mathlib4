/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Cotlar–Stein lemma

In this file we prove the Cotlar–Stein lemma.

https://www.jstor.org/stable/j.ctt1bpmb3s.12?seq=50


-/

open MeasureTheory InnerProduct ContinuousLinearMap
variable {X E F : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F]
variable {T : X → (E →L[ℝ] F)} {h : X → X → ℝ} {A : ℝ}

theorem CotlarStein (hT : ∀ e, Measurable (fun x => T x e))
    (hxy : ∀ x y, ‖T x ∘L (T y)†‖ ≤ (h x y) ^ 2 ∧ ‖(T x)† ∘L T y‖ ≤ (h x y) ^ 2)
    (hh : ⨆ x, ∫ y, h x y ∂μ ≤ A) (v : E) :
    ‖∫ x, T x v ∂μ‖ ≤ A * ‖v‖ := by sorry

#min_imports
