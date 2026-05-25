/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

module

public import Mathlib.Probability.Kernel.Defs

/-!
# Statistical Inference

-/

@[expose] public section

open MeasureTheory

structure InferenceModel (ι : Type*) (θ Ω S X : ι → Type) [∀ i, MeasurableSpace (θ i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)] where
    domain
    statFunctional (i : ι) :
