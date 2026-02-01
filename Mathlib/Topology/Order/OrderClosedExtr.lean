/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.LocalExtr

/-!
# Extrema from monotonicity and antitonicity

In this file we prove a lemma that is useful for the First Derivative Test in calculus,
and its dual.

## Main statements

* `isLocalMax_of_mono_anti` : if a function `f` is monotone to the left of `x`
  and antitone to the right of `x` then `f` has a local maximum at `x`.

* `isLocalMin_of_anti_mono` : the dual statement for minima.

-/

public section

open Set Topology Filter

variable {α β : Type*} [Preorder β] {s : Set α} {a b c : α} {f : α → β}

section PartialOrder

variable [PartialOrder α]

/-- If `b ≤ c`, and `f` is antitone on `[b,c)`, then the maximum of
`f` on `[b, c)` is attained at `b`. -/
lemma isMaxOn_of_anti_Ico (g₁ : b ≤ c) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ico b c) b := by
  rcases g₁.lt_or_eq with (hp | hq) <;> intro
  · aesop
  · simp [show Ico b c = ∅ by rw [Ico_eq_empty_iff]; grind]

/-- If `b ≤ c`, and `f` is monotone on `[b,c)`, then the minimum of
`f` on `[b, c)` is attained at `b`. -/
lemma isMinOn_of_mono_Ico (g₁ : b ≤ c) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ico b c) b :=
  isMaxOn_of_anti_Ico (β := βᵒᵈ) g₁ h₁

/-- If `b ≤ c`, and `f` is antitone on `[b,c]`, then the maximum of
`f` on `[b, c]` is attained at `b`. -/
lemma isMaxOn_of_anti_Icc (g₁ : b ≤ c) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Icc b c) b := by
  rcases g₁.lt_or_eq with (hp | hq) <;> intro
  · aesop
  · simp_all

/-- If `b ≤ c`, and `f` is monotone on `[b,c]`, then the minimum of
`f` on `[b, c]` is attained at `b`. -/
lemma isMinOn_of_mono_Icc (g₁ : b ≤ c) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Icc b c) b :=
  isMaxOn_of_anti_Icc (β := βᵒᵈ) g₁ h₁

end PartialOrder

variable [LinearOrder α]

/-- If `a` is an element of a set `s`, and `f` is monotone on `s ∩ (-∞, a]` and antitone on
`s ∩ [a, ∞)`, then the maximum of `f` on `s` is attained at `a`. -/
lemma isMaxOn_of_mono_anti (ha : a ∈ s) (h₀ : MonotoneOn f (s ∩ Set.Iic a))
    (h₁ : AntitoneOn f (s ∩ Set.Ici a)) : IsMaxOn f s a :=
  fun x _ => by rcases le_total x a <;> aesop

/-- If `a < b < c`, and `f` is monotone on `(a, b]` and antitone on `[b,c)`, then the maximum of
`f` on `(a, c)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ioo (g₀ : a < b) (g₁ : b < c)
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ioo a c) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a ≤ b < c`, and `f` is monotone on `[a, b]` and antitone on `[b,c)`, then the maximum of
`f` on `[a, c)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ico (g₀ : a ≤ b) (g₁ : b < c)
    (h₀ : MonotoneOn f (Icc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ico a c) b :=
  fun x _ => by rcases le_total x b <;> aesop

lemma isMinOn_of_anti_mono
    {α β : Type*} [LinearOrder α] [Preorder β]
    {s : Set α} {a : α} (ha : a ∈ s) {f : α → β}
    (h₀ : AntitoneOn f (s ∩ Set.Iic a))
    (h₁ : MonotoneOn f (s ∩ Set.Ici a)) : IsMinOn f s a :=
  isMaxOn_of_mono_anti (β := βᵒᵈ) ha h₀ h₁

/-- If `f` is monotone on `(a,b]` and antitone on `[b,c)` then `f` has
a local maximum at `b`. -/
lemma isLocalMax_of_mono_anti
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b :=
  isLocalMax_of_mono_anti' (Ioc_mem_nhdsLE g₀) (Ico_mem_nhdsGE g₁) h₀ h₁

/-- If `f` is antitone on `(a,b]` and monotone on `[b,c)` then `f` has
a local minimum at `b`. -/
lemma isLocalMin_of_anti_mono
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b :=
  mem_of_superset (Ioo_mem_nhds g₀ g₁) (fun x hx => by rcases le_total x b <;> aesop)
