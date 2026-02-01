/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot, Yongxi Lin
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

variable {α β : Type*} [LinearOrder α] [Preorder β] {s : Set α} {a b c : α} {f : α → β}

/-- If `a` is an element of a set `s`, and `f` is monotone on `s ∩ (-∞, a]` and antitone on
`s ∩ [a, ∞)`, then the maximum of `f` on `s` is attained at `a`. -/
lemma isMaxOn_of_mono_anti (ha : a ∈ s) (h₀ : MonotoneOn f (s ∩ Set.Iic a))
    (h₁ : AntitoneOn f (s ∩ Set.Ici a)) : IsMaxOn f s a :=
  fun x _ => by rcases le_total x a <;> aesop

/-- If `a` is an element of a set `s`, and `f` is antitone on `s ∩ (-∞, a]` and monotone on
`s ∩ [a, ∞)`, then the minimum of `f` on `s` is attained at `a`. -/
lemma isMinOn_of_anti_mono (ha : a ∈ s) (h₀ : AntitoneOn f (s ∩ Set.Iic a))
    (h₁ : MonotoneOn f (s ∩ Set.Ici a)) : IsMinOn f s a :=
  isMaxOn_of_mono_anti (β := βᵒᵈ) ha h₀ h₁

/-- If `a < b < c`, and `f` is monotone on `(a, b]` and antitone on `[b,c)`, then the maximum of
`f` on `(a, c)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ioo (g₀ : a < b) (g₁ : b < c)
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ioo a c) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a < b < c`, and `f` is antitone on `(a, b]` and monotone on `[b,c)`, then the minimum of
`f` on `(a, c)` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Ioo (g₀ : a < b) (g₁ : b < c)
    (h₀ : AntitoneOn f (Ioc a b))
    (h₁ : MonotoneOn f (Ico b c)) : IsMinOn f (Ioo a c) b :=
  isMaxOn_of_mono_anti_Ioo (β := βᵒᵈ) g₀ g₁ h₀ h₁

/-- If `a ≤ b < c`, and `f` is monotone on `[a, b]` and antitone on `[b,c)`, then the maximum of
`f` on `[a, c)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ico (g₀ : a ≤ b) (g₁ : b < c)
    (h₀ : MonotoneOn f (Icc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ico a c) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a ≤ b < c`, and `f` is antitone on `[a, b]` and monotone on `[b,c)`, then the minimum of
`f` on `[a, c)` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Ico (g₀ : a ≤ b) (g₁ : b < c)
    (h₀ : AntitoneOn f (Icc a b))
    (h₁ : MonotoneOn f (Ico b c)) : IsMinOn f (Ico a c) b :=
  isMaxOn_of_mono_anti_Ico (β := βᵒᵈ) g₀ g₁ h₀ h₁

/-- If `a < b ≤ c`, and `f` is monotone on `(a, b]` and antitone on `[b,c]`, then the maximum of
`f` on `(a, c]` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ioc (g₀ : a < b) (g₁ : b ≤ c)
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Icc b c)) : IsMaxOn f (Ioc a c) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a < b ≤ c`, and `f` is monotone on `(a, b]` and antitone on `[b,c]`, then the maximum of
`f` on `(a, c]` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Ioc (g₀ : a < b) (g₁ : b ≤ c)
    (h₀ : AntitoneOn f (Ioc a b))
    (h₁ : MonotoneOn f (Icc b c)) : IsMinOn f (Ioc a c) b :=
  isMaxOn_of_mono_anti_Ioc (β := βᵒᵈ) g₀ g₁ h₀ h₁

/-- If `a ≤ b ≤ c`, and `f` is monotone on `[a, b]` and antitone on `[b,c]`, then the maximum of
`f` on `[a, c]` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Icc (g₀ : a ≤ b) (g₁ : b ≤ c)
    (h₀ : MonotoneOn f (Icc a b))
    (h₁ : AntitoneOn f (Icc b c)) : IsMaxOn f (Icc a c) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a ≤ b ≤ c`, and `f` is antitone on `[a, b]` and monotone on `[b,c]`, then the minimum of
`f` on `(a, c]` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Icc (g₀ : a ≤ b) (g₁ : b ≤ c)
    (h₀ : AntitoneOn f (Icc a b))
    (h₁ : MonotoneOn f (Icc b c)) : IsMinOn f (Icc a c) b :=
  isMaxOn_of_mono_anti_Icc (β := βᵒᵈ) g₀ g₁ h₀ h₁

/-- If `a < b`, and `f` is monotone on `(a, b]` and antitone on `[b,∞)`, then the maximum of
`f` on `(a, ∞)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ioi (g₀ : a < b)
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f (Ioi a) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a < b`, and `f` is antitone on `(a, b]` and monotone on `[b,∞)`, then the minimum of
`f` on `(a, ∞)` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Ioi (g₀ : a < b)
    (h₀ : AntitoneOn f (Ioc a b))
    (h₁ : MonotoneOn f (Ici b)) : IsMinOn f (Ioi a) b :=
  isMaxOn_of_mono_anti_Ioi (β := βᵒᵈ) g₀ h₀ h₁

/-- If `a ≤ b`, and `f` is monotone on `[a, b]` and antitone on `[b,∞)`, then the maximum of
`f` on `[a, ∞)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Ici (g₀ : a ≤ b)
    (h₀ : MonotoneOn f (Icc a b))
    (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f (Ici a) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `a < b`, and `f` is antitone on `(a, b]` and monotone on `[b,∞)`, then the minimum of
`f` on `[a, ∞)` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Ici (g₀ : a ≤ b)
    (h₀ : AntitoneOn f (Icc a b))
    (h₁ : MonotoneOn f (Ici b)) : IsMinOn f (Ici a) b :=
  isMaxOn_of_mono_anti_Ici (β := βᵒᵈ) g₀ h₀ h₁

/-- If `b < a`, and `f` is monotone on `(-∞, b]` and antitone on `[b,a)`, then the maximum of
`f` on `(-∞, a)` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Iio (g₀ : b < a)
    (h₀ : MonotoneOn f (Iic b))
    (h₁ : AntitoneOn f (Ico b a)) : IsMaxOn f (Iio a) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `b < a`, and `f` is antitone on `(-∞, b]` and monotone on `[b,a)`, then the minimum of
`f` on `(-∞, a)` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Iio (g₀ : b < a)
    (h₀ : AntitoneOn f (Iic b))
    (h₁ : MonotoneOn f (Ico b a)) : IsMinOn f (Iio a) b :=
  isMaxOn_of_mono_anti_Iio (β := βᵒᵈ) g₀ h₀ h₁

/-- If `b ≤ a`, and `f` is monotone on `(-∞, b]` and antitone on `[b,a]`, then the maximum of
`f` on `(-∞, a]` is attained at `b`. -/
lemma isMaxOn_of_mono_anti_Iic (g₀ : b ≤ a)
    (h₀ : MonotoneOn f (Iic b))
    (h₁ : AntitoneOn f (Icc b a)) : IsMaxOn f (Iic a) b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `b < a`, and `f` is antitone on `(-∞, b]` and monotone on `[b,a]`, then the minimum of
`f` on `(-∞, a]` is attained at `b`. -/
lemma isMinOn_of_anti_mono_Iic (g₀ : b ≤ a)
    (h₀ : AntitoneOn f (Iic b))
    (h₁ : MonotoneOn f (Icc b a)) : IsMinOn f (Iic a) b :=
  isMaxOn_of_mono_anti_Iic (β := βᵒᵈ) g₀ h₀ h₁

/-- If `f` is monotone on `(-∞, b]` and antitone on `[b,∞)`, then the maximum of `f` is attained
at `b`. -/
lemma isMaxOn_of_mono_anti_univ (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f univ b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `f` is antitone on `(-∞, b]` and monotone on `[b,∞)`, then the minimum of `f` is attained
at `b`. -/
lemma isMinOn_of_anti_mono_univ (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f univ b :=
  isMaxOn_of_mono_anti_univ (β := βᵒᵈ) h₀ h₁

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
