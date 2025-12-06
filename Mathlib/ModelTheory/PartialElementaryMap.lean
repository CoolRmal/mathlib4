/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.ModelTheory.Substructures
public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Types
public import Mathlib.ModelTheory.Bundled

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions

- A `FirstOrder.Language.PartialElementaryMap` is an embedding that commutes with the
  realizations of formulas.

## Main Results

-

-/

@[expose] public section


universe u v w w'

open FirstOrder

namespace FirstOrder

namespace Language

open Structure Theory CategoryTheory

variable (L : Language.{u, v}) {T : L.Theory} {α : Type w} {n : ℕ}
variable (M : Type w) [L.Structure M] (N : Type w) [L.Structure N]

def IsPartialElementaryMap (B : Set M) (f : M → N) : Prop :=
    ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → M), (∀ i, x i ∈ B) →
      (φ.Realize (f ∘ x) ↔ φ.Realize x)

/-- An elementary embedding is also a partial elementary map defined on the entire set. -/
def toPartialElementaryMap (f : M ↪ₑ[L] N) : IsPartialElementaryMap L M N (Set.univ : Set M) f :=
  fun _ φ x _ => f.map_formula' φ x

lemma extendPartial {B : Set M} {f : M → N} (hf : IsPartialElementaryMap L M N B f) (m : M) :
    ∃ (N' : Bundled L.Structure) (i : N ↪ₑ[L] N') (g : M → N'),
      IsPartialElementaryMap L M N' (B ∪ {m}) g ∧ ∀ b ∈ B, i (f b) = g b := by
  by_cases hm : m ∈ B
  · use Bundled.of N, by rfl, f
    simpa [Bundled.of, Set.union_singleton, Set.insert_eq_of_mem hm]
  · sorry

theorem automorphism [Nonempty M] {n : ℕ} (a c : Fin n → M) (B : Set M)
    (hab : typeOf (L[[B]].completeTheory M) a = typeOf (L[[B]].completeTheory M) c) :
    ∃ (M' : Bundled L.Structure) (σ : M' ≃[L] M') (i : M ↪ₑ[L] M'),
    ∀ b ∈ B, σ (i b) = i b ∧ σ ∘ (i ∘ a) = (i ∘ c) := by sorry

end Language

end FirstOrder

#min_imports
