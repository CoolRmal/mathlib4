/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.ModelTheory.Types

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

variable (L : Language.{u, v}) {T : L.Theory} {n : ℕ}
variable (M : Type w) [L.Structure M] (N : Type w') [L.Structure N]

def IsPartialElementaryMap {B : Set M} (f : B → N) : Prop :=
    ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → B), (φ.Realize (f ∘ x) ↔ φ.Realize (Subtype.val ∘ x))

lemma extendPartial {B : Set M} {f : B → N} (hf : IsPartialElementaryMap L M N f) (m : M) :
    ∃ (N' : Type (max (max (max u w) w') v)) (hN' : L.Structure N') (i : N ↪ₑ[L] N')
      (g : ↑(B ∪ {m}) → N'), IsPartialElementaryMap L M N' g ∧
      ∀ b : B, i (f b) = g ⟨b, Or.inl b.2⟩ := by
  by_cases hm : m ∈ B
  · -- Equiv.inducedStructureEquiv
    sorry
  · let S := ↑({m} : Set M)
    let LmN := ((L.lhomWithConstants S).addConstants N).comp (L.lhomWithConstants N)
    let Γ := (L[[S]].lhomWithConstantsMap f).onTheory (L[[S]][[B]].completeTheory M) ∪
      ((L.lhomWithConstants S).addConstants N).onTheory (L.elementaryDiagram N)
    suffices hΓ : IsSatisfiable Γ from by
      obtain N' := Classical.choice hΓ
      let LSN' := (((L.lhomWithConstants S).addConstants N).comp
        (L.lhomWithConstants N)).reduct N'
      let := ((L.lhomWithConstants S).addConstants N).reduct N'
      have : N' ⊨ L.elementaryDiagram N := (ModelType.subtheoryModel N'
        Set.subset_union_right).reduct.is_model
      let e := ElementaryEmbedding.ofModelsElementaryDiagram L N N'
      let LSB := (L[[S]].lhomWithConstantsMap f).reduct N'
      have : N' ⊨ (L[[↑S]][[↑B]].completeTheory M) := (ModelType.subtheoryModel N'
        Set.subset_union_left).reduct.is_model
      let c := LSB.funMap ((L[[S]].lhomWithConstants B).onFunction (L.con
        (⟨m, Set.mem_singleton_iff.mpr rfl⟩ : S))) fun x => nomatch x
      classical
      let g : ↑(B ∪ {m}) → N' := fun a => if h : a.1 ∈ B then e (f ⟨a.1, h⟩) else c
      refine ⟨N', LSN', e, ⟨g, fun n φ x => ⟨fun p => ?_, fun q => ?_⟩, by grind⟩⟩
      · sorry
      · sorry
    refine isSatisfiable_iff_isFinitelySatisfiable.mpr fun T0 hT0 => Nonempty.intro ?_
    have : L[[S]][[N]].Structure N := sorry
    have : N ⊨ SetLike.coe T0 := by sorry
    have : Nonempty N := by sorry
    sorry

theorem automorphism [Nonempty M] {n : ℕ} (a c : Fin n → M) (B : Set M)
    (hab : typeOf (L[[B]].completeTheory M) a = typeOf (L[[B]].completeTheory M) c) :
    ∃ (M' : Bundled L.Structure) (σ : M' ≃[L] M') (i : M ↪ₑ[L] M'),
    ∀ b ∈ B, σ (i b) = i b ∧ σ ∘ (i ∘ a) = (i ∘ c) := by sorry

end Language

end FirstOrder

#min_imports
