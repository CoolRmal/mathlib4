/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Topology.DiscreteFamily

/-!
# Strong measurability for inner regular measures

This file proves that measurable maps into pseudometrizable Borel spaces have an almost everywhere
separable range under the uncountable disjoint-union property. This is the topological reduction in
the proof that almost everywhere measurability and almost everywhere strong measurability agree for
finite inner regular measures.
-/

@[expose] public section

open Filter Function Set TopologicalSpace

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
  [PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}

omit [PseudoMetrizableSpace Y] in
private theorem measure_preimage_iUnion_null_of_discreteFamily_aux [SFinite μ]
    (hf : Measurable f) {b : Set (Set Y)} (hb_open : ∀ U ∈ b, IsOpen U)
    (hb_discrete : DiscreteFamily ((↑) : b → Set Y))
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    μ (f ⁻¹' ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y)) = 0 := by
  classical
  let q : Set (Set Y) := {U | U ∈ b ∧ μ (f ⁻¹' U) = 0}
  let A : Set Y → Set X := fun U ↦ if U ∈ q then f ⁻¹' U else ∅
  have hA_disj : Pairwise (Disjoint on A) := by
    intro U V hUV
    change Disjoint (A U) (A V)
    by_cases hU : U ∈ q
    · by_cases hV : V ∈ q
      · rw [show A U = f ⁻¹' U by simp [A, hU], show A V = f ⁻¹' V by simp [A, hV]]
        apply Disjoint.preimage f
        have hne : (⟨U, hU.1⟩ : b) ≠ ⟨V, hV.1⟩ := by
          intro h
          exact hUV (congrArg Subtype.val h)
        exact hb_discrete.pairwiseDisjoint hne
      · simp [A, hV]
    · simp [A, hU]
  have hA_null (U : Set Y) : μ (A U) = 0 := by
    by_cases hU : U ∈ q
    · simpa [A, hU] using hU.2
    · simp [A, hU]
  have hA_union (I : Set (Set Y)) : MeasurableSet (⋃ U ∈ I, A U) := by
    have hopen (U : Set Y) : IsOpen (if U ∈ q then U else ∅) := by
      by_cases hU : U ∈ q
      · simpa [hU] using hb_open U hU.1
      · simp [hU]
    rw [show (⋃ U ∈ I, A U) = f ⁻¹' ⋃ U ∈ I, if U ∈ q then U else ∅ by
      ext x
      simp [A]]
    exact hf (isOpen_iUnion fun U ↦ isOpen_iUnion fun _ ↦ hopen U).measurableSet
  rw [show f ⁻¹' ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y) =
      ⋃ U, A U by
    ext x
    constructor
    · intro hx
      change f x ∈ ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y) at hx
      obtain ⟨U, hxU⟩ := mem_iUnion.1 hx
      apply mem_iUnion.2
      refine ⟨(U : Set Y), ?_⟩
      have hUq : (U : Set Y) ∈ q := ⟨U.1.2, U.2⟩
      simpa [A, hUq] using hxU
    · intro hx
      obtain ⟨U, hxU⟩ := mem_iUnion.1 hx
      by_cases hU : U ∈ q
      · change f x ∈ ⋃ U : {U : b | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y)
        exact mem_iUnion_of_mem ⟨⟨U, hU.1⟩, hU.2⟩ (by simpa [A, hU] using hxU)
      · exfalso
        simp [A, hU] at hxU]
  exact hnull A hA_disj hA_null hA_union

omit [PseudoMetrizableSpace Y] in
private theorem countable_setOf_pos_preimage_of_sigmaDiscreteFamily_aux [SFinite μ]
    (hf : Measurable f) (b : ℕ → Set (Set Y))
    (hb_open : ∀ {n : ℕ} (U : b n), IsOpen (U : Set Y))
    (hb_discrete : ∀ n, DiscreteFamily ((↑) : b n → Set Y)) :
    {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)}.Countable := by
  have hn_count (n : ℕ) : Set.Countable {U : b n | 0 < μ (f ⁻¹' (U : Set Y))} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun U ↦ hf (hb_open U).measurableSet)
      (fun U V hUV ↦ Disjoint.preimage f ((hb_discrete n).pairwiseDisjoint hUV))
  rw [show {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)} =
      ⋃ n, ((↑) : b n → Set Y) '' {U | 0 < μ (f ⁻¹' (U : Set Y))} by
    ext U
    simp only [mem_setOf_eq, mem_iUnion, mem_image, Subtype.exists, exists_and_left]
    aesop]
  exact countable_iUnion fun n ↦ (hn_count n).image _

omit [TopologicalSpace Y] [PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
private theorem countable_induced_basis_compl_aux (b : ℕ → Set (Set Y)) (N : Set Y)
    (hp_count : {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)}.Countable)
    (hnull_sub : ∀ n U, U ∈ b n → μ (f ⁻¹' U) = 0 → U ⊆ N) :
    (((preimage ((↑) : ↑(Nᶜ) → Y)) '' (⋃ n, b n)) : Set (Set ↑(Nᶜ))).Countable := by
  refine ((hp_count.image (preimage ((↑) : ↑(Nᶜ) → Y))).union
    (countable_singleton (∅ : Set ↑(Nᶜ)))).mono ?_
  rintro V ⟨U, hUb, rfl⟩
  obtain ⟨n, hUn⟩ := mem_iUnion.1 hUb
  by_cases hU_pos : 0 < μ (f ⁻¹' U)
  · exact Or.inl ⟨U, ⟨n, hUn, hU_pos⟩, rfl⟩
  · right
    rw [mem_singleton_iff]
    ext y
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun hyU ↦ y.2 (hnull_sub n U hUn (nonpos_iff_eq_zero.1 (not_lt.1 hU_pos)) hyU)

/-- A measurable map into a pseudometrizable Borel space has an almost everywhere closed separable
range, provided that arbitrary measurable unions of a disjoint family of null sets are null.

This isolates the topological part of the Kupka--Prikry theorem from its measure-theoretic core. -/
theorem Measurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null [SFinite μ]
    (hf : Measurable f)
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    ∃ s : Set Y, IsClosed s ∧ IsSeparable s ∧ ∀ᵐ x ∂μ, f x ∈ s := by
  classical
  obtain ⟨b, hb, hdisc⟩ := exists_isTopologicalBasis_sigmaDiscrete (X := Y)
  let z : ℕ → Set Y := fun n ↦
    ⋃ U : {U : b n | μ (f ⁻¹' (U : Set Y)) = 0}, (U : Set Y)
  have hb_open {n : ℕ} (U : b n) : IsOpen (U : Set Y) :=
    hb.isOpen (mem_iUnion.2 ⟨n, U.2⟩)
  have hz_open (n : ℕ) : IsOpen (z n) := isOpen_iUnion fun U ↦ hb_open U.1
  have hz_null (n : ℕ) : μ (f ⁻¹' z n) = 0 := by
    simpa only [z] using measure_preimage_iUnion_null_of_discreteFamily_aux hf
      (fun U hU ↦ hb_open ⟨U, hU⟩) (hdisc n) hnull
  let N : Set Y := ⋃ n, z n
  have hN_open : IsOpen N := isOpen_iUnion hz_open
  have hN_null : μ (f ⁻¹' N) = 0 := by
    simpa only [N, preimage_iUnion] using measure_iUnion_null hz_null
  let p : Set (Set Y) :=
    {U | ∃ n, U ∈ b n ∧ 0 < μ (f ⁻¹' U)}
  have hp_count : p.Countable := by
    simpa only [p] using
      countable_setOf_pos_preimage_of_sigmaDiscreteFamily_aux hf b hb_open hdisc
  let Z : Set Y := Nᶜ
  have hZ_closed : IsClosed Z := hN_open.isClosed_compl
  have hZ_ae : ∀ᵐ x ∂μ, f x ∈ Z := by
    apply ae_iff.2
    change μ (f ⁻¹' Zᶜ) = 0
    simpa only [Z, compl_compl] using hN_null
  have hZ_basis : IsTopologicalBasis
      ((preimage ((↑) : Z → Y)) '' (⋃ n, b n)) := hb.induced _
  have hnull_sub (n : ℕ) (U : Set Y) (hUn : U ∈ b n) (hUnull : μ (f ⁻¹' U) = 0) :
      U ⊆ N := fun y hyU ↦ by
    apply mem_iUnion.2
    refine ⟨n, mem_iUnion.2 ?_⟩
    exact ⟨⟨⟨U, hUn⟩, hUnull⟩, hyU⟩
  have hZ_basis_count :
      (((preimage ((↑) : Z → Y)) '' (⋃ n, b n)) : Set (Set Z)).Countable :=
    countable_induced_basis_compl_aux b N hp_count hnull_sub
  letI : SecondCountableTopology Z := hZ_basis.secondCountableTopology hZ_basis_count
  exact ⟨Z, hZ_closed, IsSeparable.of_subtype Z, hZ_ae⟩

/-- An almost everywhere measurable map into a pseudometrizable Borel space has an almost
everywhere closed separable range, provided that arbitrary measurable unions of a disjoint family
of null sets are null. -/
theorem AEMeasurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null [SFinite μ]
    (hf : AEMeasurable f μ)
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    ∃ s : Set Y, IsClosed s ∧ IsSeparable s ∧ ∀ᵐ x ∂μ, f x ∈ s := by
  obtain ⟨s, hs_closed, hs_sep, hs⟩ :=
    Measurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null hf.measurable_mk hnull
  refine ⟨s, hs_closed, hs_sep, ?_⟩
  filter_upwards [hf.ae_eq_mk, hs] with x hfx hx
  rwa [hfx]

/-- Under the uncountable null-union property, almost everywhere measurable maps into a
pseudometrizable Borel space are almost everywhere strongly measurable. -/
theorem AEMeasurable.aestronglyMeasurable_of_iUnion_null [SFinite μ]
    (hf : AEMeasurable f μ)
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    AEStronglyMeasurable f μ := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨hf, ?_⟩
  obtain ⟨s, -, hs, hfs⟩ :=
    AEMeasurable.exists_isClosed_isSeparable_ae_mem_of_iUnion_null hf hnull
  exact ⟨s, hs, hfs⟩

/-- Under the uncountable null-union property, almost everywhere strong measurability is
equivalent to almost everywhere measurability for maps into pseudometrizable Borel spaces. -/
theorem aestronglyMeasurable_iff_aemeasurable_of_iUnion_null [SFinite μ]
    (hnull : ∀ (s : Set Y → Set X), Pairwise (Disjoint on s) →
      (∀ i, μ (s i) = 0) → (∀ I : Set (Set Y), MeasurableSet (⋃ i ∈ I, s i)) →
      μ (⋃ i, s i) = 0) :
    AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨AEStronglyMeasurable.aemeasurable,
    fun hf ↦ AEMeasurable.aestronglyMeasurable_of_iUnion_null hf hnull⟩

end MeasureTheory
