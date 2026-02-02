/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.Instances.Discrete

/-!
# Adapted and progressively measurable processes

This file defines the related notions of a process `u` being `Adapted`, `StronglyAdapted`
or `ProgMeasurable` (progressively measurable) with respect to a filter `f`, and proves
some basic facts about them.

## Main definitions

* `MeasureTheory.Adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `MeasureTheory.StronglyAdapted`: a sequence of functions `u` is said to be strongly adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-strongly measurable
* `MeasureTheory.ProgMeasurable`: a sequence of functions `u` is said to be progressively
  measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
  `Set.Iic i × Ω` is strongly measurable with respect to the product `MeasurableSpace` structure
  where the σ-algebra used for `Ω` is `f i`.

## Main results

* `StronglyAdapted.progMeasurable_of_continuous`: a continuous strongly adapted process is
  progressively measurable.

## Tags

adapted, progressively measurable

-/

@[expose] public section

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι] {f : Filtration ι m}

section Adapted

variable {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {u v : (i : ι) → Ω → β i}

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable.

The definition known as `Adapted` before 2026-01-13 is now `StronglyAdapted`. -/
def Adapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, Measurable[f i] (u i)

namespace Adapted

@[to_additive]
protected theorem mul [∀ i, Mul (β i)] [∀ i, MeasurableMul₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive]
protected theorem div [∀ i, Div (β i)] [∀ i, MeasurableDiv₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u / v) := fun i => (hu i).div (hv i)

@[to_additive]
protected theorem inv [∀ i, Group (β i)] [∀ i, MeasurableInv (β i)] (hu : Adapted f u) :
    Adapted f u⁻¹ := fun i => (hu i).inv

protected theorem smul {𝕂 : Type*} [MeasurableSpace 𝕂]
    [∀ i, SMul 𝕂 (β i)] [∀ i, MeasurableSMul 𝕂 (β i)] (c : 𝕂) (hu : Adapted f u) :
    Adapted f (c • u) := fun i => (hu i).const_smul c

protected theorem measurable {i : ι} (hf : Adapted f u) : Measurable[m] (u i) :=
  (hf i).mono (f.le i) (by rfl)

theorem measurable_le {i j : ι} (hf : Adapted f u) (hij : i ≤ j) : Measurable[f j] (u i) :=
  (hf i).mono (f.mono hij) (by rfl)

end Adapted

theorem adapted_const' (f : Filtration ι m) (x : (i : ι) → β i) : Adapted f fun i _ ↦ x i :=
  fun _ ↦ measurable_const

theorem adapted_const {β : Type*} [MeasurableSpace β] (f : Filtration ι m) (x : β) :
    Adapted f fun _ _ ↦ x := adapted_const' _ _

end Adapted

section StronglyAdapted

variable {β : ι → Type*} [∀ i, TopologicalSpace (β i)] {u v : (i : ι) → Ω → β i}

/-- A sequence of functions `u` is strongly adapted to a filtration `f` if for all `i`,
`u i` is `f i`-strongly measurable. -/
def StronglyAdapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, StronglyMeasurable[f i] (u i)

namespace StronglyAdapted

@[to_additive]
protected theorem mul [∀ i, Mul (β i)] [∀ i, ContinuousMul (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive]
protected theorem div [∀ i, Div (β i)] [∀ i, ContinuousDiv (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u / v) := fun i => (hu i).div (hv i)

@[to_additive]
protected theorem inv [∀ i, Group (β i)] [∀ i, ContinuousInv (β i)] (hu : StronglyAdapted f u) :
    StronglyAdapted f u⁻¹ := fun i => (hu i).inv

protected theorem smul [∀ i, SMul ℝ (β i)] [∀ i, ContinuousConstSMul ℝ (β i)]
    (c : ℝ) (hu : StronglyAdapted f u) :
    StronglyAdapted f (c • u) := fun i => (hu i).const_smul c

protected theorem stronglyMeasurable {i : ι} (hf : StronglyAdapted f u) :
    StronglyMeasurable[m] (u i) := (hf i).mono (f.le i)

theorem stronglyMeasurable_le {i j : ι} (hf : StronglyAdapted f u) (hij : i ≤ j) :
    StronglyMeasurable[f j] (u i) := (hf i).mono (f.mono hij)

end StronglyAdapted

theorem StronglyAdapted.adapted [mΒ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    [∀ i, PseudoMetrizableSpace (β i)] (hf : StronglyAdapted f u) :
    Adapted f u := fun _ ↦ (hf _).measurable

theorem Adapted.stronglyAdapted [mΒ : ∀ i, MeasurableSpace (β i)]
    [∀ i, OpensMeasurableSpace (β i)] [∀ i, PseudoMetrizableSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] (hf : Adapted f u) :
    StronglyAdapted f u := fun _ ↦ (hf _).stronglyMeasurable

theorem stronglyAdapted_iff_adapted [mΒ : ∀ i, MeasurableSpace (β i)]
    [∀ i, BorelSpace (β i)] [∀ i, PseudoMetrizableSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] :
    StronglyAdapted f u ↔ Adapted f u := ⟨fun h ↦ h.adapted, fun h ↦ h.stronglyAdapted⟩

theorem stronglyAdapted_const' (f : Filtration ι m) (x : (i : ι) → β i) :
    StronglyAdapted f fun i _ ↦ x i :=
  fun _ ↦ stronglyMeasurable_const

theorem stronglyAdapted_const {β : Type*} [TopologicalSpace β] (f : Filtration ι m) (x : β) :
    StronglyAdapted f fun _ _ ↦ x :=
  stronglyAdapted_const' _ _

variable (β) in
theorem stronglyAdapted_zero' [∀ i, Zero (β i)] (f : Filtration ι m) :
    StronglyAdapted f (0 : (i : ι) → Ω → β i) :=
  fun i ↦ @stronglyMeasurable_zero Ω (β i) (f i) _ _

theorem stronglyAdapted_zero (β : Type*) [TopologicalSpace β] [Zero β] (f : Filtration ι m) :
    StronglyAdapted f (0 : ι → Ω → β) :=
  fun i ↦ @stronglyMeasurable_zero Ω β (f i) _ _

theorem Filtration.stronglyAdapted_natural [∀ i, MetrizableSpace (β i)]
    [mβ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    (hum : ∀ i, StronglyMeasurable[m] (u i)) :
    StronglyAdapted (Filtration.natural u hum) u := by
  intro i
  refine StronglyMeasurable.mono ?_ (le_iSup₂_of_le i (le_refl i) le_rfl)
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).isSeparable_range⟩

end StronglyAdapted

variable {β : Type*} [TopologicalSpace β] {u v : ι → Ω → β}

/-- Progressively measurable process. A sequence of functions `u` is said to be progressively
measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
`Set.Iic i × Ω` is measurable with respect to the product `MeasurableSpace` structure where the
σ-algebra used for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
def ProgMeasurable [MeasurableSpace ι] (f : Filtration ι m) (u : ι → Ω → β) : Prop :=
  ∀ i, StronglyMeasurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

theorem progMeasurable_const [MeasurableSpace ι] (f : Filtration ι m) (b : β) :
    ProgMeasurable f (fun _ _ => b : ι → Ω → β) := fun i =>
  @stronglyMeasurable_const _ _ (Subtype.instMeasurableSpace.prod (f i)) _ _

namespace ProgMeasurable

variable [MeasurableSpace ι]

protected theorem stronglyAdapted (h : ProgMeasurable f u) : StronglyAdapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp_measurable measurable_prodMk_left

protected theorem comp {t : ι → Ω → ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
    (h : ProgMeasurable f u) (ht : ProgMeasurable f t) (ht_le : ∀ i ω, t i ω ≤ i) :
    ProgMeasurable f fun i ω => u (t i ω) ω := by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp_measurable ((ht i).measurable.subtype_mk.prodMk measurable_snd)

section Arithmetic

@[to_additive]
protected theorem mul [Mul β] [ContinuousMul β] (hu : ProgMeasurable f u)
    (hv : ProgMeasurable f v) : ProgMeasurable f fun i ω => u i ω * v i ω := fun i =>
  (hu i).mul (hv i)

@[to_additive]
protected theorem finset_prod' {γ} [CommMonoid β] [ContinuousMul β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, ProgMeasurable f (U c)) : ProgMeasurable f (∏ c ∈ s, U c) :=
  Finset.prod_induction U (ProgMeasurable f) (fun _ _ => ProgMeasurable.mul)
    (progMeasurable_const _ 1) h

@[to_additive]
protected theorem finset_prod {γ} [CommMonoid β] [ContinuousMul β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, ProgMeasurable f (U c)) :
    ProgMeasurable f fun i a => ∏ c ∈ s, U c i a := by
  convert ProgMeasurable.finset_prod' h using 1; ext (i a); simp only [Finset.prod_apply]

@[to_additive]
protected theorem inv [Group β] [ContinuousInv β] (hu : ProgMeasurable f u) :
    ProgMeasurable f fun i ω => (u i ω)⁻¹ := fun i => (hu i).inv

@[to_additive]
protected theorem div [Group β] [ContinuousDiv β] (hu : ProgMeasurable f u)
    (hv : ProgMeasurable f v) : ProgMeasurable f fun i ω => u i ω / v i ω := fun i =>
  (hu i).div (hv i)

end Arithmetic

end ProgMeasurable

theorem progMeasurable_of_tendsto' {γ} [MeasurableSpace ι] [PseudoMetrizableSpace β]
    (fltr : Filter γ) [fltr.NeBot] [fltr.IsCountablyGenerated] {U : γ → ι → Ω → β}
    (h : ∀ l, ProgMeasurable f (U l)) (h_tendsto : Tendsto U fltr (𝓝 u)) : ProgMeasurable f u := by
  intro i
  apply @stronglyMeasurable_of_tendsto (Set.Iic i × Ω) β γ
    (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto ⊢
  intro x
  specialize h_tendsto x.fst
  rw [tendsto_nhds] at h_tendsto ⊢
  exact fun s hs h_mem => h_tendsto {g | g x.snd ∈ s} (hs.preimage (continuous_apply x.snd)) h_mem

theorem progMeasurable_of_tendsto [MeasurableSpace ι] [PseudoMetrizableSpace β] {U : ℕ → ι → Ω → β}
    (h : ∀ l, ProgMeasurable f (U l)) (h_tendsto : Tendsto U atTop (𝓝 u)) : ProgMeasurable f u :=
  progMeasurable_of_tendsto' atTop h h_tendsto

/-- A continuous and strongly adapted process is progressively measurable. -/
theorem StronglyAdapted.progMeasurable_of_continuous [TopologicalSpace ι] [MetrizableSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) (hu_cont : ∀ ω, Continuous fun i => u i ω) :
    ProgMeasurable f u := fun i =>
  @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable _ _ (Set.Iic i) _ _ _ _ _ _ _
    (f i) _ (fun ω => (hu_cont ω).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.prop)

/-- A right continuous and strongly adapted proces is progressively measurable. Note that the
assumptions -/
lemma Adapted.progMeasurable_of_rightContinuous [TopologicalSpace ι] [LinearOrder ι]
    [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u)
    (hu_cont : ∀ ω i, ContinuousWithinAt (u · ω) (Set.Ioi i) i) :
    ProgMeasurable f u := by
  intro t
  -- separate into two cases because the partition we defined below cannot contain empty sets
  by_cases hΩ : Nonempty Ω
  swap; · simp_all [stronglyMeasurable_const']
  -- ip is the set of points in (-∞,t] that are isolated on the right
  let ip := {x : Set.Iic t | 𝓝[>] x = ⊥}
  have tmemip : ⟨t, le_rfl⟩ ∈ ip := by
    simp only [← not_neBot, nhdsWithin_neBot, not_forall,
      Set.not_nonempty_iff_eq_empty, Set.mem_setOf_eq, ip]
    use .univ; simp; sorry
  have ipc : ip.Countable := countable_setOf_isolated_right (α := Set.Iic t)
  -- d is the set of points dense in (-∞,t]
  obtain ⟨d, dc, dd⟩ := TopologicalSpace.exists_countable_dense (Set.Iic t)
  let s := ip ∪ d
  have tmems : ⟨t, le_rfl⟩ ∈ s := Or.inl tmemip
  have nonemptys : Nonempty s := ⟨_, tmems⟩
  obtain ⟨u, hu⟩ := countable_iff_exists_surjective.mp (Countable.union ipc dc)
  obtain ⟨k, hk⟩ := hu ⟨_, tmems⟩
  let r (n : ℕ) := (Finset.range (n + k + 1)).image (Subtype.val ∘ u)
  -- rearrange the set {u 0, ..., u (n + k)} so that it is in the increasing order
  let v (n : ℕ) := Finset.orderEmbOfFin (r n) rfl
  let f (n : ℕ) : Fin (r n).card → Set (Iic t × Ω) := fun i =>
    if h0 : i = ⟨0, by simp [r]⟩ then Iic (v n i) ×ˢ univ
    else Ioc (v n ⟨i.val - 1, lt_trans (Nat.sub_one_lt (fun h => h0 (Fin.eq_of_val_eq h))) i.2⟩)
      (v n i) ×ˢ univ
  have hav (a : Iic t × Ω) (n : ℕ) : a.1 ≤ v n ⟨(r n).card - 1, Nat.sub_one_lt (by simp [r])⟩ := by
    have l : v n ⟨(r n).card - 1, Nat.sub_one_lt (by simp [r])⟩ = ⟨t, le_rfl⟩ := by
      simp only [Finset.orderEmbOfFin_last (rfl : (r n).card = (r n).card) (by simp [r]),
        Finset.max'_eq_iff, Subtype.forall, mem_Iic, Subtype.mk_le_mk, v, r,
        Finset.mem_image, Finset.mem_range, comp_apply]
      exact ⟨⟨k, by linarith, by simp [hk]⟩, fun a ha _ => ha⟩
    simpa [l] using mem_Iic.mp a.1.2
  have LEM (a : Iic t × Ω) (n : ℕ) := (Option.isSome_iff_exists.mp (Fin.isSome_find_iff.mpr
    (Exists.intro (p := fun i ↦ a.1 ≤ v n i) ⟨(r n).card - 1, Nat.sub_one_lt (by simp [r])⟩
    (hav a n))))
  have disj (n : ℕ) : Pairwise (Disjoint on (f n)) := by
    simp only [pairwise_disjoint_on]
    intro i j hij
    by_cases hi0 : i = ⟨0, by simp [r]⟩
    · have hj0 : ⟨0, by simp [r]⟩ ≠ j := by simp [← hi0, hij.ne]
      simp [f, hi0, hj0.symm]
    · have hj0 : 0 < j.val := by grind
      have hj1 : ⟨0, by simp [r]⟩ ≠ j := by grind
      simp only [hi0, ↓reduceDIte, hj1.symm, Set.disjoint_prod, Ioc_disjoint_Ioc, le_sup_iff,
        inf_le_iff, OrderEmbedding.le_iff_le, disjoint_self, bot_eq_empty, univ_eq_empty_iff,
        not_isEmpty_of_nonempty, or_false, f]
      simp only [Fin.lt_def, ← Nat.le_sub_one_iff_lt hj0] at hij
      exact Or.inr (Or.inl hij)
  -- create a partition of (Iic t) × Ω
  let P (n : ℕ) : IndexedPartition (f n) :=
    { eq_of_mem {a i j} hai haj := by_contradiction fun h => (disj n h).le_bot ⟨hai, haj⟩
      some i := (v n i, hΩ.some)
      some_mem i := by
        by_cases h0 : i = ⟨0, by simp [r]⟩
        · simp [f, h0]
        · simp [f, h0, Fin.lt_def, Nat.sub_one_lt (fun j => h0 (Fin.eq_of_val_eq j))]
      index a := (LEM a n).choose -- choose the smallest i such that a.1 ≤ v n i
      mem_index a := by
        have hi := (LEM a n).choose_spec
        by_cases h0 : (LEM a n).choose = ⟨0, by simp [r]⟩
        · simp_all only [nonempty_subtype, Subtype.exists, mem_Iic, ↓reduceDIte, mem_prod, mem_univ,
            and_true, f]
          exact Fin.find_spec (fun i ↦ a.1 ≤ (v n) i) hi
        · simp only [h0, ↓reduceDIte, mem_prod, mem_Ioc, mem_univ, and_true, f]
          constructor
          · exact lt_of_not_ge (Fin.find_min hi (Nat.sub_one_lt (fun j => h0 (Fin.eq_of_val_eq j))))
          · exact Fin.find_spec (fun i ↦ a.1 ≤ (v n) i) hi }
  -- discrete approximation of X
  let U : ℕ → (Iic t) × Ω → β := fun n p => (P n).piecewise (fun m => fun q => X (v n m) q.2) p
  -- X is strongly measurable because it is the pointwise limit of strongly measurable functions
  refine stronglyMeasurable_of_tendsto (f := U) (u := atTop) (fun n => ?_) ?_
  · refine StronglyMeasurable.IndexedPartition (P n) (fun m => ?_) (fun m => ?_)
    · by_cases h0 : m = ⟨0, by simp [r]⟩
      · simpa [f, h0] using MeasurableSet.prod measurableSet_Iic MeasurableSet.univ
      · simpa [f, h0] using MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
    · exact ((h (v n m)).mono (𝓕.mono' (by grind))).comp_snd
  · simp only [tendsto_pi_nhds]
    intro a
    -- to show pointwise convergence, we consider two cases : a.1 ∈ s or a.1 ∉ s.
    by_cases has : a.1 ∈ s
    · -- in this case, U i is eventually equal to X because a.1 is eventually in the image of v
      have : ∀ᶠ i in atTop, U i a = X a.1 a.2 := by
        have ⟨z, hz⟩ := hu ⟨_, has⟩
        refine eventually_atTop.mpr ⟨z, fun x hxz => ?_⟩
        simp only [U, IndexedPartition.piecewise_apply]
        congr
        have : ∃ y, v x y = a.1 := by
          have lem1 := Finset.range_orderEmbOfFin (r x) rfl
          have lem2 : a.1 ∈ (r x : Set (Iic t)) := by
            simp only [Finset.coe_image, comp_apply, Finset.coe_range, mem_image, mem_Iio, r]
            exact ⟨z, by linarith, by simp [hz]⟩
          rw [← lem1, Set.mem_range] at lem2
          exact lem2
        obtain ⟨y, hy⟩ := this
        by_cases py : y = ⟨0, by simp [r]⟩
        · have qy : a ∈ (f x) y := by simp [py, f, ← hy]
          simpa [(P x).mem_iff_index_eq.mp qy]
        · have qy : a ∈ (f x) y := by
            simp only [py, ↓reduceDIte, mem_prod, ← hy, mem_Ioc, OrderEmbedding.lt_iff_lt, le_refl,
              and_true, mem_univ, f]
            exact Nat.sub_one_lt (fun j => py (Fin.eq_of_val_eq j))
          simpa [(P x).mem_iff_index_eq.mp qy]
      exact tendsto_nhds_of_eventually_eq this
    · -- in this case, we use Tendsto.comp, right continuity, and density of d
      let w : ℕ → ι := fun n => v n ((P n).index a)
      have tends1 : Tendsto w atTop (𝓝[>] a.1) := by
        have lem1 (n) : a.1 ≤ v n ((P n).index a) := by
          have := (P n).mem_iff_index_eq.mpr (rfl : (P n).index a = (P n).index a)
          by_cases hPa : (P n).index a = ⟨0, by simp [r]⟩ <;> simp_all [f]
        refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_atTop_nhds.mpr fun V hV hoV => ?_,
          Eventually.of_forall fun n => ?_⟩
        · -- we want to show for n large enough, w n ∈ V. V ∩ (-∞, t] is a neighborhood of a.1 in
          -- the subspace topology of (-∞, t], so we have some ep : Iic t such that
          -- [a.1, ep) ⊆ V ∩ (-∞, t]. (a.1, ep) is then a nonempty open set (because a.1 is not
          -- isolated from right), so it intersects with d. Denote this point of intersection by
          -- e. e = u N, so it is also equal to (v n) M for all n ≥ N and some M : Fin n.
          -- As a.1 ≤ e = (v N) M, w n ≤ e = (v n) M < ep.
          have NVa : Subtype.val ⁻¹' V ∈ 𝓝 a.1 := (hoV.preimage continuous_subtype_val).mem_nhds
            (by simp [hV])
          have altt : a.1 < ⟨t, le_rfl⟩ := LE.le.lt_of_ne' a.1.2 (fun h =>
            by rw [← h] at has; exact has tmems)
          obtain ⟨ep, hep⟩ := exists_Ico_subset_of_mem_nhds NVa (Exists.intro ⟨t, le_rfl⟩ altt)
          have : (Ioo a.1 ep).Nonempty := by
            by_contra!
            have : a.1 ∈ ip := by
              have inter : Ioo a.1 ep = Ioi a.1 ∩ Iio ep := by grind
              simp only [← empty_mem_iff_bot, ← this, mem_setOf_eq, ip, inter]
              apply inter_mem_nhdsWithin (Ioi a.1) (IsOpen.mem_nhds isOpen_Iio (by simp [hep.1]))
            exact has (Or.inl this)
          have : ((Ioo a.1 ep) ∩ d).Nonempty := Dense.inter_open_nonempty dd (Ioo a.1 ep)
            isOpen_Ioo this
          obtain ⟨e, he⟩ := this
          obtain ⟨N, hN⟩ := hu ⟨_, Or.inr he.2⟩
          refine ⟨N, fun n hn => ?_⟩
          suffices w n ∈ Subtype.val '' Ico a.1 ep from by
            rw [← image_subset_iff] at hep
            exact hep.2 this
          simp only [image_subtype_val_Ico, mem_Ico]
          refine ⟨lem1 n, ?_⟩
          suffices w n ≤ e from lt_of_le_of_lt this he.1.2
          have hev : e ∈ univ.image (v n) := by simpa [v, r] using ⟨N, by linarith, by simp [hN]⟩
          obtain ⟨M, hM⟩ := hev
          simp only [← hM.2, Subtype.coe_le_coe, OrderEmbedding.le_iff_le, ge_iff_le, w]
          exact (Fin.find_eq_some_iff.mp (LEM a n).choose_spec).2 M (by simp [hM.2, he.1.1.le])
        · simp only [mem_Ioi, Subtype.coe_lt_coe, w]
          have lem2 : v n ((P n).index a) ≠ a.1 := by
            intro hva
            have m1 : a.1 ∈ (r n : Set (Iic t)) := by simp [← hva, v]
            have m2 : (r n : Set (Iic t)) ⊆ s := by
              simpa [r] using MapsTo.subset_preimage (fun _ _ => by simp)
            exact has (m2 m1)
          exact LE.le.lt_of_ne' (lem1 n) lem2
      have tends2 := ContinuousWithinAt.tendsto (hu_cont a.2 a.1)
      have : (fun x => U x a) = (X · a.2) ∘ w := by
        ext; simp [U, w, IndexedPartition.piecewise_apply]
      simpa [this] using tends2.comp tends1

/-- For filtrations indexed by a discrete order, `StronglyAdapted` and `ProgMeasurable` are
equivalent. This lemma provides `StronglyAdapted f u → ProgMeasurable f u`.
See `ProgMeasurable.stronglyAdapted` for the reverse direction, which is true more generally. -/
theorem StronglyAdapted.progMeasurable_of_discrete [TopologicalSpace ι] [DiscreteTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) : ProgMeasurable f u :=
  h.progMeasurable_of_continuous fun _ => continuous_of_discreteTopology

-- this dot notation will make more sense once we have a more general definition for predictable
theorem Predictable.stronglyAdapted {f : Filtration ℕ m} {u : ℕ → Ω → β}
    (hu : StronglyAdapted f fun n => u (n + 1)) (hu0 : StronglyMeasurable[f 0] (u 0)) :
    StronglyAdapted f u := fun n =>
  match n with
  | 0 => hu0
  | n + 1 => (hu n).mono (f.mono n.le_succ)

end MeasureTheory
