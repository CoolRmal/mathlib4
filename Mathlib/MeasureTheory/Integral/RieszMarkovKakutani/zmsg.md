**Subject:** Complex Riesz-Markov-Kakutani representation theorem

Following up on the Aug 2025 thread "Uniqueness in Riesz-Markov-Kakutani representation theorem" (now resolved), I'd like to propose the next step: formalizing the complex RMK theorem (Rudin, RCA Theorem 6.19). For `X` locally compact T2, the topological dual of `C₀(X, ℂ)` is isometrically isomorphic to the space of finite regular complex Borel measures with total variation norm. Is anyone already working on this? Happy to help or split the work. Below are the details and a few design questions.

**Goal.** `C₀(X, ℂ)* ≃ₗᵢ[ℂ] M(X)`, where `M(X)` denotes the space of regular complex Borel measures with total variation norm (Rudin's notation).

**Infrastructure needed to state the goal.**

- **Norm on `ComplexMeasure`/`SignedMeasure`.** `totalVariation` exists but has no triangle inequality or homogeneity, so neither has a `NormedAddCommGroup` instance.
- **Bundled type `M(X)`.** `Measure.Regular` is a typeclass on positive measures; there is no `Regular` predicate for `SignedMeasure`/`ComplexMeasure`. I propose defining a typeclass `SignedMeasure.Regular s` (asserting both Jordan parts are regular) and a bundled structure `RegularComplexMeasure X` carrying the `NormedAddCommGroup` and `CompleteSpace` instances needed as the codomain.
- **Isometric embedding `C_c → C₀`.** The coercion exists (`CoeTC` via `ZeroAtInftyContinuousMapClass`). We'll prove it's an isometric embedding (sup norm pulled back from `C₀`) rather than defining a global `NormedAddCommGroup` on `C_c` — the latter would conflict with a future inductive limit topology (mathlib has no inductive limit TVS infrastructure yet).
- **Density of `C_c` in `C₀`.** `DenseRange` for the embedding above is missing.
- **Density of `C_c` in `L¹(μ)`.** Mathlib has `Lp.dense_hasCompactSupport_contDiff` (smooth compactly supported functions are dense in `Lp`), but we need the `C_c` version (continuous, not smooth) for finite regular `μ`. Needed for extending `Φ` from `C_c` to `L¹(μ)` in step 3.
- **(L¹(μ))* ≅ L∞(μ) for finite `μ`.** The representation theorem for the dual of `L¹` is missing. Mathlib has Hölder pairing (`lpPairing` in `Holder.lean`) but no `LinearIsometryEquiv`. Since our `μ` is finite (`μ(X) ≤ ‖Φ‖`), we only need the finite-measure case (no σ-finiteness issues).

**Riesz representation proof outline (following Rudin RCA 6.19).**

0. **Uniqueness.** If two regular measures give the same integrals on `C_c`, they are equal. *Already formalized:* `Measure.ext_of_integral_eq_on_compactlySupported`.
1. **Construct `Λ`.** Given `Φ : C₀(X, ℂ) →L[ℂ] ℂ`, define `Λ(f) = sup{|Φ(g)| : |g| ≤ f, g ∈ C_c}` for `f ≥ 0`. Show `Λ` is a bounded positive linear functional. Additivity uses the Riesz decomposition property of the lattice.
2. **Apply positive RMK to `Λ`.** `Λ` is defined on `C_c`; apply positive RMK directly to get regular measure `μ` with `Λ(f) = ∫ f dμ` for all `f ∈ C_c`. Extend to `C₀` by density.
3. **Complex measure construction (representation + isometry).** The key bound `|Φ(f)| ≤ Λ(|f|) = ∫ |f| dμ = ‖f‖_{L¹(μ)}` shows `Φ` extends by density to a continuous functional on `L¹(μ)` with `(L¹)*`-norm `≤ 1`. By `(L¹(μ))* ≅ L∞(μ)`, there exists `g ∈ L∞(μ)` with `‖g‖_∞ ≤ 1` and `Φ(f) = ∫ f · g dμ`. Choose a strongly measurable representative and define the complex measure `λ := μ.withDensityᵥ g`. Show `|g| = 1` μ-a.e. (comparing `Λ(f) = ∫ f dμ` with the L¹ sup `∫ f |g| dμ`), so `|λ| = μ`. Then `Φ(f) = ∫ f dλ` and `‖Φ‖ = |λ|(X) = μ(X)`.

*What exists:* Steps 0 and 2 are done.

*What's missing:* Step 1 (positive-part construction + Riesz decomposition); step 3 needs `(L¹)* ≅ L∞`, which isn't in mathlib.

**Proposed PRs:** (PRs 1–4 are independent and can be done in parallel.)

1. **Isometric embedding `C_c → C₀` and density.** Prove the existing coercion is an isometric embedding (pullback of sup norm) without defining a global `NormedAddCommGroup` on `C_c`. Prove `DenseRange`: given `f ∈ C₀` and `ε > 0`, `{|f| ≥ ε}` is compact; by Urysohn find cutoff `g ∈ C_c` with `g = 1` there, then `f · g ∈ C_c` and `‖f - f·g‖ ≤ ε`.

2. **`NormedAddCommGroup` on `ComplexMeasure`/`SignedMeasure` and bundled `M(X)`.** Define `‖s‖ := (s.totalVariation Set.univ).toReal`. Need triangle inequality and homogeneity for `totalVariation`, which don't exist yet. Define typeclass `SignedMeasure.Regular` (both Jordan parts regular) and bundled `RegularComplexMeasure X` structure with `NormedAddCommGroup` and `CompleteSpace` instances.

3. **Riesz decomposition property.** `0 ≤ h ≤ f₁ + f₂` with `fᵢ ≥ 0` implies `h = h₁ + h₂` with `0 ≤ hᵢ ≤ fᵢ`, via `h₁ := h ⊓ f₁`. I propose a mixin typeclass `[RieszDecomposition E]` rather than a full `RieszSpace` hierarchy. Should live in `Order.LatticeOrderedGroup`.

4. **Dual of L¹ for finite measures.** Prove `(L¹(μ))* ≃ₗᵢ L∞(μ)` for `[IsFiniteMeasure μ]` (or σ-finite) — every bounded linear functional on `L¹` is integration against an `L∞` function, with matching norms. Mathlib has Hölder pairing but not the isometric isomorphism.

5. **Positive-part construction for bounded functionals.** (Step 1.) For `Φ : C₀(X, ℂ) →L[ℂ] ℂ`, define `Λ(f) = sup{|Φ(g)| : |g| ≤ f, g ∈ C_c}` for `f ≥ 0`, prove linearity, positivity, and boundedness with `|Φ(f)| ≤ Λ(|f|)`. Additivity uses PR 3.

6. **The complex RMK theorem.** (Step 3.) Extend `Φ` to `L¹(μ)` using `|Φ(f)| ≤ ∫ |f| dμ`, apply PR 4 to get `g ∈ L∞(μ)` with `Φ(f) = ∫ f · g dμ`. Show `|g| = 1` μ-a.e. Define `λ := g · μ`, then `|λ| = μ`, `Φ(f) = ∫ f dλ`, and `‖Φ‖ = |λ|(X)`. Prove `C₀(X, ℂ)* ≃ₗᵢ[ℂ] M(X)`.

**Questions for the community.** The mathematical content follows Rudin closely and is well-understood; the design questions are about API packaging.

1. **Riesz decomposition (PR 3).** I propose a mixin typeclass `[RieszDecomposition E]` for `[Lattice E] [AddCommGroup E] [IsOrderedAddMonoid E]`, rather than a full `VectorLattice` / `RieszSpace` hierarchy. PR 5 would then assume `[RieszDecomposition E]`. Is this the right scope?

2. **Bundled `M(X)` (PR 2).** I propose a typeclass `SignedMeasure.Regular` (both Jordan parts regular) and a bundled `RegularComplexMeasure X` structure with `NormedAddCommGroup` and `CompleteSpace`. Is a bundled structure the right approach, or would a subtype with typeclass assumptions be preferred?

3. **Dual of L¹ (PR 4).** Is anyone already working on `(L¹)* ≃ₗᵢ L∞`? It's a foundational result and would be independently useful. If no one is doing it, is there a preferred route (e.g., via Radon-Nikodym)?













<details>
<summary>Detailed Infrastructure Audit (click to expand)</summary>

### PR 1: Sup Norm on `C_c(X, ℝ)`

**Goal.** Equip `CompactlySupportedContinuousMap α β` with `NormedAddCommGroup` (and `NormedSpace`)
via the sup norm, induced from `BoundedContinuousFunction` through the existing embedding.

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| Embedding into BCF | `toBoundedContinuousFunction : C_c(α, β) → (α →ᵇ β)` | `CompactlySupported.lean:156` | Uses `HasCompactSupport.isCompact_range` for boundedness. `@[simps]` gives `toBoundedContinuousFunction_apply`. |
| BCF norm | `BoundedContinuousFunction.instNorm` | `Bounded/Normed.lean:40` | `‖f‖ = sInf { C \| 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C }`. Full `NormedAddCommGroup` (line 202). |
| `C₀` norm (template) | `instSeminormedAddCommGroup`, `instNormedAddCommGroup` | `ZeroAtInfty.lean:449-456` | Induced from BCF via `AddMonoidHom` with `NormedAddCommGroup.induced`. Inline `rfl` proofs for `map_zero'` and `map_add'`. |
| `C₀` metric (template) | `instPseudoMetricSpace`, `instMetricSpace` | `ZeroAtInfty.lean:390-397` | `PseudoMetricSpace.induced toBCF`, `MetricSpace.induced _ inj`. |
| `C₀` isometry/completeness | `isometry_toBCF`, `isClosed_range_toBCF`, `instCompleteSpace` | `ZeroAtInfty.lean:412-433` | Completeness follows from closed range + complete codomain. |
| `C₀` normed space | `instNormedSpace` | `ZeroAtInfty.lean:464` | `norm_smul_le k f := norm_smul_le k f.toBCF`. |
| `C_c` is `C₀` | `ZeroAtInftyContinuousMapClass` instance on `C_c` | `CompactlySupported.lean:661` | Via `HasCompactSupport.is_zero_at_infty`. |
| `C_c` uniform continuity | `CompactlySupportedContinuousMapClass.uniformContinuous` | `CompactlySupported.lean:650` | ✓ |

#### What's missing

All items below are ~1-5 lines each, following the `C₀` template verbatim:

1. **`toBoundedContinuousFunction_injective`** — `DFunLike.coe_injective.comp` or `fun f g h => ext (DFunLike.congr_fun h ·)`.

2. **`instPseudoMetricSpace`** — `PseudoMetricSpace.induced toBoundedContinuousFunction inferInstance`.

3. **`instMetricSpace`** — `MetricSpace.induced _ (toBoundedContinuousFunction_injective α β) inferInstance`.

4. **`instSeminormedAddCommGroup`** — `SeminormedAddCommGroup.induced _ _ ⟨⟨toBoundedContinuousFunction, rfl⟩, fun _ _ => rfl⟩`. The `rfl` proofs work because `toBoundedContinuousFunction` preserves `0` and `+` definitionally (all operations are pointwise).

5. **`instNormedAddCommGroup`** — `NormedAddCommGroup.induced _ _ (AddMonoidHom) (toBoundedContinuousFunction_injective α β)`.

6. **`instNormedSpace`** — `norm_smul_le k f := norm_smul_le k f.toBoundedContinuousFunction`.

7. **Simp lemmas** — `norm_toBoundedContinuousFunction_eq_norm`, `dist_toBoundedContinuousFunction_eq_dist` (both `rfl`).

8. **Optional: `isometry_toBoundedContinuousFunction`, `isClosed_range_toBoundedContinuousFunction`, `instCompleteSpace`** — following `C₀` pattern. Completeness uses closed range in complete space.

**Estimated size:** ~50-60 lines. No design decisions. No new mathematical content.

---

### PR 2: Density of `C_c` in `C₀`

**Goal.** Prove `C_c` is dense in `C₀` w.r.t. the sup norm. Transfer the positive RMK from `C_c` to `C₀`.

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| `ZeroAtInftyContinuousMapClass` on `C_c` | instance | `CompactlySupported.lean:662` | Via `HasCompactSupport.is_zero_at_infty`. |
| Coercion `C_c → C₀` | `instCoeTC` | `ZeroAtInfty.lean:89` | Generic `CoeTC F C₀(α, β)` for any `F` with `ZeroAtInftyContinuousMapClass`. Already works for `C_c`. |
| Urysohn for LCH | `exists_continuousMap_one_of_isCompact_subset_isOpen` | Used in `Real.lean:385` | Gives `f : C(X, ℝ)` with `f = 1` on compact `K`, `tsupport f ⊆ U` open, `0 ≤ f ≤ 1`. |

#### What's missing

1. **`DenseRange` for the `C_c → C₀` embedding.** Given `f ∈ C₀(X, ℝ)` and `ε > 0`, `{x : |f(x)| ≥ ε}` is compact (vanishing at infinity). By Urysohn, find cutoff `g ∈ C_c` with `g = 1` on this set, `0 ≤ g ≤ 1`. Then `f · g ∈ C_c` and `‖f - f · g‖ ≤ ε`.

2. **Transfer of positive RMK to `C₀`.** A positive functional `Λ : C₀(X, ℝ) → ℝ` restricts to `C_c`. Apply `rieszMeasure` to the restriction. Prove the resulting measure integrates all `C₀` functions correctly by density + dominated convergence.

**Should live in:** `Topology.ContinuousMap.ZeroAtInfty` or `CompactlySupported`.

---

### PR 3: `NormedAddCommGroup` Instance on `SignedMeasure` via Total Variation

**Goal.** Equip `SignedMeasure α` with a norm `‖s‖ := (s.totalVariation Set.univ).toReal`
and prove it satisfies `NormedAddCommGroup`.

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| `SignedMeasure` definition | `abbrev SignedMeasure α := VectorMeasure α ℝ` | `VectorMeasure/Basic.lean:74` | Abbreviation, not a new type. |
| Algebraic instances | `AddCommGroup`, `Module R` on `VectorMeasure` | `VectorMeasure/Basic.lean:351,372` | Via `Function.Injective.addCommGroup`. |
| `totalVariation` | `s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart` | `Jordan.lean:454` | Returns `Measure α`. |
| Finiteness of Jordan parts | `[posPart_finite : IsFiniteMeasure posPart]`, `[negPart_finite : IsFiniteMeasure negPart]` | `Jordan.lean:64-65` | Built into `JordanDecomposition`. |
| `IsFiniteMeasure` of sum | `isFiniteMeasureAdd` | `Measure/Typeclasses/Finite.lean` | `totalVariation` is automatically finite. |
| `totalVariation_zero` | `(0 : SignedMeasure α).totalVariation = 0` | `Jordan.lean:458` | ✓ |
| `totalVariation_neg` | `(-s).totalVariation = s.totalVariation` | `Jordan.lean:461` | ✓ |
| Separation | `null_of_totalVariation_zero` | `Jordan.lean:464` | `s.totalVariation i = 0 → s i = 0`. |
| General variation | `VectorMeasure.variation` | `VectorMeasure/Variation/Defs.lean:51` | Definition only (58-line file), no lemmas. Different construction from `totalVariation`. |
| `NormedAddCommGroup.ofSeparation` | Takes `SeminormedAddCommGroup` + separation proof | `Analysis/Normed/Group/Defs.lean:272` | Standard constructor. |

#### What's missing

1. **Triangle inequality for `totalVariation`.** Need `(s + t).totalVariation Set.univ ≤ s.totalVariation Set.univ + t.totalVariation Set.univ`. Not equality. Requires Hahn decomposition arguments. No existing lemma.

2. **Homogeneity.** Need `(r • s).totalVariation Set.univ = |r| * s.totalVariation Set.univ`. No `totalVariation_smul` exists.

3. **`SeminormedAddCommGroup` instance.** Define `Norm`, `Dist`, `PseudoMetricSpace`, verify axioms.

4. **Full separation.** Lift `null_of_totalVariation_zero` to `s = 0` via `VectorMeasure` extensionality.

5. **Unification of `VectorMeasure.variation` and `SignedMeasure.totalVariation`.** Two competing definitions of the same thing. Should prove they agree. Not blocking, but important for coherence.

---

### PR 4: Riesz Decomposition Property for Lattice-Ordered Groups

**Goal.** Prove: in a lattice-ordered additive group, if `0 ≤ h ≤ f₁ + f₂` with `f₁, f₂ ≥ 0`,
then `h = h₁ + h₂` with `0 ≤ hᵢ ≤ fᵢ`.

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| Lattice-ordered group API | `sup_sub_inf_eq`, `sup_add_inf_eq`, etc. | `Order/LatticeOrderedGroup.lean` | Birkhoff's identities. |
| Positive/negative parts | `a⁺ := a ⊔ 0`, `a⁻ := (-a) ⊔ 0` | `Algebra/Order/Group/PosPart.lean:54,61` | `posPart_sub_negPart`, `posPart_inf_negPart_eq_zero`. |

#### What's missing

1. **The Riesz decomposition lemma.** For `[Lattice E] [AddCommGroup E] [IsOrderedAddMonoid E]`: given `0 ≤ h ≤ f₁ + f₂` with `f₁, f₂ ≥ 0`, set `h₁ := h ⊓ f₁` and `h₂ := h - h₁`. Prove `0 ≤ h₁ ≤ f₁`, `0 ≤ h₂ ≤ f₂`, `h = h₁ + h₂`. The bound `h₂ ≤ f₂` follows from `h - f₂ ≤ f₁` (since `h ≤ f₁ + f₂`) and `h - f₂ ≤ h`, giving `h - f₂ ≤ h ⊓ f₁`.

2. **Placement.** Should live in `Order.LatticeOrderedGroup` or a new `Order.RieszDecomposition`. Community to decide: typeclass `RieszDecompositionProperty` or just a lemma.

**Estimated size:** ~30-50 lines.

---

### PR 5: Decomposition of Bounded Linear Functionals into Positive Parts

**Goal.** Given `Λ : C₀(X, ℝ) →L[ℝ] ℝ`, construct `Λ⁺, Λ⁻` positive linear with `Λ = Λ⁺ - Λ⁻`.

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| Positive linear maps | `PositiveLinearMap R E₁ E₂` (notation `E →ₚ[R] F`) | `Algebra/Order/Module/PositiveLinearMap.lean:31` | Has `AddCommMonoid` (line 158), but **no `AddCommGroup`**. |
| Lattice on `C_c` / `C₀` | `Lattice C_c(α, β)` | `CompactlySupported.lean:512` | Pointwise. |
| Supremum on ℝ | `sSup : Set ℝ → ℝ`, `Real.isLUB_sSup` | `Data/Real/Archimedean.lean` | Completeness of ℝ. |
| Riesz decomposition | (PR 4) | | Prerequisite. |

#### What's missing

1. **The decomposition `Λ⁺` itself.** Define `Λ⁺(f) := sSup {Λ(g) | 0 ≤ g ≤ f}` for `f ≥ 0`, extend to all functions.

2. **Linearity of `Λ⁺`.** Additivity for nonneg arguments uses PR 4 to split `g` with `0 ≤ g ≤ f₁ + f₂`.

3. **Boundedness of `Λ⁺`.** Need `Λ⁺(f) ≤ ‖Λ‖ · ‖f‖` (sup norm from PR 1).

4. **Extension from nonneg to all functions.** `Λ⁺(f) := Λ⁺(f⁺) - Λ⁺(f⁻)` requires well-definedness.

5. **`AddCommGroup` on `PositiveLinearMap`.** Currently only `AddCommMonoid`. Work with underlying `LinearMap` and prove positivity separately.

---

### PR 6: The Signed RMK Theorem

**Goal.** Every bounded linear functional on `C₀(X, ℝ)` is integration against a unique
regular signed measure.

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| Positive RMK: existence | `integral_rieszMeasure : ∫ x, f x ∂(rieszMeasure Λ) = Λ f` | `Real.lean:344` | For positive `Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ`. |
| Positive RMK: uniqueness | `rieszMeasure_integralPositiveLinearMap` | `Real.lean:432` | `rieszMeasure` is surjective onto regular measures. |
| Positive RMK: inverse | `integralPositiveLinearMap_rieszMeasure` | `Real.lean:437` | Round-trip. |
| Regularity | `regular_rieszMeasure` | `Real.lean:356` | Automatic instance. |
| Measure → SignedMeasure | `Measure.toSignedMeasure` | `VectorMeasure/Basic.lean:418` | Requires `[IsFiniteMeasure μ]`. ✓ — bounded on `C₀` gives finite. |
| Subtraction | `μ.toSignedMeasure - ν.toSignedMeasure` | `VectorMeasure/Basic.lean:495` | Pointwise. |
| Jordan equiv | `toJordanDecompositionEquiv` | `Jordan.lean:409` | Full bijection. |
| Uniqueness of measures | `Measure.ext_of_integral_eq_on_compactlySupported` | `Real.lean:411` | Two regular measures equal iff same integrals on `C_c`. |

#### What's missing

1. **Integration against signed measures.** No `∫ x, f x ∂s` for `s : SignedMeasure`. State via Jordan parts: `∫ f ∂posPart - ∫ f ∂negPart`.

2. **Regularity for signed measures.** No `Regular` predicate for `SignedMeasure`. Define as: both Jordan parts are regular. Typeclass or subtype.

3. **Representation formula.** Prove `Λ(f) = ∫ f ∂s.posPart - ∫ f ∂s.negPart` for all `f : C₀(X, ℝ)`.

4. **Uniqueness for signed measures.** If two regular signed measures give the same integrals on `C₀`, they're equal. Apply `Measure.ext_of_integral_eq_on_compactlySupported` to Jordan parts.

5. **Mutual singularity: NOT required.** Construct `s := μ⁺.toSignedMeasure - μ⁻.toSignedMeasure` as direct `VectorMeasure` subtraction. The Jordan decomposition of `s` is computed by `toJordanDecomposition`; we never need `μ⁺ ⟂ₘ μ⁻`.

---

### PR 7: Isometric Isomorphism `C₀(X, ℝ)* ≅ M(X)`

**Goal.** The map `s ↦ (f ↦ ∫ f ds)` is a `LinearIsometryEquiv` between regular signed
measures (TV norm) and the topological dual of `C₀(X, ℝ)` (operator norm).

#### What exists

| Component | Declaration | File | Notes |
|-----------|-------------|------|-------|
| `LinearIsometryEquiv` | `structure LinearIsometryEquiv` | `LinearIsometry.lean:425` | Needs `toLinearEquiv` + `norm_map'`. |
| `ofSurjective` constructor | `LinearIsometryEquiv.ofSurjective` | `LinearIsometry.lean:952` | Standard pattern: isometry + surjectivity. |
| Operator norm | `ContinuousLinearMap.opNorm` | `Normed/Operator/Basic.lean:174` | Automatic from `ContinuousLinearMap`. |
| Riesz representation pattern | `InnerProductSpace.toDual` | `InnerProductSpace/Dual.lean:137` | Example of the pattern: `ofSurjective` on a `LinearIsometry`. |
| Urysohn infrastructure | `exists_continuousMap_one_of_isCompact_subset_isOpen` | Used in `Real.lean:385` | Gives test functions separating compact sets from open complements. |

#### What's missing

1. **Isometry proof.** The core: `‖Λ‖ = |s|(X)`.
   - Upper bound: `|∫ f ds| ≤ ‖f‖_∞ · |s|(X)` — standard.
   - Lower bound: approximate the Hahn set `P` with compact `K⁺ ⊆ P`, `K⁻ ⊆ Pᶜ` (inner regularity), then Urysohn for `f = 1` on `K⁺`, `f = -1` on `K⁻`, `‖f‖ ≤ 1`. Then `∫ f ds ≥ |s|(X) - ε`.
   - **Cannot** go through `μ⁺(X) + μ⁻(X)` unless mutual singularity is established — `|s|(X) ≤ μ⁺(X) + μ⁻(X)` may be strict.

2. **Surjectivity.** This IS the signed RMK (PR 6).

3. **`NormedAddCommGroup` on `SignedMeasure`** (PR 3). Needed for codomain.

4. **Subtype of regular signed measures.** The isomorphism is with `{s : SignedMeasure X // s.Regular}`. This subtype needs its own `NormedAddCommGroup` instance.

5. **Completeness.** Corollary of the isometry: `M(X)` with TV norm is a Banach space (inheriting completeness from the dual).

</details>
