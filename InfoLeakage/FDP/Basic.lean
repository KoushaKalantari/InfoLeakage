/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Topology.Order.Compact

/-!
# Trade-off functions and `f`-differential privacy

This file formalizes the hypothesis-testing foundations of J. Dong, A. Roth and W. J. Su,
*Gaussian differential privacy*, J. R. Stat. Soc. Ser. B 84(1), 2022
([arXiv:1905.02383](https://arxiv.org/abs/1905.02383)); result numbers follow arXiv v3.

To distinguish two distributions `P` (null) and `Q` (alternative), a randomized test
`φ : Y → [0, 1]` has type I error `α_φ = E_P[φ]` and type II error `β_φ = 1 - E_Q[φ]`. The
trade-off function `T(P, Q)(α) = inf {β_φ : α_φ ≤ α}` records the optimal type II error at each
level, and a mechanism `M` is `f`-DP if `T(M(S), M(S')) ≥ f` for all neighbouring datasets.

**Scope.** Everything is stated for a **finite output alphabet** `Y` with measurable singletons:
distributions are (probability) measures on `Y`, expectations are finite sums
`E_P[φ] = ∑_y P{y} φ(y)`, and a mechanism is a Markov kernel `M : Kernel 𝒟 Y` from datasets to
outputs (the predicates `IsFDP` and `IsEpsDeltaDP` accept any kernel; their privacy meaning, and
the principal theorems, require `[IsMarkovKernel M]`). The neighbouring relation `Adj` is an
arbitrary relation, assumed symmetric (`[Std.Symm Adj]`) where the paper's "differ in one
record" relation is used symmetrically. On a finite alphabet the infimum defining `T(P, Q)` is
attained by compactness (`exists_tradeoff_eq`), which replaces the Neyman–Pearson arguments of
the paper.

## Main definitions

* `IsRandomizedTest φ`, `typeIError P φ`, `typeIIError Q φ`: tests and their errors.
* `tradeoff P Q`: the trade-off function `T(P, Q)` (Definition 2.1).
* `IsFDP M Adj f`: `f`-differential privacy (Definition 2.3).
* `IsEpsDeltaDP M Adj ε δ`: `(ε, δ)`-differential privacy (Definition 1.1).
* `fEpsDelta ε δ`: the function `f_{ε,δ}` of `(ε, δ)`-DP (equation (5)).
* `tradeoffInv f`: the left-continuous inverse `f⁻¹` (equation (4)).
* `tradeoffConj f`: the convex conjugate `f*` of a function on `[0, 1]` (equation (8)).
* `IsKNeighbour Adj k`: `k`-neighbouring datasets (Section 2.5).

## Main statements (paper result → Lean name)

* Proposition 2.2, "only if" direction, for finite alphabets: `antitoneOn_tradeoff`,
  `convexOn_tradeoff` / `convexOn_Icc_tradeoff`, `continuousOn_tradeoff` (via the Lipschitz
  bound `exists_lipschitzOnWith_tradeoff`), `tradeoff_le_one_sub`, `tradeoff_nonneg`.
* Proposition 2.4 (symmetrization): `IsFDP.max_tradeoffInv`; Lemma A.2:
  `tradeoff_swap_eq_tradeoffInv`.
* Proposition 2.5 (`(ε, δ)`-DP iff `f_{ε,δ}`-DP): `isEpsDeltaDP_iff_isFDP`, with the pairwise form
  `fEpsDelta_le_tradeoff_iff`.
* Lemma 2.9 and Proposition 2.8 (post-processing): `tradeoff_le_tradeoff_comp`, `IsFDP.comp`.
* Proposition 2.11 (dual to primal): `forall_isEpsDeltaDP_iff_isFDP_iSup`.
* Proposition 2.12 (primal to dual), direction `⟹` only:
  `IsFDP.isEpsDeltaDP_one_add_tradeoffConj`.
* Theorem 2.14 (group privacy, `f`-DP part) and Lemma A.5: `IsFDP.group`,
  `comp_one_sub_le_tradeoff`.
* `Id` is the trade-off function of identical distributions (Section 3.1): `tradeoff_self`.

## Notes on the paper

* In the proof of Proposition 2.2 (Appendix A, convexity) the displayed inequality
  `f(tα + (1 - t)α') ≤ tα + (1 - t)α'` is a typo for `≤ t f(α) + (1 - t) f(α')`, which is what
  `convexOn_tradeoff` proves (the literal display fails, e.g. `T(P, P)(0) = 1`). The same
  proof also writes "rules achieving errors `(α, f(α))` and `(α, f(α))`", where the second pair
  should be `(α', f(α'))`.
* The direction `⟹` of Proposition 2.12 needs neither the symmetry of `f` nor `ε ≥ 0`, only
  `f ≥ 0` on `[0, 1]` and a symmetric neighbouring relation.
* On a finite alphabet, Lemma A.2 needs no continuity of `T(P, Q)`, only attainment.

## Not formalized

* The "if" direction of Proposition 2.2 (it needs distributions on `[0, 1]`).
* Everything Gaussian: Definition 2.6, equation (6), Theorem 2.7, Corollary 2.13 and the GDP part
  of Theorem 2.14 (Gaussians are not finitely supported).
* That `f_{ε,δ}` (after equation (5)) and `sup_i f_{ε_i,δ_i}` (after Proposition 2.11) are
  trade-off functions.
* Blackwell's Theorem 2.10, the direction `⟸` of Proposition 2.12, the trade-off-function
  properties of `f^S` and of `1 - (1 - f)^{∘k}`, Proposition 2.15, and Sections 3–5
  (composition, central limit theorems, subsampling, SGD).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real

namespace InformationTheory

variable {Y Z 𝒟 : Type*} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
  {m𝒟 : MeasurableSpace 𝒟}

/-! ### Tests, errors and the trade-off function -/

/-- A randomized rejection rule (test) `φ : Y → [0, 1]`: on observing `y`, the null hypothesis
is rejected with probability `φ y`. -/
def IsRandomizedTest (φ : Y → ℝ) : Prop :=
  ∀ y, φ y ∈ Icc (0 : ℝ) 1

/-- The type I error `α_φ = E_P[φ]` of a test `φ` for the null hypothesis `P`, on a finite
alphabet. It equals `E_P[φ]` only when singletons are measurable
(`[MeasurableSingletonClass Y]`, assumed by every result below); otherwise `P.real {y}` is an
outer measure. -/
noncomputable def typeIError [Fintype Y] (P : Measure Y) (φ : Y → ℝ) : ℝ :=
  ∑ y, P.real {y} * φ y

/-- The type II error `β_φ = 1 - E_Q[φ]` of a test `φ` for the alternative `Q`, on a finite
alphabet. As for `typeIError`, this is `1 - E_Q[φ]` only when singletons are measurable. -/
noncomputable def typeIIError [Fintype Y] (Q : Measure Y) (φ : Y → ℝ) : ℝ :=
  1 - ∑ y, Q.real {y} * φ y

/-- The **trade-off function** `T(P, Q)(α) = inf {β_φ : α_φ ≤ α}` (Definition 2.1 of
Dong–Roth–Su), the infimum ranging over all randomized tests `φ : Y → [0, 1]` on the finite
alphabet `Y`. It is meaningful for `α ≥ 0` (for `α < 0` no test is admissible and the value is
the junk value `0`); the paper considers `α ∈ [0, 1]`. It is `T(P, Q)` only when singletons are
measurable (`[MeasurableSingletonClass Y]`, assumed by every result below), see `typeIError`. -/
noncomputable def tradeoff [Fintype Y] (P Q : Measure Y) (α : ℝ) : ℝ :=
  ⨅ φ : {φ : Y → ℝ // IsRandomizedTest φ ∧ typeIError P φ ≤ α}, typeIIError Q φ

section IsRandomizedTest

variable {φ ψ : Y → ℝ}

lemma IsRandomizedTest.nonneg (hφ : IsRandomizedTest φ) (y : Y) : 0 ≤ φ y := (hφ y).1

lemma IsRandomizedTest.le_one (hφ : IsRandomizedTest φ) (y : Y) : φ y ≤ 1 := (hφ y).2

lemma isRandomizedTest_const {c : ℝ} (h₀ : 0 ≤ c) (h₁ : c ≤ 1) : IsRandomizedTest fun _ : Y ↦ c :=
  fun _ ↦ ⟨h₀, h₁⟩

lemma IsRandomizedTest.one_sub (hφ : IsRandomizedTest φ) : IsRandomizedTest fun y ↦ 1 - φ y :=
  fun y ↦ ⟨by linarith [hφ.le_one y], by linarith [hφ.nonneg y]⟩

lemma IsRandomizedTest.convexComb (hφ : IsRandomizedTest φ) (hψ : IsRandomizedTest ψ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsRandomizedTest fun y ↦ a * φ y + b * ψ y := fun y ↦
  ⟨by nlinarith [hφ.nonneg y, hψ.nonneg y],
    by nlinarith [hφ.nonneg y, hψ.nonneg y, hφ.le_one y, hψ.le_one y]⟩

lemma isRandomizedTest_indicator (E : Set Y) : IsRandomizedTest (E.indicator 1) := fun y ↦ by
  by_cases hy : y ∈ E <;> simp [hy]

end IsRandomizedTest

section Tradeoff

variable [Fintype Y] [MeasurableSingletonClass Y] {P Q : Measure Y} {φ ψ : Y → ℝ} {α β : ℝ}

omit [MeasurableSingletonClass Y] in
lemma typeIError_nonneg (hφ : IsRandomizedTest φ) : 0 ≤ typeIError P φ :=
  Finset.sum_nonneg fun y _ ↦ mul_nonneg measureReal_nonneg (hφ.nonneg y)

lemma sum_measureReal_mul_le_one [IsProbabilityMeasure P] (hφ : IsRandomizedTest φ) :
    ∑ y, P.real {y} * φ y ≤ 1 := by
  calc ∑ y, P.real {y} * φ y ≤ ∑ y, P.real {y} :=
        Finset.sum_le_sum fun y _ ↦ mul_le_of_le_one_right measureReal_nonneg (hφ.le_one y)
    _ = 1 := by simp

lemma typeIError_le_one [IsProbabilityMeasure P] (hφ : IsRandomizedTest φ) : typeIError P φ ≤ 1 :=
  sum_measureReal_mul_le_one hφ

lemma typeIIError_nonneg [IsProbabilityMeasure Q] (hφ : IsRandomizedTest φ) : 0 ≤ typeIIError Q φ :=
  sub_nonneg.2 (sum_measureReal_mul_le_one hφ)

lemma sum_measureReal_mul_const [IsProbabilityMeasure P] (c : ℝ) :
    ∑ y, P.real {y} * c = c := by
  rw [← Finset.sum_mul]
  simp

lemma sum_measureReal_mul_one_sub [IsProbabilityMeasure P] (φ : Y → ℝ) :
    ∑ y, P.real {y} * (1 - φ y) = 1 - ∑ y, P.real {y} * φ y := by
  simp only [mul_sub, Finset.sum_sub_distrib, sum_measureReal_mul_const]

lemma sum_measureReal_mul_indicator (P : Measure Y) [IsFiniteMeasure P] (E : Set Y) :
    ∑ y, P.real {y} * E.indicator 1 y = P.real E := by
  classical
  have h (y : Y) : P.real {y} * E.indicator 1 y = if y ∈ E.toFinset then P.real {y} else 0 := by
    by_cases hy : y ∈ E <;> simp [hy]
  simp_rw [h, Finset.sum_ite_mem, Finset.univ_inter, sum_measureReal_singleton, coe_toFinset]

omit [MeasurableSingletonClass Y] in
lemma continuous_sum_measureReal_mul (P : Measure Y) :
    Continuous fun φ : Y → ℝ ↦ ∑ y, P.real {y} * φ y := by
  fun_prop

lemma bddBelow_range_typeIIError [IsProbabilityMeasure Q] :
    BddBelow (range fun φ : {φ : Y → ℝ // IsRandomizedTest φ ∧ typeIError P φ ≤ α} ↦
      typeIIError Q φ) :=
  ⟨0, forall_mem_range.2 fun φ ↦ typeIIError_nonneg φ.2.1⟩

omit [MeasurableSingletonClass Y] in
lemma typeIError_convexComb (P : Measure Y) (φ ψ : Y → ℝ) (a b : ℝ) :
    typeIError P (fun y ↦ a * φ y + b * ψ y) = a * typeIError P φ + b * typeIError P ψ := by
  simp only [typeIError, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ by ring

omit [MeasurableSingletonClass Y] in
lemma typeIIError_convexComb (Q : Measure Y) (φ ψ : Y → ℝ) {a b : ℝ} (hab : a + b = 1) :
    typeIIError Q (fun y ↦ a * φ y + b * ψ y) = a * typeIIError Q φ + b * typeIIError Q ψ := by
  have h := typeIError_convexComb Q φ ψ a b
  simp only [typeIError] at h
  simp only [typeIIError, h]
  linear_combination -hab

/-- Any admissible test bounds the trade-off function from above. -/
lemma tradeoff_le [IsProbabilityMeasure Q] (hφ : IsRandomizedTest φ) (h : typeIError P φ ≤ α) :
    tradeoff P Q α ≤ typeIIError Q φ :=
  ciInf_le bddBelow_range_typeIIError
    (⟨φ, hφ, h⟩ : {φ : Y → ℝ // IsRandomizedTest φ ∧ typeIError P φ ≤ α})

omit [MeasurableSingletonClass Y] in
lemma le_tradeoff (hα : 0 ≤ α)
    (h : ∀ φ, IsRandomizedTest φ → typeIError P φ ≤ α → β ≤ typeIIError Q φ) :
    β ≤ tradeoff P Q α := by
  have : Nonempty {φ : Y → ℝ // IsRandomizedTest φ ∧ typeIError P φ ≤ α} :=
    ⟨⟨fun _ ↦ 0, isRandomizedTest_const le_rfl zero_le_one, by simpa [typeIError] using hα⟩⟩
  exact le_ciInf fun φ ↦ h φ φ.2.1 φ.2.2

lemma tradeoff_nonneg [IsProbabilityMeasure Q] : 0 ≤ tradeoff P Q α :=
  Real.iInf_nonneg fun φ ↦ typeIIError_nonneg φ.2.1

/-- On a finite alphabet the infimum defining `T(P, Q)(α)` is attained by some test with type I
error at most `α`: existence of a most powerful test. Theorem A.1 (the Neyman–Pearson lemma, in
its likelihood-ratio form) is not formalized. -/
theorem exists_tradeoff_eq [IsProbabilityMeasure Q] (hα : 0 ≤ α) :
    ∃ φ, IsRandomizedTest φ ∧ typeIError P φ ≤ α ∧ typeIIError Q φ = tradeoff P Q α := by
  set s : Set (Y → ℝ) := (univ.pi fun _ ↦ Icc (0 : ℝ) 1) ∩ {φ | typeIError P φ ≤ α}
  have hs : IsCompact s := (isCompact_univ_pi fun _ ↦ isCompact_Icc).inter_right
    (isClosed_le (continuous_sum_measureReal_mul P) continuous_const)
  have hne : s.Nonempty :=
    ⟨fun _ ↦ 0, fun _ _ ↦ ⟨le_rfl, zero_le_one⟩, by simpa [typeIError] using hα⟩
  obtain ⟨φ, ⟨hφ, hφα⟩, hmin⟩ := hs.exists_isMinOn hne
    (continuous_const.sub (continuous_sum_measureReal_mul Q)).continuousOn
  have hφ' : IsRandomizedTest φ := fun y ↦ hφ y (mem_univ y)
  refine ⟨φ, hφ', hφα, le_antisymm ?_ (tradeoff_le hφ' hφα)⟩
  exact le_tradeoff hα fun ψ hψ hψα ↦ hmin ⟨fun y _ ↦ hψ y, hψα⟩

/-- **Proposition 2.2** (necessity, monotonicity): `T(P, Q)` is non-increasing on `[0, ∞)`. -/
theorem antitoneOn_tradeoff [IsProbabilityMeasure Q] : AntitoneOn (tradeoff P Q) (Ici 0) := by
  intro a ha b _ hab
  obtain ⟨φ, hφ, hφa, hφT⟩ := exists_tradeoff_eq (P := P) (Q := Q) ha
  exact hφT ▸ tradeoff_le hφ (hφa.trans hab)

/-- **Proposition 2.2** (necessity, `f(α) ≤ 1 - α`): `T(P, Q)(α) ≤ 1 - α` for `α ∈ [0, 1]`,
witnessed by the blind test rejecting with probability `α`. -/
theorem tradeoff_le_one_sub [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h₀ : 0 ≤ α)
    (h₁ : α ≤ 1) : tradeoff P Q α ≤ 1 - α := by
  have h := tradeoff_le (P := P) (Q := Q) (α := α) (isRandomizedTest_const h₀ h₁) (le_of_eq ?_)
  · simpa [typeIIError, sum_measureReal_mul_const] using h
  · simp [typeIError, sum_measureReal_mul_const]

/-- **Proposition 2.2** (necessity, convexity): `T(P, Q)` is convex on `[0, ∞)`. -/
theorem convexOn_tradeoff [IsProbabilityMeasure Q] : ConvexOn ℝ (Ici 0) (tradeoff P Q) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab ↦ ?_⟩
  obtain ⟨φ, hφ, hφx, hφT⟩ := exists_tradeoff_eq (P := P) (Q := Q) hx
  obtain ⟨ψ, hψ, hψy, hψT⟩ := exists_tradeoff_eq (P := P) (Q := Q) hy
  have h := tradeoff_le (P := P) (Q := Q) (α := a • x + b • y) (hφ.convexComb hψ ha hb hab)
    (by rw [typeIError_convexComb, smul_eq_mul, smul_eq_mul]; gcongr)
  rwa [typeIIError_convexComb Q φ ψ hab, hφT, hψT] at h

/-- The trade-off function is convex on `[0, 1]`, as stated in Proposition 2.2. -/
theorem convexOn_Icc_tradeoff [IsProbabilityMeasure Q] :
    ConvexOn ℝ (Icc 0 1) (tradeoff P Q) :=
  convexOn_tradeoff.subset Icc_subset_Ici_self (convex_Icc 0 1)

/-- A linear lower bound at the origin: `T(P, Q)(α) ≥ T(P, Q)(0) - C α` for all `α ≥ 0`, with
`C = ∑_{P{y} ≠ 0} Q{y} / P{y}`. This is where finiteness of the alphabet replaces the
Neyman–Pearson limiting argument used in the paper for continuity at `0`. -/
lemma exists_tradeoff_zero_sub_mul_le [IsProbabilityMeasure Q] :
    ∃ C, 0 ≤ C ∧ ∀ α, 0 ≤ α → tradeoff P Q 0 - C * α ≤ tradeoff P Q α := by
  classical
  set c : Y → ℝ := fun y ↦ if P.real {y} = 0 then 0 else Q.real {y} / P.real {y} with hc_def
  set N : Set Y := {y | P.real {y} = 0} with hN
  have hc (y : Y) : 0 ≤ c y := by
    simp only [hc_def]
    split_ifs <;> positivity
  refine ⟨∑ y, c y, Finset.sum_nonneg fun y _ ↦ hc y,
    fun α hα ↦ le_tradeoff hα fun φ hφ hφα ↦ ?_⟩
  have h0 : tradeoff P Q 0 ≤ typeIIError Q (N.indicator 1) := by
    refine tradeoff_le (isRandomizedTest_indicator N) (le_of_eq (Finset.sum_eq_zero fun y _ ↦ ?_))
    by_cases hy : y ∈ N
    · simp only [hN, mem_ofPred_eq] at hy
      simp [hy]
    · simp [hy]
  have hP : ∀ y, P.real {y} * φ y ≤ typeIError P φ := fun y ↦
    Finset.single_le_sum (f := fun y ↦ P.real {y} * φ y)
      (fun y _ ↦ mul_nonneg measureReal_nonneg (hφ.nonneg y)) (Finset.mem_univ y)
  have hterm (y : Y) :
      Q.real {y} * φ y ≤ Q.real {y} * N.indicator 1 y + c y * typeIError P φ := by
    by_cases hy : P.real {y} = 0
    · have hyN : y ∈ N := hy
      simp only [indicator_of_mem hyN, Pi.one_apply, mul_one, hc_def, hy, ite_true, zero_mul,
        add_zero]
      exact mul_le_of_le_one_right measureReal_nonneg (hφ.le_one y)
    · have hyN : y ∉ N := hy
      simp only [indicator_of_notMem hyN, mul_zero, zero_add, hc_def, hy, ite_false]
      calc Q.real {y} * φ y = Q.real {y} / P.real {y} * (P.real {y} * φ y) := by
            field_simp
        _ ≤ Q.real {y} / P.real {y} * typeIError P φ := by gcongr; exact hP y
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) ↦ hterm y
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hCα : (∑ y, c y) * typeIError P φ ≤ (∑ y, c y) * α :=
    mul_le_mul_of_nonneg_left hφα (Finset.sum_nonneg fun y _ ↦ hc y)
  simp only [typeIIError] at h0 ⊢
  linarith

/-- On a finite alphabet, `T(P, Q)` is Lipschitz on `[0, ∞)`. -/
theorem exists_lipschitzOnWith_tradeoff [IsProbabilityMeasure Q] :
    ∃ K, LipschitzOnWith K (tradeoff P Q) (Ici 0) := by
  obtain ⟨C, hC, hT⟩ := exists_tradeoff_zero_sub_mul_le (P := P) (Q := Q)
  refine ⟨C.toNNReal, LipschitzOnWith.of_le_add_mul' C fun x hx y hy ↦ ?_⟩
  rcases le_total y x with hxy | hxy
  · exact (antitoneOn_tradeoff hy hx hxy).trans (le_add_of_nonneg_right (by positivity))
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy)]
  have hx0 : 0 ≤ x := hx
  obtain rfl | hy0 := (show (0 : ℝ) ≤ y from hy).eq_or_lt
  · obtain rfl : x = 0 := le_antisymm hxy hx0
    simp
  set a := (y - x) / y with ha_def
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.2 hxy) hy0.le
  have hb : x / y = 1 - a := by rw [ha_def]; field_simp; ring
  have h := (convexOn_tradeoff (P := P) (Q := Q)).2 (mem_Ici.2 le_rfl) hy ha
    (div_nonneg hx0 hy0.le) (by rw [hb]; ring)
  have hx' : a • (0 : ℝ) + (x / y) • y = x := by
    simp only [smul_eq_mul, mul_zero, zero_add]; field_simp
  rw [hx', smul_eq_mul, smul_eq_mul, hb] at h
  have h2 : a * (tradeoff P Q 0 - tradeoff P Q y) ≤ a * (C * y) :=
    mul_le_mul_of_nonneg_left (by linarith [hT y hy]) ha
  have e1 : a * (C * y) = C * (y - x) := by rw [ha_def]; field_simp
  nlinarith

/-- **Proposition 2.2** (necessity, continuity): `T(P, Q)` is continuous on `[0, ∞)`, in
particular on `[0, 1]`. -/
theorem continuousOn_tradeoff [IsProbabilityMeasure Q] : ContinuousOn (tradeoff P Q) (Ici 0) :=
  exists_lipschitzOnWith_tradeoff.choose_spec.continuousOn

/-- `T(P, Q)(1) = 0`. -/
lemma tradeoff_one [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : tradeoff P Q 1 = 0 :=
  le_antisymm (by simpa using tradeoff_le_one_sub (P := P) (Q := Q) zero_le_one le_rfl)
    tradeoff_nonneg

/-- The trade-off function of two identical distributions is `Id(α) = 1 - α` (Section 3.1). -/
theorem tradeoff_self [IsProbabilityMeasure P] (h₀ : 0 ≤ α) (h₁ : α ≤ 1) :
    tradeoff P P α = 1 - α := by
  refine le_antisymm (tradeoff_le_one_sub h₀ h₁) (le_tradeoff h₀ fun φ _ hφα ↦ ?_)
  simp only [typeIError] at hφα
  simp only [typeIIError]
  linarith

/-- The left-continuous inverse `f⁻¹(α) = inf {t ∈ [0, 1] : f(t) ≤ α}`, equation (4) of
Dong–Roth–Su. It is defined for every `f : ℝ → ℝ` and `α : ℝ`, but it is the paper's inverse
only for a trade-off function `f` and a level `α ∈ [0, 1]`.

**Empty-set convention.** When no `t ∈ [0, 1]` has `f t ≤ α`, the infimum is over the empty
set and Lean returns `sInf ∅ = 0`, which has no inverse interpretation (e.g. `f ≡ 1`, `α = 0`
gives `0`). The results using `tradeoffInv` (`tradeoff_swap_eq_tradeoffInv`,
`tradeoffInv_mono`, `IsFDP.max_tradeoffInv`) carry hypotheses that keep the set nonempty in
their intended applications. -/
noncomputable def tradeoffInv (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  sInf {t | t ∈ Icc (0 : ℝ) 1 ∧ f t ≤ α}

/-- **Lemma A.2** (finite `Y`): `T(Q, P) = T(P, Q)⁻¹` on `[0, ∞)`. The proof only uses
that the infima are attained (no continuity is needed). -/
theorem tradeoff_swap_eq_tradeoffInv [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hβ : 0 ≤ β) : tradeoff Q P β = tradeoffInv (tradeoff P Q) β := by
  have hbdd : BddBelow {t | t ∈ Icc (0 : ℝ) 1 ∧ tradeoff P Q t ≤ β} := ⟨0, fun t ht ↦ ht.1.1⟩
  refine le_antisymm (le_csInf ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [tradeoff_one]; exact hβ⟩ ?_) ?_
  · rintro t ⟨ht, htβ⟩
    obtain ⟨φ, hφ, hφt, hφT⟩ := exists_tradeoff_eq (P := P) (Q := Q) ht.1
    have h := tradeoff_le (P := Q) (Q := P) (α := β) hφ.one_sub (by
      rw [typeIError, sum_measureReal_mul_one_sub]
      rw [← hφT, typeIIError] at htβ
      exact htβ)
    rw [typeIIError, sum_measureReal_mul_one_sub] at h
    simp only [typeIError] at hφt
    linarith
  · obtain ⟨ψ, hψ, hψβ, hψT⟩ := exists_tradeoff_eq (P := Q) (Q := P) hβ
    refine (csInf_le hbdd ⟨⟨typeIIError_nonneg hψ, ?_⟩, ?_⟩).trans_eq hψT
    · have := typeIError_nonneg (P := P) hψ
      simp only [typeIIError, typeIError] at this ⊢
      linarith
    · refine (tradeoff_le hψ.one_sub ?_).trans ?_
      · rw [typeIError, sum_measureReal_mul_one_sub, typeIIError]
      · rw [typeIIError, sum_measureReal_mul_one_sub]
        simp only [typeIError] at hψβ
        linarith

end Tradeoff

/-! ### Post-processing -/

section PostProcessing

variable [Fintype Y] [MeasurableSingletonClass Y] [Fintype Z] [MeasurableSingletonClass Z]
  {P Q : Measure Y} {α : ℝ}

omit [Fintype Z] in
lemma measureReal_comp_singleton (Proc : Kernel Y Z) [IsMarkovKernel Proc] (P : Measure Y)
    [IsFiniteMeasure P] (z : Z) :
    (Proc ∘ₘ P).real {z} = ∑ y, (Proc y).real {z} * P.real {y} := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton z) Proc.measurable.aemeasurable,
    lintegral_fintype, ENNReal.toReal_sum fun y _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp [measureReal_def, ENNReal.toReal_mul]

/-- **Lemma 2.9** (post-processing for trade-off functions, finite `Y` and `Z`): for every
Markov kernel `Proc`, `T(Proc(P), Proc(Q)) ≥ T(P, Q)` on `[0, ∞)`. -/
theorem tradeoff_le_tradeoff_comp [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Proc : Kernel Y Z) [IsMarkovKernel Proc] (hα : 0 ≤ α) :
    tradeoff P Q α ≤ tradeoff (Proc ∘ₘ P) (Proc ∘ₘ Q) α := by
  refine le_tradeoff hα fun ψ hψ hψα ↦ ?_
  set φ : Y → ℝ := fun y ↦ ∑ z, (Proc y).real {z} * ψ z with hφ_def
  have hφ : IsRandomizedTest φ := fun y ↦
    ⟨Finset.sum_nonneg fun z _ ↦ mul_nonneg measureReal_nonneg (hψ.nonneg z),
      sum_measureReal_mul_le_one hψ⟩
  have key (R : Measure Y) [IsFiniteMeasure R] :
      ∑ z, (Proc ∘ₘ R).real {z} * ψ z = ∑ y, R.real {y} * φ y := by
    simp only [measureReal_comp_singleton, Finset.sum_mul, hφ_def, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have h := tradeoff_le (P := P) (Q := Q) (α := α) hφ (by rw [typeIError, ← key]; exact hψα)
  rw [typeIIError, ← key] at h
  exact h

end PostProcessing

/-! ### `f`-differential privacy -/

/-- **`f`-differential privacy** (Definition 2.3 of Dong–Roth–Su): a mechanism `M`, given as a
Markov kernel from datasets `𝒟` to a finite output alphabet `Y`, is `f`-DP for the neighbouring
relation `Adj` if `T(M(S), M(S')) ≥ f` on `[0, 1]` for all neighbouring `S, S'`.

The paper takes `f` to be a trade-off function and `Adj` to be "differ in exactly one record";
here `f : ℝ → ℝ` and `Adj` are arbitrary, and the results that need the neighbouring relation to
be symmetric assume it. As for `tradeoff`, this is the paper's notion only when singletons of
`Y` are measurable (`[MeasurableSingletonClass Y]`, assumed by every result below).

**Markov requirement (documented, not enforced).** The predicate accepts an arbitrary `Kernel`,
and a Mathlib `Kernel` need not be Markov. It is an unrestricted algebraic extension whose
privacy interpretation requires `[IsMarkovKernel M]`: e.g. for the zero kernel every
`T(0, 0)(α)` with `α ≥ 0` is `1`, so the zero kernel is `f`-DP for every `f ≤ 1` on `[0, 1]`,
although it is no randomized mechanism; for infinite measures `toReal ∞ = 0` also distorts
the errors. The principal theorems below (`IsFDP.comp`, `isEpsDeltaDP_iff_isFDP`,
`IsFDP.max_tradeoffInv`, `IsFDP.group`, …) assume `[IsMarkovKernel M]`. -/
def IsFDP [Fintype Y] (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃S S'⦄, Adj S S' → ∀ α ∈ Icc (0 : ℝ) 1, f α ≤ tradeoff (M S) (M S') α

section FDP

variable [Fintype Y] [MeasurableSingletonClass Y] {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop}
  {f g : ℝ → ℝ}

omit [MeasurableSingletonClass Y] in
lemma IsFDP.mono (h : IsFDP M Adj f) (hgf : ∀ α ∈ Icc (0 : ℝ) 1, g α ≤ f α) : IsFDP M Adj g :=
  fun _ _ hS α hα ↦ (hgf α hα).trans (h hS α hα)

/-- **Proposition 2.8** (post-processing): if `M` is `f`-DP, so is `Proc ∘ M` for every Markov
kernel `Proc` into a finite alphabet. -/
theorem IsFDP.comp [Fintype Z] [MeasurableSingletonClass Z] [IsMarkovKernel M]
    (h : IsFDP M Adj f) (Proc : Kernel Y Z) [IsMarkovKernel Proc] : IsFDP (Proc ∘ₖ M) Adj f :=
  fun S S' hS α hα ↦ by
    rw [Kernel.comp_apply, Kernel.comp_apply]
    exact (h hS α hα).trans (tradeoff_le_tradeoff_comp Proc hα.1)

end FDP

/-! ### `(ε, δ)`-differential privacy as `f_{ε,δ}`-DP -/

/-- **`(ε, δ)`-differential privacy** (Definition 1.1 of Dong–Roth–Su): for all neighbouring
`S, S'` and every event `E`, `P[M(S) ∈ E] ≤ e^ε P[M(S') ∈ E] + δ`. On a finite alphabet with
measurable singletons every set is an event.

**Markov requirement (documented, not enforced).** As for `IsFDP`, `M` is an arbitrary
`Kernel`, not necessarily Markov, so this is an unrestricted algebraic extension whose privacy
interpretation requires `[IsMarkovKernel M]`: e.g. the zero kernel satisfies
`IsEpsDeltaDP 0 Adj 0 0`, and for infinite measures `Measure.real` reads `∞` as `0`. Every
result below relating it to `f`-DP assumes `[IsMarkovKernel M]`. -/
def IsEpsDeltaDP (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (ε δ : ℝ) : Prop :=
  ∀ ⦃S S'⦄, Adj S S' → ∀ E : Set Y, (M S).real E ≤ exp ε * (M S').real E + δ

/-- The function `f_{ε,δ}(α) = max {0, 1 - δ - e^ε α, e^{-ε} (1 - δ - α)}` of `(ε, δ)`-DP,
equation (5) of Dong–Roth–Su. (The paper notes it is a trade-off function; this is not
formalized.) -/
noncomputable def fEpsDelta (ε δ α : ℝ) : ℝ :=
  max 0 (max (1 - δ - exp ε * α) (exp (-ε) * (1 - δ - α)))

section EpsDelta

variable [Fintype Y] [MeasurableSingletonClass Y] {P Q : Measure Y} {φ : Y → ℝ} {ε δ : ℝ}

/-- An `(ε, δ)` inequality between two measures on all events extends to all randomized tests:
`E_P[φ] ≤ e^ε E_Q[φ] + δ`. -/
lemma sum_mul_le_of_forall_measureReal_le [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ E : Set Y, P.real E ≤ exp ε * Q.real E + δ) (hφ : IsRandomizedTest φ) :
    ∑ y, P.real {y} * φ y ≤ exp ε * ∑ y, Q.real {y} * φ y + δ := by
  set A : Set Y := {y | exp ε * Q.real {y} < P.real {y}}
  have hterm (y : Y) : P.real {y} * φ y - exp ε * (Q.real {y} * φ y) ≤
      P.real {y} * A.indicator 1 y - exp ε * (Q.real {y} * A.indicator 1 y) := by
    by_cases hy : y ∈ A
    · have hy' : exp ε * Q.real {y} < P.real {y} := hy
      simp only [indicator_of_mem hy, Pi.one_apply, mul_one]
      nlinarith [hφ.le_one y]
    · have hy' : P.real {y} ≤ exp ε * Q.real {y} := not_lt.1 hy
      simp only [indicator_of_notMem hy, mul_zero, sub_zero]
      nlinarith [hφ.nonneg y]
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) ↦ hterm y
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_measureReal_mul_indicator] at hsum
  linarith [h A]

/-- If `T(P, Q)` lies above the line `1 - δ - e^ε α` on `[0, 1]`, then
`Q(E) ≤ e^ε P(E) + δ` for every event `E`. -/
lemma measureReal_le_of_forall_le_tradeoff [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ α ∈ Icc (0 : ℝ) 1, 1 - δ - exp ε * α ≤ tradeoff P Q α) (E : Set Y) :
    Q.real E ≤ exp ε * P.real E + δ := by
  have h₁ := (h (P.real E) ⟨measureReal_nonneg, measureReal_le_one⟩).trans
    (tradeoff_le (isRandomizedTest_indicator E) (sum_measureReal_mul_indicator P E).le)
  rw [typeIIError, sum_measureReal_mul_indicator] at h₁
  linarith

/-- If `T(P, Q)` lies above the line `e^{-ε} (1 - δ - α)` on `[0, 1]`, then
`P(E) ≤ e^ε Q(E) + δ` for every event `E`. -/
lemma measureReal_le_of_forall_le_tradeoff' [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ α ∈ Icc (0 : ℝ) 1, exp (-ε) * (1 - δ - α) ≤ tradeoff P Q α) (E : Set Y) :
    P.real E ≤ exp ε * Q.real E + δ := by
  have hE : MeasurableSet E := (toFinite E).measurableSet
  have h₁ := (h (P.real Eᶜ) ⟨measureReal_nonneg, measureReal_le_one⟩).trans
    (tradeoff_le (isRandomizedTest_indicator Eᶜ) (sum_measureReal_mul_indicator P Eᶜ).le)
  rw [typeIIError, sum_measureReal_mul_indicator, probReal_compl_eq_one_sub hE,
    probReal_compl_eq_one_sub hE, exp_neg, inv_mul_le_iff₀ (exp_pos ε)] at h₁
  linarith

/-- The pairwise form of Proposition 2.5: `T(P, Q) ≥ f_{ε,δ}` on `[0, 1]` iff
`P(E) ≤ e^ε Q(E) + δ` and `Q(E) ≤ e^ε P(E) + δ` for every event `E`. -/
theorem fEpsDelta_le_tradeoff_iff [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (∀ α ∈ Icc (0 : ℝ) 1, fEpsDelta ε δ α ≤ tradeoff P Q α) ↔
      ∀ E : Set Y, P.real E ≤ exp ε * Q.real E + δ ∧ Q.real E ≤ exp ε * P.real E + δ := by
  refine ⟨fun h E ↦ ⟨measureReal_le_of_forall_le_tradeoff' (fun α hα ↦ ?_) E,
    measureReal_le_of_forall_le_tradeoff (fun α hα ↦ ?_) E⟩, fun h α hα ↦ ?_⟩
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (h α hα))
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (h α hα))
  refine le_tradeoff hα.1 fun φ hφ hφα ↦ max_le (typeIIError_nonneg hφ) (max_le ?_ ?_)
  · have := sum_mul_le_of_forall_measureReal_le (fun E ↦ (h E).2) hφ
    have : exp ε * typeIError P φ ≤ exp ε * α := by gcongr
    simp only [typeIIError, typeIError] at *
    linarith
  · have h₁ := sum_mul_le_of_forall_measureReal_le (fun E ↦ (h E).1) hφ.one_sub
    rw [sum_measureReal_mul_one_sub, sum_measureReal_mul_one_sub] at h₁
    rw [exp_neg, inv_mul_le_iff₀ (exp_pos ε), typeIIError]
    simp only [typeIError] at hφα
    linarith

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop}

/-- **Proposition 2.5**, direction `f_{ε,δ}`-DP `⟹` `(ε, δ)`-DP (no symmetry needed). -/
theorem IsFDP.isEpsDeltaDP [IsMarkovKernel M] (h : IsFDP M Adj (fEpsDelta ε δ)) :
    IsEpsDeltaDP M Adj ε δ :=
  fun _ _ hS E ↦ (fEpsDelta_le_tradeoff_iff.1 (h hS) E).1

/-- **Proposition 2.5** (Wasserman–Zhou; finite `Y`): for a symmetric neighbouring relation, a
mechanism is `(ε, δ)`-DP iff it is `f_{ε,δ}`-DP. -/
theorem isEpsDeltaDP_iff_isFDP [IsMarkovKernel M] [Std.Symm Adj] :
    IsEpsDeltaDP M Adj ε δ ↔ IsFDP M Adj (fEpsDelta ε δ) :=
  ⟨fun h _ _ hS ↦ fEpsDelta_le_tradeoff_iff.2 fun E ↦ ⟨h hS E, h (Std.Symm.symm _ _ hS) E⟩,
    IsFDP.isEpsDeltaDP⟩

end EpsDelta

/-! ### The primal–dual perspective -/

section PrimalDual

variable [Fintype Y] [MeasurableSingletonClass Y] {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop}
  {f : ℝ → ℝ}

lemma fEpsDelta_le_one {ε δ α : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hα : 0 ≤ α) :
    fEpsDelta ε δ α ≤ 1 := by
  have h₁ : 0 < exp (-ε) := exp_pos _
  have h₂ : exp (-ε) ≤ 1 := exp_le_one_iff.2 (neg_nonpos.2 hε)
  refine max_le zero_le_one (max_le (by nlinarith [exp_pos ε]) ?_)
  rcases le_total 0 (1 - δ - α) with h | h
  · nlinarith
  · nlinarith

/-- **Proposition 2.11** (dual to primal): for a symmetric neighbouring relation and any family
`(ε_i, δ_i)` with `ε_i, δ_i ≥ 0`, a mechanism is `(ε_i, δ_i)`-DP for all `i` iff it is `f`-DP
with `f = sup_i f_{ε_i, δ_i}` (finite `Y`). (For an empty family both sides hold trivially.)
That this function is a symmetric trade-off function, remarked in the paper, is not
formalized. -/
theorem forall_isEpsDeltaDP_iff_isFDP_iSup [IsMarkovKernel M] [Std.Symm Adj] {ι : Type*}
    (ε δ : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (hδ : ∀ i, 0 ≤ δ i) :
    (∀ i, IsEpsDeltaDP M Adj (ε i) (δ i)) ↔ IsFDP M Adj fun α ↦ ⨆ i, fEpsDelta (ε i) (δ i) α := by
  refine ⟨fun h S S' hS α hα ↦ Real.iSup_le (fun i ↦ (isEpsDeltaDP_iff_isFDP.1 (h i)) hS α hα)
    tradeoff_nonneg, fun h i ↦ (h.mono fun α hα ↦ ?_).isEpsDeltaDP⟩
  exact le_ciSup ⟨1, forall_mem_range.2 fun j ↦ fEpsDelta_le_one (hε j) (hδ j) hα.1⟩ i

/-- The convex conjugate `f*(y) = sup_{x ∈ [0, 1]} (y x - f(x))` of a function on `[0, 1]`
(extended by `+∞` outside `[0, 1]`), equation (8) of Dong–Roth–Su. If the family
`x ↦ y x - f(x)` is unbounded above on `[0, 1]`, this is the junk value `0` where the paper has
`+∞`; in Proposition 2.12 (`IsFDP.isEpsDeltaDP_one_add_tradeoffConj`) the hypothesis `f ≥ 0` on
`[0, 1]` bounds the family above (by `0` for `y ≤ 0`). -/
noncomputable def tradeoffConj (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ⨆ x : Icc (0 : ℝ) 1, (y * x - f x)

/-- **Proposition 2.12** (primal to dual), direction `⟹`: for a symmetric neighbouring relation,
an `f`-DP mechanism with `f ≥ 0` on `[0, 1]` is `(ε, 1 + f*(-e^ε))`-DP for every `ε`.

The paper assumes `f` is a symmetric trade-off function and `ε ≥ 0`; neither is needed for this
direction. The converse direction (which needs symmetry and the biconjugation `f = f**`) is not
formalized. -/
theorem IsFDP.isEpsDeltaDP_one_add_tradeoffConj [IsMarkovKernel M] [Std.Symm Adj]
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) (h : IsFDP M Adj f) (ε : ℝ) :
    IsEpsDeltaDP M Adj ε (1 + tradeoffConj f (-exp ε)) := by
  have hline : ∀ α ∈ Icc (0 : ℝ) 1, 1 - (1 + tradeoffConj f (-exp ε)) - exp ε * α ≤ f α := by
    intro α hα
    have hbdd : BddAbove (range fun x : Icc (0 : ℝ) 1 ↦ -exp ε * x - f x) :=
      ⟨0, forall_mem_range.2 fun x ↦ by nlinarith [exp_pos ε, x.2.1, hf x x.2]⟩
    have := le_ciSup hbdd ⟨α, hα⟩
    simp only [tradeoffConj] at this ⊢
    linarith
  intro S S' hS E
  exact measureReal_le_of_forall_le_tradeoff
    (fun α hα ↦ (hline α hα).trans (h (Std.Symm.symm _ _ hS) α hα)) E

lemma tradeoffInv_mono {g : ℝ → ℝ} {α : ℝ} (hfg : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ g t)
    (hne : ∃ t ∈ Icc (0 : ℝ) 1, g t ≤ α) : tradeoffInv f α ≤ tradeoffInv g α := by
  obtain ⟨t, ht, hgt⟩ := hne
  exact csInf_le_csInf ⟨0, fun t ht ↦ ht.1.1⟩ ⟨t, ht, hgt⟩
    fun t ht ↦ ⟨ht.1, (hfg t ht.1).trans ht.2⟩

/-- **Proposition 2.4** (symmetrization): for a symmetric neighbouring relation, an `f`-DP
mechanism is `f^S`-DP with `f^S = max {f, f⁻¹}`. (That `f^S` is a symmetric trade-off function
is not formalized.) -/
theorem IsFDP.max_tradeoffInv [IsMarkovKernel M] [Std.Symm Adj] (h : IsFDP M Adj f) :
    IsFDP M Adj fun α ↦ max (f α) (tradeoffInv f α) := by
  intro S S' hS α hα
  refine max_le (h hS α hα) ?_
  rw [tradeoff_swap_eq_tradeoffInv hα.1]
  exact tradeoffInv_mono (h (Std.Symm.symm _ _ hS))
    ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [tradeoff_one]; exact hα.1⟩

end PrimalDual

/-! ### Group privacy -/

/-- `S` and `S'` are `k`-neighbours (Section 2.5 of Dong–Roth–Su): they are joined by a chain
`S = S₀, S₁, …, S_k = S'` in which consecutive datasets are neighbouring or identical. -/
inductive IsKNeighbour (Adj : 𝒟 → 𝒟 → Prop) : ℕ → 𝒟 → 𝒟 → Prop
  | zero (S : 𝒟) : IsKNeighbour Adj 0 S S
  | succ {k : ℕ} {S T U : 𝒟} :
      IsKNeighbour Adj k S T → Adj T U ∨ T = U → IsKNeighbour Adj (k + 1) S U

section GroupPrivacy

variable [Fintype Y] [MeasurableSingletonClass Y] {P Q R : Measure Y} {f g : ℝ → ℝ}

/-- **Lemma A.5** (finite `Y`): if `T(P, Q) ≥ f` and `T(Q, R) ≥ g` on `[0, 1]` with `g`
non-increasing, then `T(P, R)(α) ≥ g(1 - f(α))` wherever `f(α) ≥ 0`. -/
theorem comp_one_sub_le_tradeoff [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] (hg : AntitoneOn g (Icc 0 1))
    (hPQ : ∀ α ∈ Icc (0 : ℝ) 1, f α ≤ tradeoff P Q α)
    (hQR : ∀ α ∈ Icc (0 : ℝ) 1, g α ≤ tradeoff Q R α) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (hf : 0 ≤ f α) : g (1 - f α) ≤ tradeoff P R α := by
  obtain ⟨φ, hφ, hφα, hφT⟩ := exists_tradeoff_eq (P := P) (Q := R) hα.1
  have ha₀ := typeIError_nonneg (P := Q) hφ
  have ha₁ := typeIError_le_one (P := Q) hφ
  have h₁ : f α ≤ 1 - typeIError Q φ := (hPQ α hα).trans (tradeoff_le hφ hφα)
  calc g (1 - f α) ≤ g (typeIError Q φ) :=
        hg ⟨ha₀, ha₁⟩ ⟨by linarith, by linarith⟩ (by linarith)
    _ ≤ tradeoff Q R (typeIError Q φ) := hQR _ ⟨ha₀, ha₁⟩
    _ ≤ typeIIError R φ := tradeoff_le hφ le_rfl
    _ = tradeoff P R α := hφT

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop}

/-- **Theorem 2.14** (group privacy, `f`-DP part; finite `Y`): if `M` is `f`-DP for a function
`f` with the trade-off-function properties used in the proof (`f` maps `[0, 1]` into `[0, 1]`,
is non-increasing and satisfies `f(x) ≤ 1 - x`), then `T(M(S), M(S')) ≥ 1 - (1 - f)^{∘k}` on
`[0, 1]` for all `k`-neighbours `S, S'`. The Gaussian part (`μ`-GDP gives `kμ`-GDP) is not
formalized. -/
theorem IsFDP.group [IsMarkovKernel M] (h : IsFDP M Adj f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc (0 : ℝ) 1) (hfa : AntitoneOn f (Icc 0 1))
    (hf₁ : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ 1 - x) {k : ℕ} {S S' : 𝒟}
    (hSS' : IsKNeighbour Adj k S S') :
    ∀ α ∈ Icc (0 : ℝ) 1, 1 - (fun x ↦ 1 - f x)^[k] α ≤ tradeoff (M S) (M S') α := by
  have hmaps (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1, (fun x ↦ 1 - f x)^[n] x ∈ Icc (0 : ℝ) 1 := by
    induction n with
    | zero => exact fun x hx ↦ hx
    | succ n ih =>
      intro x hx
      have := hf _ (ih x hx)
      rw [Function.iterate_succ_apply']
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
  induction hSS' with
  | zero S =>
    intro α hα
    simp [tradeoff_self hα.1 hα.2]
  | @succ n _ _ _ _ hTU ih =>
    intro α hα
    simp only [Function.iterate_succ_apply', sub_sub_cancel]
    rcases hTU with hTU | rfl
    · have := comp_one_sub_le_tradeoff hfa ih (h hTU) hα
        (by linarith [(hmaps n α hα).2])
      simpa only [sub_sub_cancel] using this
    · exact (hf₁ _ (hmaps n α hα)).trans (ih α hα)

end GroupPrivacy

end InformationTheory
