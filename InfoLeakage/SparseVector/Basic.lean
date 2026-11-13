/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.DP.Laplace
public import InfoLeakage.ForMathlib.MeasurableSum
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Report Noisy Max and the sparse vector technique

We formalize two selection mechanisms with continuous Laplace noise and finite outputs, following
C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Found. Trends Theor.
Comput. Sci. 9(3–4), 2014 (result numbers refer to this book), and M. Lyu, D. Su and N. Li,
*Understanding the sparse vector technique for differential privacy*, PVLDB 10(6), 2017,
arXiv:1603.01699 (v2).

* **Report Noisy Max** (Section 3.3): add i.i.d. `Lap(1/ε)` noise to `m` counting queries and
  release only the index of the largest noisy count.
* **AboveThreshold** (Section 3.6, Algorithm 1): compare noisy query answers `f_i(x) + Lap(4/ε)`
  with a noisy threshold `T + Lap(2/ε)` and halt at the first query above it.
* A variant without noise on the query answers (Alg. 5 of Lyu–Su–Li, from Stoddard–Chen–
  Machanavajjhala 2014), which Lyu–Su–Li show is not `ε'`-DP for any `ε'`.

Privacy is pure DP, `IsEpsDP` (`IsEpsDeltaDP` with `δ = 0`), for an arbitrary neighbouring
relation; datasets live in an arbitrary measurable space, the noise is the Laplace distribution
`laplaceMeasure` on `ℝ`, and the outputs are finite.

## Main definitions

* `noisyArgmax y`: the index of a largest coordinate of `y : ι → ℝ` (smallest such index).
* `reportNoisyMax c b`: `x ↦ noisyArgmax (c(x) + (Y_i)_i)` with `Y_i` i.i.d. `Lap(b)`.
* `countingQuery P x`: the number of records of the histogram `x : X → ℕ` that satisfy `P`.
* `firstAbove t y`: the transcript of AboveThreshold given the noisy threshold `t` and noisy
  answers `y`: `Sum.inl k` for "`⊥` before `k`, `⊤` at `k`, halt", `Sum.inr ()` for "all `⊥`".
* `aboveThreshold f T b₁ b₂`: AboveThreshold with threshold noise `Lap(b₁)` and query noise
  `Lap(b₂)`.
* `svtWithoutQueryNoise q T b`: Alg. 5 of Lyu–Su–Li (no noise on the query answers, no cutoff).

## Main statements (source result → Lean name)

* Dwork–Roth, Claim 3.9 (Report Noisy Max is `(ε, 0)`-DP for counting queries):
  `isEpsDP_reportNoisyMax_countingQuery`; general form for any scale `b ≥ 1/ε` and queries whose
  changes `c(x)_i - c(x')_i` vary by at most `1` across `i`: `isEpsDP_reportNoisyMax_of_le`.
* Dwork–Roth, Theorem 3.23 (AboveThreshold is `(ε, 0)`-DP), non-adaptive case (a fixed finite
  query sequence; deterministic analysts reduce to it, randomized ones are not covered):
  `isEpsDP_aboveThreshold`; this is also Theorem 2 of Lyu–Su–Li (their Alg. 1) for `c = 1`,
  `Δ = 1` and a single threshold. General form `isEpsDP_aboveThreshold_of_le`:
  `(ε₁ + ε₂)`-DP when `1 ≤ ε₁ b₁` and `2 ≤ ε₂ b₂`; with `b₁ = 1/ε₁`, `b₂ = 2/ε₂` and an arbitrary
  split `(ε₁, ε₂)` this is Theorem 4 of Lyu–Su–Li (their Alg. 7) for `c = 1`, `ε₃ = 0`, `Δ = 1`,
  a single threshold and a finite query sequence.
* Lyu–Su–Li, Theorem 3 (Alg. 5 is not `ε'`-DP for any `ε'`), with their counterexample:
  `not_isEpsDP_svtWithoutQueryNoise`.

## Implementation notes

* Both privacy proofs are shift arguments on densities. For Report Noisy Max we shift the whole
  noisy vector at once (`SparseVector.withDensity_noisyArgmax_le`): moving the noisy answers by
  `c(x') - c(x) + e_i` can only increase the lead of `i`, and costs `e^ε` in density. This
  replaces Dwork–Roth's conditioning on `r_{-i}`. For AboveThreshold we integrate over the noisy
  threshold last, as in Lyu–Su–Li's proof: given the threshold, the event "the transcript is
  `o`" is a box (`SparseVector.firstAbove_preimage`), and shifting the threshold by `1` changes
  each factor by at most `e^{ε₂}` at the `⊤`-query and not at all elsewhere.
* Ties in the noisy maximum (probability zero) are broken towards the smallest index. The
  outputs `ι ⊕ Unit` of AboveThreshold encode the transcripts `⊥^{k-1} ⊤` and `⊥^m`.
* Adaptivity: Dwork–Roth allow an adaptively chosen stream of queries. We treat the
  non-adaptive case of a fixed finite sequence (a finite stream is within the book's setting).
  Before halting all answers are `⊥`, so a deterministic adaptive analyst asks a fixed sequence
  on the only path that matters and reduces to this case; randomized analysts are not
  covered.

## Notes on the paper

* Dwork–Roth, proof of Claim 3.9 (Section 3.3, pp. 35–37): `r* = min_{r_i} : c_i + r_i > c_j + r_j
  ∀ j ≠ i` is an infimum, not a minimum (the set is an open half-line), so "`i` is the output iff
  `r_i ≥ r*`" should read `r_i > r*`. This is immaterial (`P[r_i = r*] = 0`); the claim is true.
* Dwork–Roth, proof of Theorem 3.23 (Section 3.6, pp. 57–58): the proof only treats outputs of
  the form `⊥^{k-1} ⊤`. For a finite stream of `m` queries the output `⊥^m` (no query above the
  threshold) also occurs, and is not covered. It follows from the same argument with the
  threshold shift alone (as in Lemma 1 of Lyu–Su–Li); the theorem is true and our
  `isEpsDP_aboveThreshold` covers all outputs.

## Not formalized

* Accuracy (Theorems 3.24 and later), `Sparse` with `c > 1` positive answers, NumericSparse,
  Lyu–Su–Li's Algs. 1 and 7 for `c > 1` or `ε₃ > 0`, their monotone-query refinement, and the
  other non-private variants (Algs. 3, 4, 6). General sensitivity `Δ` and per-query thresholds
  `T_i` are not stated separately; they follow by the trivial rescaling `r_i = (q_i - T_i)/Δ`
  of the queries (cf. Lyu–Su–Li's footnote on `r_i = q_i - T_i`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace InformationTheory

namespace SparseVector

/-- Translating the argument of a set by `v` amounts to translating the density by `-v`: for a
right-invariant measure `μ`, `(μ.withDensity p) {y | y + v ∈ A} = (μ.withDensity (p (· - v))) A`. -/
lemma withDensity_preimage_add {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    {μ : Measure G} [μ.IsAddRightInvariant] (p : G → ℝ≥0∞) (v : G) {A : Set G}
    (hA : MeasurableSet A) :
    μ.withDensity p ((· + v) ⁻¹' A) = μ.withDensity (fun z ↦ p (z - v)) A := by
  rw [withDensity_apply _ (hA.preimage (measurable_add_const v)), withDensity_apply _ hA,
    ← lintegral_indicator (hA.preimage (measurable_add_const v)), ← lintegral_indicator hA,
    ← lintegral_add_right_eq_self (fun z ↦ A.indicator (fun z ↦ p (z - v)) z) v]
  congr 1
  ext y
  simp only [Set.indicator, add_sub_cancel_right]
  rfl

end SparseVector

/-! ### The noisy argmax -/

section Argmax

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]

omit [LinearOrder ι] in
/-- Some coordinate of `y` is a largest one. -/
lemma SparseVector.filter_forall_le_nonempty (y : ι → ℝ) :
    (Finset.univ.filter fun i ↦ ∀ j, y j ≤ y i).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, fun j ↦ hi j (Finset.mem_univ j)⟩⟩

/-- The index of the largest coordinate of `y : ι → ℝ`, ties broken towards the smallest index.
(Dwork–Roth ignore ties, which have probability zero under continuous noise.) -/
noncomputable def noisyArgmax (y : ι → ℝ) : ι :=
  (Finset.univ.filter fun i ↦ ∀ j, y j ≤ y i).min' (SparseVector.filter_forall_le_nonempty y)

/-- `noisyArgmax y = i` iff `y i` is a largest coordinate and every smaller index has a strictly
smaller coordinate. -/
lemma noisyArgmax_eq_iff {y : ι → ℝ} {i : ι} :
    noisyArgmax y = i ↔ (∀ j, y j ≤ y i) ∧ ∀ j < i, y j < y i := by
  have hmem := Finset.min'_mem _ (SparseVector.filter_forall_le_nonempty y)
  rw [Finset.mem_filter] at hmem
  constructor
  · rintro rfl
    refine ⟨hmem.2, fun j hj ↦ lt_of_not_ge fun hji ↦ hj.not_ge ?_⟩
    exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ j,
      fun k ↦ (hmem.2 k).trans hji⟩)
  · rintro ⟨h₁, h₂⟩
    refine le_antisymm (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ i, h₁⟩)) ?_
    exact le_of_not_gt fun hlt ↦ (h₂ _ hlt).not_ge (hmem.2 i)

/-- If `i` is the noisy argmax of `y` and the lead `y' i - y' j` of `i` over every other index
is at least its lead `y i - y j` in `y`, then `i` is also the noisy argmax of `y'`. -/
lemma noisyArgmax_eq_of_le_sub {y y' : ι → ℝ} {i : ι} (h : noisyArgmax y = i)
    (hy : ∀ j, y i - y j ≤ y' i - y' j) : noisyArgmax y' = i := by
  rw [noisyArgmax_eq_iff] at h ⊢
  exact ⟨fun j ↦ by linarith [h.1 j, hy j], fun j hj ↦ by linarith [h.2 j hj, hy j]⟩

lemma measurableSet_noisyArgmax_preimage (i : ι) :
    MeasurableSet (noisyArgmax ⁻¹' {i} : Set (ι → ℝ)) := by
  have : (noisyArgmax ⁻¹' {i} : Set (ι → ℝ)) =
      (⋂ j, {y | y j ≤ y i}) ∩ ⋂ j ∈ Finset.univ.filter (· < i), {y | y j < y i} := by
    ext y
    simp [noisyArgmax_eq_iff]
  rw [this]
  exact (MeasurableSet.iInter fun j ↦ measurableSet_le (by fun_prop) (by fun_prop)).inter
    (MeasurableSet.biInter (Finset.countable_toSet _) fun j _ ↦
      measurableSet_lt (by fun_prop) (by fun_prop))

@[fun_prop]
lemma measurable_noisyArgmax [MeasurableSpace ι] :
    Measurable (noisyArgmax : (ι → ℝ) → ι) :=
  measurable_to_countable' fun i ↦ measurableSet_noisyArgmax_preimage i

end Argmax

/-! ### Report Noisy Max -/

namespace SparseVector

/-- Shifting the argument of the Laplace density is shifting its location. -/
lemma laplacePDFReal_sub (m b y v : ℝ) :
    laplacePDFReal m b (y - v) = laplacePDFReal (m + v) b y := by
  rw [laplacePDFReal, laplacePDFReal, sub_sub, add_comm v]

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] {b ε : ℝ}

/-- The heart of the proof of Claim 3.9 of Dwork–Roth: if the "lead" of coordinate `i` changes
by at most `1` between the location vectors `μ` and `μ'` (`μ i - μ' i ≤ μ j - μ' j + 1`), then
the probability that `i` is the noisy argmax under i.i.d. `Lap(b)` noise around `μ` is at most
`e^ε` times that around `μ'`, whenever `1 ≤ ε b`. The proof shifts the noise of coordinate `i`
by `1` (and the other coordinates by `μ' - μ`), which can only increase the lead of `i`. -/
lemma withDensity_noisyArgmax_le (hb : 0 < b) (hεb : 1 ≤ ε * b) {μ μ' : ι → ℝ} {i : ι}
    (h : ∀ j, μ i - μ' i ≤ μ j - μ' j + 1) :
    volume.withDensity (fun y ↦ ENNReal.ofReal (laplacePiPDFReal μ b y))
        (noisyArgmax ⁻¹' {i}) ≤
      ENNReal.ofReal (exp ε) *
        volume.withDensity (fun y ↦ ENNReal.ofReal (laplacePiPDFReal μ' b y))
          (noisyArgmax ⁻¹' {i}) := by
  set T : Set (ι → ℝ) := noisyArgmax ⁻¹' {i}
  have hT : MeasurableSet T := measurableSet_noisyArgmax_preimage i
  set w : ι → ℝ := μ' - μ + Pi.single i 1
  -- shifting by `w` keeps `i` the noisy argmax
  have hsub : T ⊆ (· + w) ⁻¹' T := fun y (hy : noisyArgmax y = i) ↦ by
    refine noisyArgmax_eq_of_le_sub hy fun j ↦ ?_
    by_cases hj : j = i
    · simp [hj]
    · have := h j
      simp only [w, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hj]
      linarith
  -- after the shift, the density is the Laplace density around `μ' + e_i`
  have hshift (z : ι → ℝ) : laplacePiPDFReal μ b (z - w) =
      laplacePiPDFReal (μ' + Pi.single i 1) b z := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Pi.sub_apply, laplacePDFReal_sub]
    congr 1
    simp only [w, Pi.add_apply, Pi.sub_apply]
    ring
  have hratio (z : ι → ℝ) : laplacePiPDFReal (μ' + Pi.single i 1) b z ≤
      exp ε * laplacePiPDFReal μ' b z := by
    refine laplacePiPDFReal_le_exp_mul hb ?_ z
    have : ∑ j, |(μ' + Pi.single i 1 : ι → ℝ) j - μ' j| = 1 := by
      simp only [Pi.add_apply, add_sub_cancel_left]
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp
    linarith
  calc _ ≤ volume.withDensity (fun y ↦ ENNReal.ofReal (laplacePiPDFReal μ b y))
        ((· + w) ⁻¹' T) := measure_mono hsub
    _ = volume.withDensity (fun z ↦ ENNReal.ofReal (laplacePiPDFReal μ b (z - w))) T :=
        withDensity_preimage_add _ w hT
    _ ≤ _ := by
        rw [withDensity_apply _ hT, withDensity_apply _ hT,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun z ↦ ?_
        rw [hshift, ← ENNReal.ofReal_mul (exp_pos ε).le]
        exact ENNReal.ofReal_le_ofReal (hratio z)

end SparseVector

section Mechanism

variable {𝒟 ι : Type*} [MeasurableSpace 𝒟] [Fintype ι] [LinearOrder ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {c : 𝒟 → ι → ℝ} {b ε : ℝ}

/-- **Report Noisy Max** (Dwork–Roth, Section 3.3): add independent `Lap(b)` noise to each of the
query answers `c(x)_i`, `i ∈ ι`, and report only the index of the largest noisy answer (ties,
which have probability zero, are broken towards the smallest index). Dwork–Roth take `b = 1/ε`
and counting queries. -/
noncomputable def reportNoisyMax (c : 𝒟 → ι → ℝ) (b : ℝ) : Kernel 𝒟 ι :=
  (laplaceMechanismPi c b).map noisyArgmax

omit [MeasurableSingletonClass ι] in
lemma isMarkovKernel_reportNoisyMax (hc : Measurable c) (hb : 0 < b) :
    IsMarkovKernel (reportNoisyMax c b) := by
  have := isMarkovKernel_laplaceMechanismPi hc hb
  exact Kernel.IsMarkovKernel.map _ measurable_noisyArgmax

/-- Report Noisy Max with noise scale `b` is `ε`-DP whenever `1 ≤ ε b` and, for all neighbouring
`x, x'`, the differences `c(x)_i - c(x')_i` of the query answers vary by at most `1` across
the queries. This is the general form of Claim 3.9 of Dwork–Roth
(`isEpsDP_reportNoisyMax_countingQuery`). -/
theorem isEpsDP_reportNoisyMax_of_le {Adj : 𝒟 → 𝒟 → Prop} (hc : Measurable c) (hb : 0 < b)
    (hεb : 1 ≤ ε * b) (hAdj : ∀ ⦃x x'⦄, Adj x x' → ∀ i j, c x i - c x' i ≤ c x j - c x' j + 1) :
    IsEpsDP (reportNoisyMax c b) Adj ε := by
  have := isMarkovKernel_reportNoisyMax hc hb
  rw [isEpsDP_iff_forall_singleton]
  intro x x' hx i
  rw [← add_zero (exp ε * _)]
  refine DP.measureReal_le_of_measure_le le_rfl ?_
  rw [ENNReal.ofReal_zero, add_zero, reportNoisyMax,
    Kernel.map_apply' _ measurable_noisyArgmax _ (measurableSet_singleton i),
    Kernel.map_apply' _ measurable_noisyArgmax _ (measurableSet_singleton i), laplaceMechanismPi,
    Kernel.withDensity_apply _ (measurable_uncurry_laplacePiPDFReal hc b),
    Kernel.withDensity_apply _ (measurable_uncurry_laplacePiPDFReal hc b), Kernel.const_apply]
  exact SparseVector.withDensity_noisyArgmax_le hb hεb fun j ↦ hAdj hx i j

end Mechanism

/-! ### Counting queries on histograms -/

section Counting

variable {X : Type*} [Fintype X]

/-- The **counting query** for the predicate `P` on a histogram `x : X → ℕ` (a database with
`x u` copies of the record `u`; Dwork–Roth, Section 2.3): the number of records of `x` that
satisfy `P`. -/
noncomputable def countingQuery (P : X → Prop) [DecidablePred P] (x : X → ℕ) : ℝ :=
  ∑ u with P u, (x u : ℝ)

/-- If two histograms are at `ℓ₁` distance at most `1`, the changes of any two counting queries
differ by at most `1` (each change is `0` or `±1`, with the same sign). -/
lemma countingQuery_sub_le (P Q : X → Prop) [DecidablePred P] [DecidablePred Q]
    {x x' : X → ℕ} (h : ∑ u, |(x u : ℝ) - x' u| ≤ 1) :
    countingQuery P x - countingQuery P x' ≤ countingQuery Q x - countingQuery Q x' + 1 := by
  have key : countingQuery P x - countingQuery P x' - (countingQuery Q x - countingQuery Q x') =
      ∑ u, ((if P u then ((x u : ℝ) - x' u) else 0) - if Q u then ((x u : ℝ) - x' u) else 0) := by
    simp only [countingQuery, Finset.sum_filter, Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun u _ ↦ by split_ifs <;> simp
    · exact Finset.sum_congr rfl fun u _ ↦ by split_ifs <;> simp
  have hle : ∑ u, ((if P u then ((x u : ℝ) - x' u) else 0) -
      if Q u then ((x u : ℝ) - x' u) else 0) ≤ ∑ u, |(x u : ℝ) - x' u| :=
    Finset.sum_le_sum fun u _ ↦ by
      split_ifs <;> linarith [le_abs_self ((x u : ℝ) - x' u), neg_abs_le ((x u : ℝ) - x' u)]
  linarith

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {ε : ℝ}

/-- **Claim 3.9 of Dwork–Roth**: Report Noisy Max for `m = |ι|` counting queries with i.i.d.
`Lap(1/ε)` noise is `(ε, 0)`-differentially private, for `ε > 0`. Databases are histograms
`x : X → ℕ` over a finite universe `X`, the queries are the counting queries of predicates
`P i`, and neighbouring databases are those at `ℓ₁` distance at most `1`,
`∑_u |x u - x' u| ≤ 1` (Dwork–Roth fix `D = D' ∪ {a}`, the case of distance exactly `1`).
Ties in the noisy maximum, which have probability zero, go to the smallest index. -/
theorem isEpsDP_reportNoisyMax_countingQuery (P : ι → X → Prop) [∀ i, DecidablePred (P i)]
    (hε : 0 < ε) :
    IsEpsDP (reportNoisyMax (fun x i ↦ countingQuery (P i) x) (1 / ε))
      (fun x x' : X → ℕ ↦ ∑ u, |(x u : ℝ) - x' u| ≤ 1) ε := by
  refine isEpsDP_reportNoisyMax_of_le ?_ (by positivity) (by field_simp; rfl)
    fun x x' hx i j ↦ countingQuery_sub_le _ _ hx
  unfold countingQuery
  fun_prop

end Counting

/-! ### AboveThreshold -/

namespace SparseVector

variable {μ μ' b ε : ℝ}

/-- Translating a Laplace variable translates its location: if `Y ∼ Lap(μ, b)` then
`Y + v ∼ Lap(μ + v, b)`. -/
lemma laplaceMeasure_map_add (μ b v : ℝ) :
    (laplaceMeasure μ b).map (· + v) = laplaceMeasure (μ + v) b := by
  ext A hA
  rw [Measure.map_apply (measurable_add_const v) hA, laplaceMeasure,
    withDensity_preimage_add _ v hA, laplaceMeasure]
  simp only [laplacePDF, laplacePDFReal_sub]
  rfl

/-- If `|μ - μ'| ≤ ε b`, then `Lap(μ, b) ≤ e^ε Lap(μ', b)` as measures. -/
lemma laplaceMeasure_le_smul (hb : 0 < b) (h : |μ - μ'| ≤ ε * b) :
    laplaceMeasure μ b ≤ ENNReal.ofReal (exp ε) • laplaceMeasure μ' b := by
  rw [laplaceMeasure, laplaceMeasure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (ae_of_all _ fun y ↦ ?_)
  rw [Pi.smul_apply, smul_eq_mul, laplacePDF, laplacePDF, ← ENNReal.ofReal_mul (exp_pos ε).le]
  exact ENNReal.ofReal_le_ofReal (laplacePDFReal_le_exp_mul hb h y)

/-- `P[Lap(μ, b) ∈ A] = P[Lap(μ + v, b) ∈ A + v]`, in preimage form. -/
lemma laplaceMeasure_preimage_add (μ b v : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    laplaceMeasure μ b ((· + v) ⁻¹' A) = laplaceMeasure (μ + v) b A := by
  rw [← laplaceMeasure_map_add, Measure.map_apply (measurable_add_const v) hA]

/-- The left tail `P[Lap(μ, b) < t]` is antitone in the location. -/
lemma laplaceMeasure_Iio_le (b : ℝ) {μ μ' : ℝ} (h : μ' ≤ μ) (t : ℝ) :
    laplaceMeasure μ b (Iio t) ≤ laplaceMeasure μ' b (Iio t) := by
  have : μ = μ' + (μ - μ') := by ring
  rw [this, ← laplaceMeasure_preimage_add _ _ _ measurableSet_Iio]
  exact measure_mono fun y (hy : y + (μ - μ') < t) ↦ show y < t by linarith

end SparseVector

section FirstAbove

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {t : ℝ} {y : ι → ℝ}

/-- The output of AboveThreshold given the noisy threshold `t` and the noisy answers `y`:
`Sum.inl k` for the first index `k` with `t ≤ y k` (the answers are `⊥` before `k`, `⊤` at `k`,
and the algorithm halts), and `Sum.inr ()` if no noisy answer reaches the threshold (all answers
are `⊥`). -/
noncomputable def firstAbove (t : ℝ) (y : ι → ℝ) : ι ⊕ Unit :=
  if h : (Finset.univ.filter fun i ↦ t ≤ y i).Nonempty then
    .inl ((Finset.univ.filter fun i ↦ t ≤ y i).min' h)
  else .inr ()

lemma firstAbove_eq_inl_iff {k : ι} :
    firstAbove t y = .inl k ↔ t ≤ y k ∧ ∀ i < k, y i < t := by
  unfold firstAbove
  split_ifs with h
  · have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    rw [Sum.inl.injEq]
    constructor
    · rintro rfl
      exact ⟨hmem.2, fun i hi ↦ lt_of_not_ge fun hti ↦ hi.not_ge
        (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ i, hti⟩))⟩
    · rintro ⟨h₁, h₂⟩
      refine le_antisymm (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ k, h₁⟩)) ?_
      exact le_of_not_gt fun hlt ↦ (h₂ _ hlt).not_ge hmem.2
  · simp only [false_iff, not_and, not_forall, not_lt]
    exact fun hk ↦ absurd ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩⟩ h

lemma firstAbove_eq_inr_iff {u : Unit} : firstAbove t y = .inr u ↔ ∀ i, y i < t := by
  unfold firstAbove
  split_ifs with h
  · simp only [false_iff, not_forall, not_lt]
    obtain ⟨i, hi⟩ := h
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  · simp only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff, Finset.mem_univ,
      not_le, true_imp_iff] at h
    simpa using h

/-- The coordinate sets whose product is the event `firstAbove t y = o` (`firstAbove_preimage`):
for `o = inl k`, `y i < t` for `i < k`, `t ≤ y k` and no condition for `i > k`; for `o = inr ()`,
`y i < t` for all `i`. -/
def SparseVector.aboveSet (o : ι ⊕ Unit) (t : ℝ) (i : ι) : Set ℝ :=
  Sum.elim (fun k ↦ if i < k then Iio t else if i = k then Ici t else univ) (fun _ ↦ Iio t) o

lemma SparseVector.firstAbove_preimage (o : ι ⊕ Unit) (t : ℝ) :
    {y : ι → ℝ | firstAbove t y = o} = univ.pi (aboveSet o t) := by
  ext y
  simp only [mem_ofPred_eq, mem_univ_pi]
  rcases o with k | u
  · rw [firstAbove_eq_inl_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ i
      simp only [aboveSet, Sum.elim_inl]
      split_ifs with hik hik'
      · exact h₂ i hik
      · exact hik' ▸ h₁
      · exact mem_univ _
    · intro h
      refine ⟨by simpa [aboveSet] using h k, fun i hi ↦ ?_⟩
      simpa [aboveSet, hi] using h i
  · rw [firstAbove_eq_inr_iff]
    simp [aboveSet]

lemma measurable_firstAbove [MeasurableSpace ι] :
    Measurable fun p : ℝ × (ι → ℝ) ↦ firstAbove p.1 p.2 := by
  refine measurable_to_countable' fun o ↦ ?_
  rcases o with k | u
  · have : (fun p : ℝ × (ι → ℝ) ↦ firstAbove p.1 p.2) ⁻¹' {.inl k} =
        {p | p.1 ≤ p.2 k} ∩ ⋂ i ∈ Finset.univ.filter (· < k), {p | p.2 i < p.1} := by
      ext p
      simp [firstAbove_eq_inl_iff]
    rw [this]
    exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ ↦
        measurableSet_lt (by fun_prop) (by fun_prop))
  · have : (fun p : ℝ × (ι → ℝ) ↦ firstAbove p.1 p.2) ⁻¹' {.inr u} =
        ⋂ i, {p | p.2 i < p.1} := by
      ext p
      simp [firstAbove_eq_inr_iff]
    rw [this]
    exact MeasurableSet.iInter fun i ↦ measurableSet_lt (by fun_prop) (by fun_prop)

end FirstAbove

namespace SparseVector

variable {ι : Type*} [LinearOrder ι] {μ μ' b ε : ℝ}

/-- The coordinatewise step of the proof of Theorem 3.23 of Dwork–Roth: if `|μ - μ'| ≤ 1` and
`2 ≤ ε b`, then moving the threshold from `t` to `t + 1`, the probability that `Lap(μ, b)` lies
in the `i`-th coordinate set of the event `firstAbove · · = o` grows from `μ` to `μ'` by a factor
of at most `e^ε` at the halting coordinate `o = inl i`, and at most `1` elsewhere. -/
lemma laplaceMeasure_aboveSet_le (hb : 0 < b) (hεb : 2 ≤ ε * b) (h : |μ - μ'| ≤ 1)
    (o : ι ⊕ Unit) (t : ℝ) (i : ι) :
    laplaceMeasure μ b (aboveSet o t i) ≤
      (if o = .inl i then ENNReal.ofReal (exp ε) else 1) *
        laplaceMeasure μ' b (aboveSet o (t + 1) i) := by
  have hIio : (· + 1) ⁻¹' Iio (t + 1) = Iio t := by ext; simp
  have hIci : (· + 1) ⁻¹' Ici (t + 1) = Ici t := by ext; simp
  -- the left tail: shift by `1`, then use `μ' ≤ μ + 1`
  have tail : laplaceMeasure μ b (Iio t) ≤ laplaceMeasure μ' b (Iio (t + 1)) := by
    rw [← hIio, laplaceMeasure_preimage_add _ _ _ measurableSet_Iio]
    exact laplaceMeasure_Iio_le b (by linarith [le_abs_self (μ' - μ), abs_sub_comm μ μ']) _
  rcases o with k | u
  · simp only [aboveSet, Sum.elim_inl, Sum.inl.injEq]
    by_cases hik : i < k
    · simp only [hik, hik.ne', ↓reduceIte, one_mul]
      exact tail
    by_cases hik' : i = k
    · subst hik'
      simp only [lt_irrefl, ↓reduceIte]
      rw [← hIci, laplaceMeasure_preimage_add _ _ _ measurableSet_Ici]
      refine laplaceMeasure_le_smul hb ?_ _
      have : |μ + 1 - μ'| ≤ 2 := by
        rw [abs_le] at h ⊢
        constructor <;> linarith
      linarith
    · simp only [hik, hik', Ne.symm hik', ↓reduceIte, one_mul]
      have := isProbabilityMeasure_laplaceMeasure μ hb
      have := isProbabilityMeasure_laplaceMeasure μ' hb
      simp
  · simp only [aboveSet, Sum.elim_inr, reduceCtorEq, ite_false, one_mul]
    exact tail

end SparseVector

section AboveThresholdMechanism

variable {𝒟 ι : Type*} [MeasurableSpace 𝒟] [Fintype ι] [LinearOrder ι] [MeasurableSpace ι]
  {f : 𝒟 → ι → ℝ} {T b₁ b₂ ε₁ ε₂ ε : ℝ}

/-- **AboveThreshold** (Dwork–Roth, Algorithm 1 in Section 3.6), for a finite sequence of queries
`f(x)_i`, `i ∈ ι` (in the order of `ι`), threshold `T` and noise scales `b₁, b₂`: draw the noisy
threshold `T̂ = T + Lap(b₁)` and independent noise `ν_i ∼ Lap(b₂)`, answer `⊥` to the queries
with `f(x)_i + ν_i < T̂`, and halt at the first query with `f(x)_i + ν_i ≥ T̂`, answering `⊤`. The
transcript `⊥ … ⊥ ⊤` (respectively `⊥ … ⊥`) is encoded by the index `Sum.inl k` of the
`⊤`-query (respectively by `Sum.inr ()`), see `firstAbove`. Dwork–Roth take `b₁ = 2/ε` and
`b₂ = 4/ε`. -/
noncomputable def aboveThreshold (f : 𝒟 → ι → ℝ) (T b₁ b₂ : ℝ) : Kernel 𝒟 (ι ⊕ Unit) :=
  (Kernel.const 𝒟 (laplaceMeasure T b₁) ×ₖ laplaceMechanismPi f b₂).map
    fun p ↦ firstAbove p.1 p.2

lemma isMarkovKernel_aboveThreshold (hf : Measurable f) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    IsMarkovKernel (aboveThreshold f T b₁ b₂) := by
  have := isProbabilityMeasure_laplaceMeasure T hb₁
  have := isMarkovKernel_laplaceMechanismPi hf hb₂
  exact Kernel.IsMarkovKernel.map _ measurable_firstAbove

/-- AboveThreshold on a finite query sequence is `(ε₁ + ε₂)`-DP for sensitivity-`1` queries when
the threshold noise scale satisfies `1 ≤ ε₁ b₁` and the query noise scale satisfies
`2 ≤ ε₂ b₂`. With `b₁ = 1/ε₁`, `b₂ = 2/ε₂` and an arbitrary split `(ε₁, ε₂)` this is Theorem 4 of
Lyu–Su–Li (their Alg. 7) for `c = 1`, `ε₃ = 0`, `Δ = 1` and a single threshold; their Theorem 2
and Theorem 3.23 of Dwork–Roth are the case `ε₁ = ε₂` (`isEpsDP_aboveThreshold`). The proof is
that of Lyu–Su–Li, not Dwork–Roth's change of variables by `g(D) - g(D')`: integrating over the
noisy threshold last, shift it up by `1` (costing `e^{ε₁}`); the factors of the `⊥`-queries do
not decrease, by monotonicity of the left Laplace tail, and the noise of the `⊤`-query moves by
at most `2`, costing `e^{ε₂}`. -/
theorem isEpsDP_aboveThreshold_of_le [MeasurableSingletonClass ι] {Adj : 𝒟 → 𝒟 → Prop}
    (hf : Measurable f) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (h₁ : 1 ≤ ε₁ * b₁) (h₂ : 2 ≤ ε₂ * b₂)
    (hAdj : ∀ ⦃x x'⦄, Adj x x' → ∀ i, |f x i - f x' i| ≤ 1) :
    IsEpsDP (aboveThreshold f T b₁ b₂) Adj (ε₁ + ε₂) := by
  have := isMarkovKernel_aboveThreshold (T := T) hf hb₁ hb₂
  have := isProbabilityMeasure_laplaceMeasure T hb₁
  have := isMarkovKernel_laplaceMechanismPi hf hb₂
  rw [isEpsDP_iff_forall_singleton]
  intro x x' hx o
  rw [← add_zero (exp (ε₁ + ε₂) * _)]
  refine DP.measureReal_le_of_measure_le le_rfl ?_
  have hF := measurable_firstAbove (ι := ι) (measurableSet_singleton o)
  rw [ENNReal.ofReal_zero, add_zero, aboveThreshold,
    Kernel.map_apply' _ measurable_firstAbove _ (measurableSet_singleton o),
    Kernel.map_apply' _ measurable_firstAbove _ (measurableSet_singleton o),
    Kernel.prod_apply' _ _ _ hF, Kernel.prod_apply' _ _ _ hF, Kernel.const_apply]
  -- the inner probability is a product over the coordinates
  set G : 𝒟 → ℝ → ℝ≥0∞ := fun z t ↦ ∏ i, laplaceMeasure (f z i) b₂ (SparseVector.aboveSet o t i)
  have hsec (z : 𝒟) (t : ℝ) : laplaceMechanismPi f b₂ z
      (Prod.mk t ⁻¹' ((fun p : ℝ × (ι → ℝ) ↦ firstAbove p.1 p.2) ⁻¹' {o})) = G z t := by
    have := fun i ↦ isProbabilityMeasure_laplaceMeasure (f z i) hb₂
    rw [laplaceMechanismPi_apply hf hb₂]
    exact (congrArg _ (SparseVector.firstAbove_preimage o t)).trans (Measure.pi_pi _ _)
  simp_rw [hsec]
  have hε₂ : 0 ≤ ε₂ := by nlinarith
  -- pointwise in the noisy threshold: shift it up by `1`
  have hpt (t : ℝ) : G x t ≤ ENNReal.ofReal (exp ε₂) * G x' (t + 1) := by
    have hc : ∏ i, (if o = .inl i then ENNReal.ofReal (exp ε₂) else 1) ≤
        ENNReal.ofReal (exp ε₂) := by
      rcases o with k | u
      · simp [Finset.prod_ite_eq]
      · simpa using ENNReal.one_le_ofReal.2 (one_le_exp hε₂)
    calc G x t ≤ ∏ i, ((if o = .inl i then ENNReal.ofReal (exp ε₂) else 1) *
          laplaceMeasure (f x' i) b₂ (SparseVector.aboveSet o (t + 1) i)) :=
          Finset.prod_le_prod fun i _ ↦
            SparseVector.laplaceMeasure_aboveSet_le hb₂ h₂ (hAdj hx i) o t i
      _ = (∏ i, if o = .inl i then ENNReal.ofReal (exp ε₂) else 1) * G x' (t + 1) :=
          Finset.prod_mul_distrib
      _ ≤ ENNReal.ofReal (exp ε₂) * G x' (t + 1) := by gcongr
  calc ∫⁻ t, G x t ∂laplaceMeasure T b₁
      ≤ ∫⁻ t, ENNReal.ofReal (exp ε₂) * G x' (t + 1) ∂laplaceMeasure T b₁ := lintegral_mono hpt
    _ = ENNReal.ofReal (exp ε₂) * ∫⁻ t, G x' t ∂laplaceMeasure (T + 1) b₁ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← SparseVector.laplaceMeasure_map_add T b₁ 1]
        congr 1
        exact (lintegral_map_equiv (G x') (MeasurableEquiv.addRight (1 : ℝ))).symm
    _ ≤ ENNReal.ofReal (exp ε₂) *
          ∫⁻ t, G x' t ∂(ENNReal.ofReal (exp ε₁) • laplaceMeasure T b₁) := by
        gcongr
        refine SparseVector.laplaceMeasure_le_smul hb₁ ?_
        simpa using h₁
    _ = ENNReal.ofReal (exp (ε₁ + ε₂)) * ∫⁻ t, G x' t ∂laplaceMeasure T b₁ := by
        rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc, exp_add,
          ENNReal.ofReal_mul (exp_pos _).le, mul_comm (ENNReal.ofReal (exp ε₂))]

/-- **Theorem 3.23 of Dwork–Roth**: AboveThreshold, with noisy threshold `T + Lap(2/ε)` and query
noise `Lap(4/ε)`, is `(ε, 0)`-differentially private for `ε > 0` and queries of sensitivity `1`
(`|f(x)_i - f(x')_i| ≤ 1` for neighbouring `x, x'`). Non-adaptive case: the queries form a
fixed finite sequence indexed by the linear order `ι`; deterministic adaptive analysts reduce to
it, randomized ones are not covered. The output is the whole transcript, including the case where
no query is above the threshold. This is also Theorem 2 of Lyu–Su–Li (their Alg. 1) for `c = 1`,
`Δ = 1` and a single threshold. -/
theorem isEpsDP_aboveThreshold [MeasurableSingletonClass ι] {Adj : 𝒟 → 𝒟 → Prop}
    (hf : Measurable f) (hε : 0 < ε) (hAdj : ∀ ⦃x x'⦄, Adj x x' → ∀ i, |f x i - f x' i| ≤ 1) :
    IsEpsDP (aboveThreshold f T (2 / ε) (4 / ε)) Adj ε := by
  have := isEpsDP_aboveThreshold_of_le (T := T) (b₁ := 2 / ε) (b₂ := 4 / ε) (ε₁ := ε / 2)
    (ε₂ := ε / 2) hf (by positivity) (by positivity) (le_of_eq (by field_simp))
    (le_of_eq (by field_simp; norm_num)) hAdj
  rwa [add_halves] at this

end AboveThresholdMechanism

/-! ### A non-private variant: no noise on the query answers -/

section NoQueryNoise

variable {𝒟 ι : Type*} [MeasurableSpace 𝒟] {q : 𝒟 → ι → ℝ} {T b : ℝ}

/-- The sparse vector variant without noise on the query answers (Alg. 5 of Lyu–Su–Li, the SVT
of Stoddard, Chen and Machanavajjhala, 2014): draw the noisy threshold `T̂ = T + Lap(b)` once
and answer every query by `⊤` (`true`) if `q(x)_i ≥ T̂` and by `⊥` (`false`) otherwise, with no
noise on the answers and no cutoff. Alg. 5 takes `b = Δ/ε₁ = 2Δ/ε`. -/
noncomputable def svtWithoutQueryNoise (q : 𝒟 → ι → ℝ) (T b : ℝ) : Kernel 𝒟 (ι → Bool) :=
  (Kernel.id ×ₖ Kernel.const 𝒟 (laplaceMeasure T b)).map fun p i ↦ decide (p.2 ≤ q p.1 i)

lemma svtWithoutQueryNoise_apply (hq : ∀ i, Measurable fun x ↦ q x i) (x : 𝒟)
    {s : Set (ι → Bool)} (hs : MeasurableSet s) :
    svtWithoutQueryNoise q T b x s =
      laplaceMeasure T b {t | (fun i ↦ decide (t ≤ q x i)) ∈ s} := by
  have hF : Measurable fun p : 𝒟 × ℝ ↦ fun i ↦ decide (p.2 ≤ q p.1 i) := by
    refine measurable_pi_iff.2 fun i ↦ measurable_to_countable' fun c ↦ ?_
    have hm : MeasurableSet {p : 𝒟 × ℝ | p.2 ≤ q p.1 i} :=
      measurableSet_le measurable_snd ((hq i).comp measurable_fst)
    cases c
    · simpa [Set.preimage] using measurableSet_lt ((hq i).comp measurable_fst) measurable_snd
    · simpa [Set.preimage] using hm
  have : SFinite (laplaceMeasure T b) := by unfold laplaceMeasure; infer_instance
  rw [svtWithoutQueryNoise, Kernel.map_apply' _ hF _ hs, Kernel.prod_apply' _ _ _ (hF hs),
    Kernel.id_apply, lintegral_dirac' _ (measurable_measure_prodMk_left (hF hs)),
    Kernel.const_apply]
  rfl

/-- **Theorem 3 of Lyu–Su–Li**: the sparse vector variant without noise on the query answers
(Alg. 5, `svtWithoutQueryNoise`) is not `ε'`-DP for any `ε'`, whatever the scale `b > 0` of the
threshold noise. Their counterexample: two neighbouring datasets `D` (`false`) and `D'` (`true`)
with `T = 0` and two sensitivity-`1` queries with answers `q(D) = (0, 1)` and `q(D') = (1, 0)`;
the transcript `(⊥, ⊤)` has probability `P[0 < Lap(b) ≤ 1] > 0` on `D` and `0` on `D'`. The
statement includes that the two queries have sensitivity `1`. -/
theorem not_isEpsDP_svtWithoutQueryNoise (hb : 0 < b) (ε' : ℝ) :
    (∀ D D' : Bool, ∀ i, |(if D then ![1, 0] else ![0, 1] : Fin 2 → ℝ) i -
      (if D' then ![1, 0] else ![0, 1] : Fin 2 → ℝ) i| ≤ 1) ∧
    ¬ IsEpsDP (svtWithoutQueryNoise (fun D : Bool ↦ (if D then ![1, 0] else ![0, 1] : Fin 2 → ℝ))
      0 b) (· ≠ ·) ε' := by
  refine ⟨fun D D' i ↦ by fin_cases i <;> cases D <;> cases D' <;> norm_num, fun h ↦ ?_⟩
  have := isProbabilityMeasure_laplaceMeasure 0 hb
  set a : Fin 2 → Bool := ![false, true]
  have hq : ∀ i, Measurable fun D : Bool ↦ (if D then ![1, 0] else ![0, 1] : Fin 2 → ℝ) i :=
    fun i ↦ measurable_of_countable _
  have h₀ := isEpsDP_iff.1 h (show false ≠ true by decide) {a}
  rw [measureReal_def, measureReal_def, svtWithoutQueryNoise_apply hq _ (measurableSet_singleton a),
    svtWithoutQueryNoise_apply hq _ (measurableSet_singleton a)] at h₀
  have e₁ : {t : ℝ | (fun i ↦ decide (t ≤ (if false then ![1, 0] else ![0, 1] : Fin 2 → ℝ) i))
      ∈ ({a} : Set (Fin 2 → Bool))} = Ioc 0 1 := by
    ext t
    simp only [a, mem_ofPred_eq, mem_singleton_iff, funext_iff, Fin.forall_fin_two, mem_Ioc]
    simp only [Bool.false_eq_true, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
      decide_eq_false_iff_not, not_le, decide_eq_true_eq]
  have e₂ : {t : ℝ | (fun i ↦ decide (t ≤ (if true then ![1, 0] else ![0, 1] : Fin 2 → ℝ) i))
      ∈ ({a} : Set (Fin 2 → Bool))} = ∅ := by
    ext t
    simp only [a, mem_singleton_iff, funext_iff, Fin.forall_fin_two, mem_ofPred_eq]
    simp only [ite_true, Matrix.cons_val_zero, Matrix.cons_val_one, decide_eq_false_iff_not,
      not_le, decide_eq_true_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro h₁
    linarith
  rw [e₁, e₂, measure_empty, ENNReal.toReal_zero, mul_zero] at h₀
  have hpos : laplaceMeasure 0 b (Ioc 0 1) ≠ 0 := by
    rw [laplaceMeasure, Ne, withDensity_apply_eq_zero' (by fun_prop)]
    have : {y : ℝ | laplacePDF 0 b y ≠ 0} = univ :=
      eq_univ_of_forall fun y ↦ by simp [laplacePDF, laplacePDFReal_pos hb y]
    simp [this]
  exact absurd h₀ (not_le.2 (ENNReal.toReal_pos hpos (measure_ne_top _ _)))

end NoQueryNoise

end InformationTheory
