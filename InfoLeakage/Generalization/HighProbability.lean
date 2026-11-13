/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.Generalization.Basic
public import InfoLeakage.MaxInformation.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Differential privacy implies generalization with high probability

This file proves, for finite data and output alphabets, a high-probability transfer theorem for
pure differential privacy in the setting of

* C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, *Preserving statistical
  validity in adaptive data analysis*, STOC 2015,
  [arXiv:1411.2664](https://arxiv.org/abs/1411.2664); result numbers follow arXiv v3,

through the max-information route of

* C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, *Generalization in adaptive
  data analysis and holdout reuse*, NeurIPS 2015,
  [arXiv:1506.02629](https://arxiv.org/abs/1506.02629); result numbers follow arXiv v2,

whose Theorems 13 and 19 are `measure_compProd_le_of_maxInformation_le` and
`hasMaxInformation_of_isEpsDeltaDP` in `InfoLeakage.MaxInformation.Basic`. The setting and
notation are those of `InfoLeakage.Generalization.Basic`: datasets `S : ι → 𝒳` of `n = |ι|`
records, `S ∼ Pⁿ`, mechanisms `M : Kernel (ι → 𝒳) Z`, neighbours at Hamming distance `1`.

## Main statements

* `Generalization.hoeffding_empiricalMean_sub_le`,
  `Generalization.hoeffding_abs_empiricalMean_sub_le`: Hoeffding's inequality
  `P[|E_S[ψ] - P[ψ]| ≥ τ] ≤ 2 e^{-2τ²n}` for `ψ : 𝒳 → [0, 1]` and finite `𝒳`, from Mathlib's
  Hoeffding inequality for sub-Gaussian variables (the bound needs no finiteness).
* `IsEpsDeltaDP.measureReal_mem_le_exp_mul`: if `M` is `ε`-differentially private and
  `P[S ∈ R z] ≤ β` for every fixed output `z`, then `P[S ∈ R(M(S))] ≤ e^{εn} β`, for every
  distribution of `S`.
* `IsEpsDeltaDP.measureReal_le_abs_empiricalMean_sub_le`: if `M` is `ε`-differentially private
  and outputs a statistical query `Q_z : 𝒳 → [0, 1]`, then
  `P[|E_S[Q_{M(S)}] - P[Q_{M(S)}]| ≥ τ] ≤ 2 e^{(ε - 2τ²) n}`.

## Paper → Lean

Dwork et al., STOC 2015 (arXiv v3):
* The Hoeffding bound stated after Definition 4 (also "the Chernoff bound" in the proof of
  Corollary 12), `P[|E_S[ψ] - P[ψ]| > τ] ≤ 2 e^{-2τ²n}` →
  `Generalization.hoeffding_abs_empiricalMean_sub_le`, with the larger event `≥ τ`, for finite
  `𝒳` (the paper's bound holds for any `𝒳`).
* Theorem 11 (any output space, `S ∼ Pⁿ`, `max_y P[S ∈ R(y)] ≤ β`) concludes
  `P[S ∈ R(Y)] ≤ 3√β` when `ε ≤ √(ln(1/β)/(2n))`. It is **not** formalized; the formalized
  `IsEpsDeltaDP.measureReal_mem_le_exp_mul` has the same hypotheses on `R`, a finite output space
  and an arbitrary distribution of `S`, and concludes `P[S ∈ R(Y)] ≤ e^{εn} β` for every `ε ≥ 0`.
  This is sharper than `3√β` when `εn ≤ ln(3/√β)` and weaker otherwise.
* Corollary 12 (`P[|P[φ] - E_S[φ]| > τ] ≤ 3√2 e^{-τ²n}` when `ε ≤ √(τ² - ln 2/(2n))`) is **not**
  formalized; its max-information analogue (finite output space, pure DP only) is
  `IsEpsDeltaDP.measureReal_le_abs_empiricalMean_sub_le`, which gives `2 e^{-τ²n}` when `ε ≤ τ²`
  (Corollary 12 allows `ε` of order `τ`).

Dwork et al., NeurIPS 2015 (arXiv v2):
* Theorem 13 (`β = 0`) combined with Theorem 19 → `IsEpsDeltaDP.measureReal_mem_le_exp_mul`.

## Not formalized

Lemma 8, Theorems 9–11 and Corollary 12 of Dwork et al. (STOC 2015) themselves (the moment method
and the McDiarmid argument), and the `(ε, δ)` case of the high-probability bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {ι 𝒳 Z : Type*} [Fintype ι] {m𝒳 : MeasurableSpace 𝒳} {mZ : MeasurableSpace Z}
  [Finite 𝒳] [MeasurableSingletonClass 𝒳] {P : Measure 𝒳} [IsProbabilityMeasure P]

namespace Generalization

/-- **Hoeffding's inequality** for the empirical mean of a `[0, 1]`-valued function `ψ` on an
i.i.d. dataset `S ∼ Pⁿ` (`n = |ι| ≥ 1`), one-sided:
`P[E_S[ψ] - P[ψ] ≥ τ] ≤ exp (-2 n τ²)`. Here `𝒳` is assumed finite; the bound itself needs no
finiteness. -/
theorem hoeffding_empiricalMean_sub_le [Nonempty ι] {ψ : 𝒳 → ℝ}
    (hψ : ∀ x, ψ x ∈ Icc (0 : ℝ) 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (Measure.pi fun _ : ι ↦ P).real {S | τ ≤ empiricalMean ψ S - ∫ x, ψ x ∂P} ≤
      exp (-2 * Fintype.card ι * τ ^ 2) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  set X : ι → (ι → 𝒳) → ℝ := fun i S ↦ ψ (S i) - ∫ x, ψ x ∂P with hX
  have hind : iIndepFun X (Measure.pi fun _ : ι ↦ P) :=
    iIndepFun_pi (X := fun _ x ↦ ψ x - ∫ x, ψ x ∂P) fun _ ↦ (measurable_of_finite _).aemeasurable
  have hsub : ∀ i ∈ (Finset.univ : Finset ι),
      HasSubgaussianMGF (X i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (Measure.pi fun _ : ι ↦ P) := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (μ := Measure.pi fun _ : ι ↦ P)
      (X := fun S ↦ ψ (S i)) (measurable_of_finite _).aemeasurable (ae_of_all _ fun S ↦ hψ (S i))
    rwa [integral_comp_eval (measurable_of_finite ψ).aestronglyMeasurable] at h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (ε := Fintype.card ι * τ) (by positivity)
  have hset : {S : ι → 𝒳 | τ ≤ empiricalMean ψ S - ∫ x, ψ x ∂P} =
      {S | Fintype.card ι * τ ≤ ∑ i, X i S} := by
    ext S
    simp only [mem_ofPred_eq, hX, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, empiricalMean]
    rw [le_sub_iff_add_le, le_div_iff₀ hn, le_sub_iff_add_le]
    ring_nf
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, sub_zero, norm_one, NNReal.coe_ofNat]
  field_simp

/-- **Hoeffding's inequality** for the empirical mean of a `[0, 1]`-valued function `ψ` on an
i.i.d. dataset `S ∼ Pⁿ` (`n = |ι| ≥ 1`), two-sided:
`P[|E_S[ψ] - P[ψ]| ≥ τ] ≤ 2 exp (-2 n τ²)` (the bound stated after Definition 4 of Dwork et al.,
STOC 2015). Here `𝒳` is assumed finite; the bound itself needs no finiteness. -/
theorem hoeffding_abs_empiricalMean_sub_le [Nonempty ι] {ψ : 𝒳 → ℝ}
    (hψ : ∀ x, ψ x ∈ Icc (0 : ℝ) 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (Measure.pi fun _ : ι ↦ P).real {S | τ ≤ |empiricalMean ψ S - ∫ x, ψ x ∂P|} ≤
      2 * exp (-2 * Fintype.card ι * τ ^ 2) := by
  have hψ' (x : 𝒳) : 1 - ψ x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [(hψ x).2], by linarith [(hψ x).1]⟩
  have hint : ∫ x, (1 - ψ x) ∂P = 1 - ∫ x, ψ x ∂P := by
    rw [integral_sub (integrable_const 1) (Integrable.of_mem_Icc 0 1
      (measurable_of_finite ψ).aemeasurable (ae_of_all _ hψ))]
    simp
  have hset : {S : ι → 𝒳 | τ ≤ |empiricalMean ψ S - ∫ x, ψ x ∂P|} ⊆
      {S | τ ≤ empiricalMean ψ S - ∫ x, ψ x ∂P} ∪
        {S | τ ≤ empiricalMean (fun x ↦ 1 - ψ x) S - ∫ x, (1 - ψ x) ∂P} := by
    intro S hS
    rw [mem_ofPred_eq, le_abs'] at hS
    rcases hS with h | h
    · right
      rw [mem_ofPred_eq, empiricalMean_one_sub, hint]
      linarith
    · exact Or.inl h
  calc (Measure.pi fun _ : ι ↦ P).real {S | τ ≤ |empiricalMean ψ S - ∫ x, ψ x ∂P|}
      ≤ (Measure.pi fun _ : ι ↦ P).real ({S | τ ≤ empiricalMean ψ S - ∫ x, ψ x ∂P} ∪
          {S | τ ≤ empiricalMean (fun x ↦ 1 - ψ x) S - ∫ x, (1 - ψ x) ∂P}) :=
        measureReal_mono hset
    _ ≤ exp (-2 * Fintype.card ι * τ ^ 2) + exp (-2 * Fintype.card ι * τ ^ 2) :=
        (measureReal_union_le _ _).trans (add_le_add
          (hoeffding_empiricalMean_sub_le hψ hτ) (hoeffding_empiricalMean_sub_le hψ' hτ))
    _ = 2 * exp (-2 * Fintype.card ι * τ ^ 2) := by ring

end Generalization

/-! ### A transfer theorem through max-information -/

variable [DecidableEq 𝒳] [Finite Z] [MeasurableSingletonClass Z] {M : Kernel (ι → 𝒳) Z}
  [IsMarkovKernel M] {ε : ℝ}

/-- **Transfer theorem for pure differential privacy, through max-information** (Theorem 13 with
`β = 0` combined with Theorem 19 of Dwork et al., NeurIPS 2015, arXiv:1506.02629). Let `M` be
`ε`-differentially private on datasets of `n = |ι|` records with a finite output space, let the
dataset `S` have any distribution `μ`, and let `R z` be a set of datasets ("`z` overfits `S`")
with `P[S ∈ R z] ≤ β` for every fixed `z`. Then `P[S ∈ R(M(S))] ≤ e^{ε n} β`. This is an
alternative to Theorem 11 of Dwork et al., STOC 2015, which concludes `3√β` when `S ∼ Pⁿ` and
`ε ≤ √(ln(1/β)/(2n))` (not formalized). -/
theorem IsEpsDeltaDP.measureReal_mem_le_exp_mul (hε : 0 ≤ ε)
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε 0) (μ : Measure (ι → 𝒳))
    [IsProbabilityMeasure μ] {R : Z → Set (ι → 𝒳)} {β : ℝ} (hR : ∀ z, μ.real (R z) ≤ β) :
    (μ ⊗ₘ M).real {q | q.1 ∈ R q.2} ≤ exp (ε * Fintype.card ι) * β := by
  obtain ⟨S⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure (M S)
  have hβ : 0 ≤ β := measureReal_nonneg.trans (hR z)
  have h := measure_compProd_le_of_maxInformation_le
    (hasMaxInformation_of_isEpsDeltaDP hε hM μ inferInstance) {q | q.1 ∈ R q.2}
  simp only [mem_ofPred_eq, ofPred_mem_eq] at h
  have hsup : ⨆ z, μ (R z) ≤ ENNReal.ofReal β := iSup_le fun z ↦ by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hR z)
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans ?_)
  rw [ENNReal.ofReal_mul (exp_pos _).le]
  gcongr

/-- **Differential privacy implies generalization with high probability**, for statistical queries
(the max-information route; compare Corollary 12 of Dwork et al., STOC 2015). If `M` is
`ε`-differentially private on datasets of `n = |ι| ≥ 1` records, has a finite output space and
outputs a statistical query `Q z : 𝒳 → [0, 1]`, and `S ∼ Pⁿ`, then for every `τ ≥ 0`,
`P[|E_S[Q_{M(S)}] - P[Q_{M(S)}]| ≥ τ] ≤ 2 e^{(ε - 2τ²) n}`; e.g. `ε ≤ τ²` gives `2 e^{-τ² n}`. -/
theorem IsEpsDeltaDP.measureReal_le_abs_empiricalMean_sub_le [Nonempty ι] (hε : 0 ≤ ε)
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε 0) {Q : Z → 𝒳 → ℝ}
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (Measure.pi (fun _ : ι ↦ P) ⊗ₘ M).real
        {q | τ ≤ |Generalization.empiricalMean (Q q.2) q.1 - ∫ x, Q q.2 x ∂P|} ≤
      2 * exp ((ε - 2 * τ ^ 2) * Fintype.card ι) := by
  refine (hM.measureReal_mem_le_exp_mul hε (Measure.pi fun _ : ι ↦ P)
    (R := fun z ↦ {S | τ ≤ |Generalization.empiricalMean (Q z) S - ∫ x, Q z x ∂P|})
    fun z ↦ Generalization.hoeffding_abs_empiricalMean_sub_le (hQ₁ z) hτ).trans_eq ?_
  rw [mul_left_comm, ← exp_add]
  ring_nf

end InformationTheory
