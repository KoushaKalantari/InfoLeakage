/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.MaxInformation.Basic
public import InfoLeakage.QIF.MinEntropy

/-!
# Differential privacy bounds min-entropy leakage

This file formalizes, for finite alphabets, the leakage bounds of

* M. S. Alvim, M. E. Andrés, K. Chatzikokolakis, P. Degano, C. Palamidessi, *Differential
  privacy: on the trade-off between utility and information leakage*, FAST 2011, LNCS 7140,
  pp. 39–54, [arXiv:1103.5188](https://arxiv.org/abs/1103.5188); result numbers follow arXiv v3.

A database records the values in `𝒳` (with `v = |𝒳|`) of the `u = |ι|` individuals `ι`, so the
databases are `ι → 𝒳`, and two databases are adjacent if they differ in the value of exactly one
individual (`hammingDist S S' = 1`). A randomized function `K : Kernel (ι → 𝒳) Z` is
`ε`-differentially private (`IsEpsDeltaDP K _ ε 0`). The paper shows that its min-entropy leakage
`I∞(X; Z) = H∞(X) - H∞(X | Z)` (`minEntropyLeakage`) is at most `u log (v e^ε / (v - 1 + e^ε))`
for every prior, that this bound is tight, and that the leakage about one individual, the others
being known, is at most `ε`. Logarithms are natural (nats; the paper uses `log₂`).

## Main definitions

* `individualChannel K D i`: the channel `K_{D⁻}` of Section 4.1, from the value of individual `i`
  to the output, the other individuals having the values of `D`.

## Main statements

* `sum_iSup_le_of_isEpsDeltaDP`, `maxMultLeakage_le_of_isEpsDeltaDP`,
  `minEntropyLeakage_le_of_isEpsDeltaDP`: **Theorem 1**, in the forms
  `∑_z max_x K(z | x) ≤ (v e^ε / (v - 1 + e^ε))^u` (the min-capacity) and
  `I∞(X; Z) ≤ u log (v e^ε / (v - 1 + e^ε))` for every prior.
* `sum_iSup_le_of_isEpsDeltaDP_ne`, `maxMultLeakage_le_of_isEpsDeltaDP_ne`,
  `minEntropyLeakage_le_of_isEpsDeltaDP_ne`: Theorem 1 for one individual (`u = 1`), stated
  directly for a channel on `v` pairwise adjacent inputs: `I∞(X; Z) ≤ log (v e^ε / (v - 1 + e^ε))`.
* `exists_isEpsDeltaDP_hammingDist_minEntropyLeakage_eq`: **Proposition 1**: for every `u`, the
  bound is attained, at the uniform prior, by the `u`-fold product of the `v`-ary randomized
  response; `sum_iSup_eq_of_randomizedResponse` and `exists_isEpsDeltaDP_minEntropyLeakage_eq`
  give the case of `v` pairwise adjacent inputs.
* `isEpsDeltaDP_hammingDist_iff_ne`: for a single individual (`[Unique ι]`), the database setting
  and the setting of pairwise adjacent inputs coincide.
* `minEntropyLeakage_individualChannel_le_log`, `minEntropyLeakage_individualChannel_le`:
  **Theorem 2**: the leakage about one individual is at most `log (v e^ε / (v - 1 + e^ε)) ≤ ε`.

## Paper → Lean (Alvim et al., arXiv v3)

* Definition 1 and the channel formulation of Section 3 → `IsEpsDeltaDP K Adj ε 0` with
  `Adj S S' ↔ hammingDist S S' = 1`, or `Adj = (· ≠ ·)` for a single individual.
* Min-entropy leakage and `C∞` (Section 2.2) → `minEntropyLeakage`, `maxMultLeakage` (from
  `InfoLeakage.QIF.MinEntropy`, with `C∞ = log ML×`).
* Theorem 1 → `minEntropyLeakage_le_of_isEpsDeltaDP`, `maxMultLeakage_le_of_isEpsDeltaDP`,
  `sum_iSup_le_of_isEpsDeltaDP`.
* Proposition 1 → `exists_isEpsDeltaDP_hammingDist_minEntropyLeakage_eq`; for pairwise adjacent
  inputs → `exists_isEpsDeltaDP_minEntropyLeakage_eq`, `sum_iSup_eq_of_randomizedResponse`.
* Section 4.1, `K_{D⁻}` → `individualChannel`; Theorem 2 → `minEntropyLeakage_individualChannel_le`
  (and the sharper `minEntropyLeakage_individualChannel_le_log`).

Not formalized: Proposition 2 (range of bounded size), Lemmas 1–5 of
the appendix (not needed by the proofs below), and Sections 5–6 (utility, optimal mechanisms).

## Implementation notes

The auxiliary lemmas live in the namespace `InformationTheory.DPLeakage`. Here `I∞(X; Z)` is the
min-entropy leakage of Alvim et al., not the max-information `maxInformation` of
`InfoLeakage.MaxInformation.Basic`.

The proof of Theorem 1 does not go through the symmetrization Lemmas 1 and 2 of the paper. It is
a direct counting argument (`DPLeakage.sum_iSup_le_of_forall_mul_le`): by group privacy
(`IsEpsDeltaDP.apply_singleton_le_hammingDist`), `K(z | x) ≥ e^{-ε d(x₀, x)} K(z | x₀)` for all
databases `x, x₀`, where `d` is the Hamming distance, so summing over `x` gives
`∑_x K(z | x) ≥ (1 + (v - 1) e^{-ε})^u max_{x₀} K(z | x₀)`; summing over `z` gives
`v^u ≥ (1 + (v - 1) e^{-ε})^u ∑_z max_x K(z | x)`. The paper's equality (8) is the same identity
`∑_x e^{-ε d(x₀, x)} = (1 + (v - 1) e^{-ε})^u` (`DPLeakage.sum_exp_neg_mul_hammingDist`).
The paper assumes `ε ≥ 0` and `v ≥ 2`. The proofs of Theorem 1 do not use `ε ≥ 0` and allow
`v ≥ 1` (`[Nonempty 𝒳]`), but this extra generality is vacuous: for `ε < 0`, `u ≥ 1` and `v ≥ 2`
no channel is `ε`-differentially private (apply the definition twice to the whole output space).
`ε ≥ 0` is assumed for Theorem 2 and Proposition 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

namespace DPLeakage

/-- The counting argument behind the bounds of Alvim et al.: if every row of the channel matrix
dominates a weighted copy of every other row, `w x₀ x * K x₀ {z} ≤ K x {z}`, and the weights of
each row sum to `W > 0`, then the sum of the column maxima is at most `|D| / W`. -/
lemma sum_iSup_le_of_forall_mul_le {D Z : Type*} [Fintype D] {mD : MeasurableSpace D}
    [Fintype Z] {mZ : MeasurableSpace Z} [MeasurableSingletonClass Z] (K : Kernel D Z)
    [IsMarkovKernel K] (w : D → D → ℝ) {W : ℝ} (hW : 0 < W) (hw0 : ∀ x₀ x, 0 ≤ w x₀ x)
    (hw : ∀ x₀, ∑ x, w x₀ x = W) (h : ∀ x₀ x z, ENNReal.ofReal (w x₀ x) * K x₀ {z} ≤ K x {z}) :
    ∑ z, ⨆ x, K x {z} ≤ ENNReal.ofReal (Fintype.card D / W) := by
  have hcol (z : Z) : ENNReal.ofReal W * ⨆ x, K x {z} ≤ ∑ x, K x {z} := by
    rw [ENNReal.mul_iSup]
    refine iSup_le fun x₀ ↦ ?_
    rw [← hw x₀, ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hw0 x₀ x, Finset.sum_mul]
    exact Finset.sum_le_sum fun x _ ↦ h x₀ x z
  have htot : (∑ z, ⨆ x, K x {z}) * ENNReal.ofReal W ≤ Fintype.card D := by
    calc (∑ z, ⨆ x, K x {z}) * ENNReal.ofReal W
        = ∑ z, ENNReal.ofReal W * ⨆ x, K x {z} := by rw [Finset.sum_mul]; simp_rw [mul_comm]
      _ ≤ ∑ z, ∑ x, K x {z} := Finset.sum_le_sum fun z _ ↦ hcol z
      _ = Fintype.card D := by
        rw [Finset.sum_comm]
        simp [sum_measure_singleton]
  rw [ENNReal.ofReal_div_of_pos hW, ENNReal.ofReal_natCast,
    ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hW)) (Or.inl ENNReal.ofReal_ne_top)]
  exact htot

/-- `∑_a w(b, a) = 1 + (v - 1) e^{-ε}` for the weights `w(b, a) = 1` if `a = b` and `e^{-ε}`
otherwise, on an alphabet with `v` letters. -/
lemma sum_ite_eq_exp_neg {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Nonempty 𝒳] (b : 𝒳)
    (ε : ℝ) : ∑ a, (if b = a then 1 else exp (-ε)) = 1 + (Fintype.card 𝒳 - 1) * exp (-ε) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  have h : ∑ a ∈ Finset.univ.erase b, (if b = a then (1 : ℝ) else exp (-ε)) =
      ∑ a ∈ Finset.univ.erase b, exp (-ε) :=
    Finset.sum_congr rfl fun a ha ↦ by simp [(Finset.ne_of_mem_erase ha).symm]
  rw [h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
  simp

/-- `v / (1 + (v - 1) e^{-ε}) = v e^ε / (v - 1 + e^ε)`. -/
lemma div_one_add_mul_exp_neg {v ε : ℝ} (hv : 1 ≤ v) :
    v / (1 + (v - 1) * exp (-ε)) = v * exp ε / (v - 1 + exp ε) := by
  have h1 : 0 < v - 1 + exp ε := by linarith [exp_pos ε]
  rw [exp_neg, div_eq_div_iff (by positivity) h1.ne']
  field_simp
  ring

/-- Pure differential privacy on one pair of neighbours, pointwise form in `ℝ≥0∞`. -/
lemma apply_singleton_le_of_isEpsDeltaDP {D Z : Type*} {mD : MeasurableSpace D}
    {mZ : MeasurableSpace Z} {M : Kernel D Z} [IsFiniteKernel M] {Adj : D → D → Prop} {ε : ℝ}
    (hM : IsEpsDeltaDP M Adj ε 0) {S S' : D} (h : Adj S S') (z : Z) :
    M S {z} ≤ ENNReal.ofReal (exp ε) * M S' {z} := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (M S) {z}),
    ← ENNReal.ofReal_toReal (measure_ne_top (M S') {z}), ← ENNReal.ofReal_mul (exp_pos _).le]
  have h' := hM h {z}
  simp only [measureReal_def, add_zero] at h'
  exact ENNReal.ofReal_le_ofReal h'

/-- `e^{-ε d(x₀, x)} = ∏_i w(x₀ i, x i)` with `w(b, a) = 1` if `a = b` and `e^{-ε}` otherwise,
where `d` is the Hamming distance. -/
lemma exp_neg_mul_hammingDist {ι 𝒳 : Type*} [Fintype ι] [DecidableEq 𝒳] (x₀ x : ι → 𝒳)
    (ε : ℝ) : exp (-ε * hammingDist x₀ x) = ∏ i, if x₀ i = x i then 1 else exp (-ε) := by
  rw [hammingDist, Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases h : x₀ i = x i <;> simp [h]

/-- `∑_x e^{-ε d(x₀, x)} = (1 + (v - 1) e^{-ε})^u` over the databases `x ∈ 𝒳^ι`, where `v = |𝒳|`,
`u = |ι|` and `d` is the Hamming distance: there are `C(u, d) (v - 1)^d` databases at distance
`d` from `x₀`. -/
lemma sum_exp_neg_mul_hammingDist {ι 𝒳 : Type*} [Fintype ι] [DecidableEq ι] [Fintype 𝒳]
    [DecidableEq 𝒳] [Nonempty 𝒳] (x₀ : ι → 𝒳) (ε : ℝ) :
    ∑ x : ι → 𝒳, exp (-ε * hammingDist x₀ x) =
      (1 + (Fintype.card 𝒳 - 1) * exp (-ε)) ^ Fintype.card ι := by
  simp_rw [exp_neg_mul_hammingDist]
  rw [← Fintype.prod_sum (fun i a ↦ if x₀ i = a then (1 : ℝ) else exp (-ε))]
  simp_rw [sum_ite_eq_exp_neg]
  simp

lemma one_add_mul_exp_neg_pos {v : ℝ} (hv : 1 ≤ v) (ε : ℝ) : 0 < 1 + (v - 1) * exp (-ε) := by
  have := exp_pos (-ε)
  have : 0 ≤ (v - 1) * exp (-ε) := mul_nonneg (by linarith) this.le
  linarith

lemma card_mul_exp_div_nonneg {v : ℝ} (hv : 1 ≤ v) (ε : ℝ) : 0 ≤ v * exp ε / (v - 1 + exp ε) :=
  div_nonneg (mul_nonneg (by linarith) (exp_pos ε).le) (by linarith [exp_pos ε])

/-- `log (v e^ε / (v - 1 + e^ε)) ≤ ε` for `ε ≥ 0` and `v ≥ 1`. -/
lemma log_card_mul_exp_div_le {v ε : ℝ} (hv : 1 ≤ v) (hε : 0 ≤ ε) :
    Real.log (v * exp ε / (v - 1 + exp ε)) ≤ ε := by
  have h1 : 0 < v - 1 + exp ε := by linarith [exp_pos ε]
  have h2 : 1 ≤ exp ε := one_le_exp hε
  rcases (card_mul_exp_div_nonneg hv ε).eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    exact hε
  rw [Real.log_le_iff_le_exp h, div_le_iff₀ h1]
  nlinarith [exp_pos ε]

/-- Multiplicative leakage at a prior is at least `1` and at most the capacity `ML×`. -/
lemma minEntropyLeakage_le_log_of_maxMultLeakage_le {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} [Finite α] [MeasurableSingletonClass α] [Fintype β]
    [MeasurableSingletonClass β] {κ : Kernel α β} [IsMarkovKernel κ] {μ : Measure α}
    [IsProbabilityMeasure μ] {B : ℝ} (hB0 : 0 ≤ B)
    (hB : maxMultLeakage κ ≤ ENNReal.ofReal B) : minEntropyLeakage μ κ ≤ Real.log B := by
  rw [minEntropyLeakage_eq_log_multLeakage]
  have hle : multLeakage μ κ ≤ ENNReal.ofReal B :=
    (le_iSup₂ (f := fun (μ : Measure α) (_ : IsProbabilityMeasure μ) ↦ multLeakage μ κ) μ
      inferInstance).trans hB
  have h1 : 1 ≤ multLeakage μ κ :=
    (ENNReal.le_div_iff_mul_le (Or.inl (vulnerability_ne_zero μ))
      (Or.inl (vulnerability_ne_top μ))).2
      (by rw [one_mul]; exact vulnerability_le_postVulnerability)
  have h1' : 1 ≤ (multLeakage μ κ).toReal := by
    simpa using ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle) h1
  exact Real.log_le_log (by linarith) (ENNReal.toReal_le_of_le_ofReal hB0 hle)

end DPLeakage

open DPLeakage

/-! ### Databases of `u` individuals -/

section Database

variable {ι 𝒳 Z : Type*} [Fintype ι] [Fintype 𝒳] [DecidableEq 𝒳] [Nonempty 𝒳]
  {m𝒳 : MeasurableSpace 𝒳} [Fintype Z] {mZ : MeasurableSpace Z} [MeasurableSingletonClass Z]
  {K : Kernel (ι → 𝒳) Z} [IsMarkovKernel K] {ε : ℝ}

/-- **Theorem 1 of Alvim et al.**, capacity form: if the randomized function `K` on databases
`𝒳^ι` of `u = |ι|` individuals with `v = |𝒳|` values is `ε`-differentially private (neighbours
differ in the value of exactly one individual), then the sum of the column maxima of its channel
matrix is at most `(v e^ε / (v - 1 + e^ε))^u`. -/
theorem sum_iSup_le_of_isEpsDeltaDP (hK : IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε 0) :
    ∑ z, ⨆ x, K x {z} ≤ ENNReal.ofReal
      ((Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) ^ Fintype.card ι) := by
  classical
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  refine (sum_iSup_le_of_forall_mul_le K (fun x₀ x ↦ exp (-ε * hammingDist x₀ x))
    (pow_pos (one_add_mul_exp_neg_pos hv ε) _) (fun _ _ ↦ (exp_pos _).le)
    (fun x₀ ↦ sum_exp_neg_mul_hammingDist x₀ ε) fun x₀ x z ↦ ?_).trans_eq ?_
  · calc ENNReal.ofReal (exp (-ε * hammingDist x₀ x)) * K x₀ {z}
        ≤ ENNReal.ofReal (exp (-ε * hammingDist x₀ x)) *
            (ENNReal.ofReal (exp (ε * hammingDist x₀ x)) * K x {z}) :=
          mul_le_mul_right (hK.apply_singleton_le_hammingDist x₀ x z) _
      _ = K x {z} := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
          simp
  · rw [Fintype.card_fun, Nat.cast_pow, ← div_pow, div_one_add_mul_exp_neg hv]

variable [MeasurableSingletonClass 𝒳]

/-- **Theorem 1 of Alvim et al.**, for the min-capacity: the worst-case multiplicative
leakage `ML× = max_π e^{I∞(X; Z)}` of an `ε`-differentially private randomized function on
databases of `u` individuals with `v` values is at most `(v e^ε / (v - 1 + e^ε))^u`. -/
theorem maxMultLeakage_le_of_isEpsDeltaDP
    (hK : IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε 0) :
    maxMultLeakage K ≤ ENNReal.ofReal
      ((Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) ^ Fintype.card ι) := by
  rw [maxMultLeakage_eq.1]
  exact sum_iSup_le_of_isEpsDeltaDP hK

/-- **Theorem 1 of Alvim et al.**: if the randomized function `K` on databases of `u`
individuals with `v` possible values each is `ε`-differentially private, then for every input
distribution the min-entropy leakage is `I∞(X; Z) ≤ u log (v e^ε / (v - 1 + e^ε))` (in nats; the
paper uses `log₂`). -/
theorem minEntropyLeakage_le_of_isEpsDeltaDP
    (hK : IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε 0) (μ : Measure (ι → 𝒳))
    [IsProbabilityMeasure μ] :
    minEntropyLeakage μ K ≤
      Fintype.card ι * Real.log (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  rw [← Real.log_pow]
  exact minEntropyLeakage_le_log_of_maxMultLeakage_le
    (pow_nonneg (card_mul_exp_div_nonneg hv ε) _) (maxMultLeakage_le_of_isEpsDeltaDP hK)

end Database

/-! ### One individual: every pair of inputs is adjacent -/

section AllAdjacent

variable {𝒳 Z : Type*} [Fintype 𝒳] [Nonempty 𝒳] {m𝒳 : MeasurableSpace 𝒳}
  [Fintype Z] {mZ : MeasurableSpace Z} [MeasurableSingletonClass Z] {K : Kernel 𝒳 Z}
  [IsMarkovKernel K] {ε : ℝ}

/-- **Theorem 1 of Alvim et al. for one individual** (`u = 1`), capacity form: if the channel `K`
on an alphabet of `v` letters is `ε`-differentially private for the relation in which every two
distinct inputs are adjacent, then `∑_z max_x K(z | x) ≤ v e^ε / (v - 1 + e^ε)`. -/
theorem sum_iSup_le_of_isEpsDeltaDP_ne (hK : IsEpsDeltaDP K (· ≠ ·) ε 0) :
    ∑ z, ⨆ x, K x {z} ≤
      ENNReal.ofReal (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  classical
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  refine (sum_iSup_le_of_forall_mul_le K (fun x₀ x ↦ if x₀ = x then 1 else exp (-ε))
    (one_add_mul_exp_neg_pos hv ε) (fun _ _ ↦ by split_ifs <;> positivity)
    (fun x₀ ↦ sum_ite_eq_exp_neg x₀ ε) fun x₀ x z ↦ ?_).trans_eq ?_
  · by_cases h : x₀ = x
    · simp [h]
    calc ENNReal.ofReal (if x₀ = x then 1 else exp (-ε)) * K x₀ {z}
        ≤ ENNReal.ofReal (exp (-ε)) * (ENNReal.ofReal (exp ε) * K x {z}) := by
          simp only [h, ↓reduceIte]
          exact mul_le_mul_right (apply_singleton_le_of_isEpsDeltaDP hK h z) _
      _ = K x {z} := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
          simp
  · rw [div_one_add_mul_exp_neg hv]

variable [MeasurableSingletonClass 𝒳]

/-- **Theorem 1 of Alvim et al. for one individual** (`u = 1`): the min-capacity of an
`ε`-differentially private channel on `v` pairwise adjacent inputs is at most
`v e^ε / (v - 1 + e^ε)`. -/
theorem maxMultLeakage_le_of_isEpsDeltaDP_ne (hK : IsEpsDeltaDP K (· ≠ ·) ε 0) :
    maxMultLeakage K ≤
      ENNReal.ofReal (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  rw [maxMultLeakage_eq.1]
  exact sum_iSup_le_of_isEpsDeltaDP_ne hK

/-- **Theorem 1 of Alvim et al. for one individual** (`u = 1`): for an `ε`-differentially private
channel on `v` pairwise adjacent inputs and every prior, the min-entropy leakage is at most
`log (v e^ε / (v - 1 + e^ε))`. -/
theorem minEntropyLeakage_le_of_isEpsDeltaDP_ne (hK : IsEpsDeltaDP K (· ≠ ·) ε 0)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] :
    minEntropyLeakage μ K ≤
      Real.log (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  exact minEntropyLeakage_le_log_of_maxMultLeakage_le (card_mul_exp_div_nonneg hv ε)
    (maxMultLeakage_le_of_isEpsDeltaDP_ne hK)

end AllAdjacent

/-! ### Leakage about one individual -/

section Individual

variable {ι 𝒳 Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype 𝒳] [DecidableEq 𝒳] [Nonempty 𝒳]
  {m𝒳 : MeasurableSpace 𝒳} [MeasurableSingletonClass 𝒳] [Fintype Z] {mZ : MeasurableSpace Z}
  [MeasurableSingletonClass Z] {K : Kernel (ι → 𝒳) Z} [IsMarkovKernel K] {ε : ℝ}

omit [Fintype 𝒳] [Nonempty 𝒳] in
lemma DPLeakage.hammingDist_update_update {D : ι → 𝒳} {i : ι} {a b : 𝒳} (h : a ≠ b) :
    hammingDist (Function.update D i a) (Function.update D i b) = 1 := by
  rw [hammingDist, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext k
  by_cases hk : k = i <;> simp [hk, h, Function.update_apply]

/-- The channel `K_{D⁻}` of Alvim et al. (Section 4.1): the value of individual `i` is the input,
the values `D⁻` of all other individuals are fixed (those of `D`). It is `K` precomposed with
`a ↦ D[i ↦ a]`. -/
noncomputable def individualChannel (K : Kernel (ι → 𝒳) Z) (D : ι → 𝒳) (i : ι) : Kernel 𝒳 Z :=
  K.comap (Function.update D i) (measurable_of_finite _)

instance (D : ι → 𝒳) (i : ι) : IsMarkovKernel (individualChannel K D i) := by
  unfold individualChannel
  infer_instance

/-- **Theorem 2 of Alvim et al.**: if `K` is `ε`-differentially private, then for all values
`D⁻` of the other individuals and every prior on the value of individual `i`, the min-entropy
leakage about that individual is at most `log (v e^ε / (v - 1 + e^ε))`, hence at most `ε`
(`minEntropyLeakage_individualChannel_le`). -/
theorem minEntropyLeakage_individualChannel_le_log
    (hK : IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε 0) (D : ι → 𝒳) (i : ι)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] :
    minEntropyLeakage μ (individualChannel K D i) ≤
      Real.log (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) :=
  minEntropyLeakage_le_of_isEpsDeltaDP_ne (fun _ _ hab E ↦ hK (hammingDist_update_update hab) E) μ

/-- **Theorem 2 of Alvim et al.**: if `K` is `ε`-differentially private with `ε ≥ 0`, the
min-entropy leakage about any single individual, the others being known, is at most `ε` (the
paper's `log₂ e^ε`, in nats). -/
theorem minEntropyLeakage_individualChannel_le
    (hK : IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε 0) (hε : 0 ≤ ε) (D : ι → 𝒳)
    (i : ι) (μ : Measure 𝒳) [IsProbabilityMeasure μ] :
    minEntropyLeakage μ (individualChannel K D i) ≤ ε :=
  (minEntropyLeakage_individualChannel_le_log hK D i μ).trans
    (log_card_mul_exp_div_le (by exact_mod_cast Fintype.card_pos) hε)

end Individual

/-! ### Tightness: randomized response -/

section Tightness

variable {𝒳 : Type*} [Fintype 𝒳] [Nonempty 𝒳] {m𝒳 : MeasurableSpace 𝒳}
  [MeasurableSingletonClass 𝒳] {ε : ℝ}

/-- On a finite alphabet, a pointwise ratio bound `K S {z} ≤ e^ε K S' {z}` on adjacent inputs gives
pure `ε`-differential privacy for all events. -/
lemma DPLeakage.isEpsDeltaDP_zero_of_forall_apply_singleton_le {D Z : Type*}
    {mD : MeasurableSpace D} [Finite Z] {mZ : MeasurableSpace Z} [MeasurableSingletonClass Z]
    {K : Kernel D Z} [IsFiniteKernel K] {Adj : D → D → Prop}
    (h : ∀ S S', Adj S S' → ∀ z, K S {z} ≤ ENNReal.ofReal (exp ε) * K S' {z}) :
    IsEpsDeltaDP K Adj ε 0 := by
  classical
  have := Fintype.ofFinite Z
  intro S S' hSS' E
  have hE : K S E ≤ ENNReal.ofReal (exp ε) * K S' E := by
    rw [← Set.coe_toFinset E, ← sum_measure_singleton, ← sum_measure_singleton, Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ ↦ h S S' hSS' z
  rw [add_zero, measureReal_def, measureReal_def]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hE
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos ε).le] at this

/-- The rows of the `v`-ary randomized-response matrix
`e^ε / (v - 1 + e^ε) · (1 if z = x, e^{-ε} otherwise)` sum to one. -/
private lemma rr_sum [DecidableEq 𝒳] (ε : ℝ) (x : 𝒳) :
    ∑ z, exp ε / (Fintype.card 𝒳 - 1 + exp ε) * (if x = z then 1 else exp (-ε)) = 1 := by
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  have h1 : 0 < (Fintype.card 𝒳 : ℝ) - 1 + exp ε := by linarith [exp_pos ε]
  rw [← Finset.mul_sum, DPLeakage.sum_ite_eq_exp_neg, div_mul_eq_mul_div,
    div_eq_one_iff_eq h1.ne', mul_add, mul_one, ← mul_assoc, mul_comm (exp ε), mul_assoc,
    exp_neg, mul_inv_cancel₀ (exp_pos ε).ne']
  ring

omit [MeasurableSingletonClass 𝒳] in
/-- Any channel with the matrix of the `v`-ary **randomized response** (report the true value with
probability `e^ε / (v - 1 + e^ε)` and each other value with probability `1 / (v - 1 + e^ε)`)
attains the bound of Theorem 1 of Alvim et al. for one individual:
`∑_z max_x K(z | x) = v e^ε / (v - 1 + e^ε)`. -/
theorem sum_iSup_eq_of_randomizedResponse [DecidableEq 𝒳] (hε : 0 ≤ ε) {K : Kernel 𝒳 𝒳}
    (hK : ∀ x z, K x {z} = ENNReal.ofReal
      (exp ε / (Fintype.card 𝒳 - 1 + exp ε) * (if x = z then 1 else exp (-ε)))) :
    ∑ z, ⨆ x, K x {z} =
      ENNReal.ofReal (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  have h1 : 0 < (Fintype.card 𝒳 : ℝ) - 1 + exp ε := by linarith [exp_pos ε]
  have hcol (z : 𝒳) : ⨆ x, K x {z} = ENNReal.ofReal (exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
    refine le_antisymm (iSup_le fun x ↦ ?_) (le_iSup_of_le z (by simp [hK]))
    rw [hK]
    refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity) ?_)
    split_ifs
    · exact le_rfl
    · exact exp_le_one_iff.2 (neg_nonpos.2 hε)
  simp_rw [hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_assoc]

/-- **Proposition 1 of Alvim et al. for one individual** (`u = 1`): the bound of
`minEntropyLeakage_le_of_isEpsDeltaDP_ne` is tight. For `ε ≥ 0` there is an `ε`-differentially
private channel on `v` pairwise adjacent inputs (the randomized response) whose min-entropy leakage
for the uniform prior, and whose min-capacity, are `log (v e^ε / (v - 1 + e^ε))`. -/
theorem exists_isEpsDeltaDP_minEntropyLeakage_eq (hε : 0 ≤ ε) :
    ∃ K : Kernel 𝒳 𝒳, IsMarkovKernel K ∧ IsEpsDeltaDP K (· ≠ ·) ε 0 ∧
      maxMultLeakage K =
        ENNReal.ofReal (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) ∧
      minEntropyLeakage (uniformOn Set.univ) K =
        Real.log (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  classical
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  set c := exp ε / (Fintype.card 𝒳 - 1 + exp ε)
  have hc : 0 ≤ c := div_nonneg (exp_pos ε).le (by linarith [exp_pos ε])
  set w : 𝒳 → 𝒳 → ℝ := fun x z ↦ c * (if x = z then 1 else exp (-ε))
  have hw0 (x z : 𝒳) : 0 ≤ w x z := mul_nonneg hc (by split_ifs <;> positivity)
  let K : Kernel 𝒳 𝒳 :=
    ⟨fun x ↦ Measure.sum fun z ↦ ENNReal.ofReal (w x z) • Measure.dirac z, measurable_of_finite _⟩
  have hK (x z : 𝒳) : K x {z} = ENNReal.ofReal (w x z) := Measure.sum_smul_dirac_singleton
  have : IsMarkovKernel K := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hK]
    rw [← ENNReal.ofReal_sum_of_nonneg fun z _ ↦ hw0 x z, rr_sum ε x, ENNReal.ofReal_one]⟩⟩
  have hsum := sum_iSup_eq_of_randomizedResponse hε hK
  have hmax : maxMultLeakage K =
      ENNReal.ofReal (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
    rw [maxMultLeakage_eq.1, hsum]
  refine ⟨K, this, ?_, hmax, ?_⟩
  · refine DPLeakage.isEpsDeltaDP_zero_of_forall_apply_singleton_le fun x x' hxx' z ↦ ?_
    rw [hK, hK, ← ENNReal.ofReal_mul (exp_pos ε).le]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [w]
    by_cases hxz : x = z
    · have hx'z : x' ≠ z := hxz ▸ hxx'.symm
      simp only [hxz, hx'z, ↓reduceIte]
      rw [mul_one, mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
    · simp only [hxz, ↓reduceIte]
      split_ifs
      · nlinarith [exp_pos ε, exp_le_one_iff.2 (neg_nonpos.2 hε), one_le_exp hε]
      · exact le_mul_of_one_le_left (mul_nonneg hc (exp_pos _).le) (one_le_exp hε)
  · rw [minEntropyLeakage_eq_log_multLeakage, ← maxMultLeakage_eq.2, hmax,
      ENNReal.toReal_ofReal (DPLeakage.card_mul_exp_div_nonneg hv ε)]

end Tightness

/-! ### Tightness for databases of `u` individuals -/

section TightnessDatabase

variable {ι 𝒳 : Type*} [Fintype ι] [Fintype 𝒳] [DecidableEq 𝒳] [Nonempty 𝒳]
  {m𝒳 : MeasurableSpace 𝒳} [MeasurableSingletonClass 𝒳] {ε : ℝ}

omit [Fintype 𝒳] [Nonempty 𝒳] [MeasurableSingletonClass 𝒳] in
/-- With a single individual, two databases are adjacent iff they are distinct. -/
lemma DPLeakage.hammingDist_eq_one_iff_ne [Unique ι] {S S' : ι → 𝒳} :
    hammingDist S S' = 1 ↔ S ≠ S' := by
  refine ⟨fun h heq ↦ by simp [heq] at h, fun h ↦ le_antisymm ?_ (hammingDist_pos.2 h)⟩
  exact hammingDist_le_card_fintype.trans_eq Fintype.card_unique

omit [Fintype 𝒳] [Nonempty 𝒳] [MeasurableSingletonClass 𝒳] in
/-- With a single individual (`u = 1`), differential privacy for databases differing in one
individual is differential privacy for all pairs of distinct inputs, so the results stated for
`(· ≠ ·)` (`minEntropyLeakage_le_of_isEpsDeltaDP_ne`,
`exists_isEpsDeltaDP_minEntropyLeakage_eq`) are those of the database setting with `u = 1`. -/
theorem isEpsDeltaDP_hammingDist_iff_ne [Unique ι] {Z : Type*} {mZ : MeasurableSpace Z}
    {K : Kernel (ι → 𝒳) Z} {δ : ℝ} :
    IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε δ ↔ IsEpsDeltaDP K (· ≠ ·) ε δ := by
  simp only [IsEpsDeltaDP, DPLeakage.hammingDist_eq_one_iff_ne]

omit [Fintype 𝒳] [Nonempty 𝒳] [MeasurableSingletonClass 𝒳] in
/-- The randomized-response matrix `r(a, b) = c (1 if a = b, e^{-ε} otherwise)`, `c ≥ 0`, satisfies
the `ε`-differential privacy ratio `r(a, b) ≤ e^ε r(a', b)` for all `a, a'`. -/
private lemma rr_le (hε : 0 ≤ ε) {c : ℝ} (hc : 0 ≤ c) (a a' b : 𝒳) :
    c * (if a = b then 1 else exp (-ε)) ≤ exp ε * (c * (if a' = b then 1 else exp (-ε))) := by
  have h1 : 1 ≤ exp ε := one_le_exp hε
  have h2 : exp ε * exp (-ε) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have h3 : 0 ≤ exp (-ε) := (exp_pos _).le
  split_ifs <;> nlinarith [mul_nonneg hc h3]

/-- **Proposition 1 of Alvim et al.**: the bound of Theorem 1 is tight for every number `u` of
individuals. For `ε ≥ 0`, the `u`-fold product of the `v`-ary randomized response is
`ε`-differentially private on databases `𝒳^ι` (neighbours differ in one individual), its
min-capacity is `(v e^ε / (v - 1 + e^ε))^u`, and its min-entropy leakage for the uniform prior is
`u log (v e^ε / (v - 1 + e^ε))`. -/
theorem exists_isEpsDeltaDP_hammingDist_minEntropyLeakage_eq [DecidableEq ι] (hε : 0 ≤ ε) :
    ∃ K : Kernel (ι → 𝒳) (ι → 𝒳), IsMarkovKernel K ∧
      IsEpsDeltaDP K (fun S S' ↦ hammingDist S S' = 1) ε 0 ∧
      maxMultLeakage K = ENNReal.ofReal
        ((Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) ^ Fintype.card ι) ∧
      minEntropyLeakage (uniformOn Set.univ) K =
        Fintype.card ι * Real.log (Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) := by
  have hv : (1 : ℝ) ≤ Fintype.card 𝒳 := by exact_mod_cast Fintype.card_pos
  set c := exp ε / (Fintype.card 𝒳 - 1 + exp ε)
  have hc : 0 ≤ c := div_nonneg (exp_pos ε).le (by linarith [exp_pos ε])
  set r : 𝒳 → 𝒳 → ℝ := fun a b ↦ c * (if a = b then 1 else exp (-ε))
  have hr0 (a b : 𝒳) : 0 ≤ r a b := mul_nonneg hc (by split_ifs <;> positivity)
  have hrow (a : 𝒳) : ∑ b, r a b = 1 := rr_sum ε a
  have hrc (a b : 𝒳) : r a b ≤ c := by
    refine mul_le_of_le_one_right hc ?_
    split_ifs
    · exact le_rfl
    · exact exp_le_one_iff.2 (neg_nonpos.2 hε)
  set w : (ι → 𝒳) → (ι → 𝒳) → ℝ := fun x z ↦ ∏ i, r (x i) (z i)
  have hw0 (x z : ι → 𝒳) : 0 ≤ w x z := Finset.prod_nonneg fun i _ ↦ hr0 _ _
  let K : Kernel (ι → 𝒳) (ι → 𝒳) :=
    ⟨fun x ↦ Measure.sum fun z ↦ ENNReal.ofReal (w x z) • Measure.dirac z, measurable_of_finite _⟩
  have hK (x z : ι → 𝒳) : K x {z} = ENNReal.ofReal (w x z) := Measure.sum_smul_dirac_singleton
  have : IsMarkovKernel K := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hK]
    rw [← ENNReal.ofReal_sum_of_nonneg fun z _ ↦ hw0 x z]
    simp only [w]
    rw [← Fintype.prod_sum (fun i b ↦ r (x i) b), Finset.prod_eq_one fun i _ ↦ hrow (x i),
      ENNReal.ofReal_one]⟩⟩
  have hcol (z : ι → 𝒳) : ⨆ x, K x {z} = ENNReal.ofReal (c ^ Fintype.card ι) := by
    refine le_antisymm (iSup_le fun x ↦ ?_) (le_iSup_of_le z ?_)
    · rw [hK]
      refine ENNReal.ofReal_le_ofReal ?_
      calc w x z ≤ ∏ _i : ι, c := Finset.prod_le_prod₀ (fun i _ ↦ hr0 _ _) fun i _ ↦ hrc _ _
        _ = c ^ Fintype.card ι := by simp
    · rw [hK]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      simp [w, r]
  have hsum : ∑ z, ⨆ x, K x {z} = ENNReal.ofReal
      ((Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) ^ Fintype.card ι) := by
    simp_rw [hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Fintype.card_fun, Nat.cast_pow, ← mul_pow,
      mul_div_assoc]
    rfl
  have hmax : maxMultLeakage K = ENNReal.ofReal
      ((Fintype.card 𝒳 * exp ε / (Fintype.card 𝒳 - 1 + exp ε)) ^ Fintype.card ι) := by
    rw [maxMultLeakage_eq.1, hsum]
  refine ⟨K, this, ?_, hmax, ?_⟩
  · refine DPLeakage.isEpsDeltaDP_zero_of_forall_apply_singleton_le fun x x' hxx' z ↦ ?_
    rw [hK, hK, ← ENNReal.ofReal_mul (exp_pos ε).le]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hxx'
    have heq (i : ι) (hi : i ≠ j) : x i = x' i := by
      by_contra h
      have : i ∈ ({j} : Finset ι) := hj ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩
      exact hi (Finset.mem_singleton.1 this)
    have hrest : ∏ i ∈ Finset.univ.erase j, r (x i) (z i) =
        ∏ i ∈ Finset.univ.erase j, r (x' i) (z i) :=
      Finset.prod_congr rfl fun i hi ↦ by rw [heq i (Finset.ne_of_mem_erase hi)]
    simp only [w]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun i ↦ r (x' i) (z i)) (Finset.mem_univ j), hrest, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (rr_le hε hc _ _ _)
      (Finset.prod_nonneg fun i _ ↦ hr0 _ _)
  · rw [minEntropyLeakage_eq_log_multLeakage, ← maxMultLeakage_eq.2, hmax,
      ENNReal.toReal_ofReal (pow_nonneg (DPLeakage.card_mul_exp_div_nonneg hv ε) _),
      Real.log_pow]

end TightnessDatabase

end InformationTheory
