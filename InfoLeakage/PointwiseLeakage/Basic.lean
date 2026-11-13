/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.GainLeakage.Basic
public import InfoLeakage.MaximalLeakage.MutualInfo
public import InfoLeakage.MaximalLeakage.Properties

/-!
# Pointwise maximal leakage

This file formalizes the closed form and the main properties of *pointwise maximal leakage* (PML)
from S. Saeidian, G. Cervia, T. J. Oechtering and M. Skoglund, *Pointwise maximal leakage*,
IEEE Trans. Inf. Theory 69(12), 2023 ([arXiv:2205.04935](https://arxiv.org/abs/2205.04935));
result numbers follow arXiv v2.

For a secret `X ∼ P_X` and the outcome `y` of a channel `P_{Y|X}`, the pointwise maximal leakage
`ℓ(X → y)` is the logarithm of the largest multiplicative gain, over all randomized functions `U`
of `X`, in the probability of guessing `U` correctly after observing `Y = y` (Definition 1).
Theorem 1 and
Remark 1 evaluate it as
`ℓ(X → y) = log max_{x ∈ supp P_X} P_{X|Y=y}(x) / P_X(x)`
`         = log max_{x ∈ supp P_X} P_{Y|X}(y | x) / P_Y(y)`.
This file takes the closed form as the definition; `InfoLeakage.PointwiseLeakage.Operational`
proves that it equals the operational Definition 1.

We work with finite alphabets: an input law `μ : Measure α` (a probability measure) and a channel
`κ : Kernel α β` (a Markov kernel), with `P_Y = κ ∘ₘ μ`. Logarithms are natural (nats). The
leakage is only meaningful for outcomes `y` with `P_Y(y) > 0`, which the statements assume.

**Scope.** As for `maxLeakageSum`, the definitions only look at atoms: the supremum ranges over
the atoms of `μ`, and `IsEpsPML` and `IsEpsDeltaPML` only constrain outcomes `y` with
`P_Y(y) > 0`. They are meant for countable (in the paper, finite) alphabets. For an atomless
output law they are vacuous or degenerate: for instance `IsEpsPML μ κ ε` then holds for every
`ε`, even `ε < 0`. The results below assume finite alphabets.

## Main definitions

* `pointwiseMaxLeakageRatio μ κ y`: `⨆_{x ∈ supp μ} κ x {y} / P_Y(y)`, in `ℝ≥0∞`; it equals
  `exp ℓ(X → y)` for `P_Y(y) > 0` (for `P_Y(y) = 0` it is `0`, whereas `exp (Real.log 0) = 1`).
* `pointwiseMaxLeakage μ κ y`: `ℓ(X → y)`, its logarithm, in `ℝ`.
* `IsEpsPML μ κ ε`: the almost-sure guarantee `ε`-PML (Definition 4).
* `IsEpsDeltaPML μ κ ε δ`: the tail-bound guarantee `(ε, δ)`-PML (Definition 5).

## Paper-to-Lean map

* Theorem 1, (5), and Remark 1: `pointwiseMaxLeakageRatio_eq_iSup_posterior` (closed form); the
  operational statement is `opPointwiseMaxLeakageRatio_eq` in `Operational.lean`.
* Lemma 1.1 (bounds): `pointwiseMaxLeakage_nonneg`, `one_le_pointwiseMaxLeakageRatio`,
  `pointwiseMaxLeakage_le_neg_log`, `pointwiseMaxLeakageRatio_le_iSup_inv`; equality in the lower
  bound: `pointwiseMaxLeakage_eq_zero_iff`, `pointwiseMaxLeakageRatio_eq_one_iff`.
* Lemma 1.2: `pointwiseMaxLeakage_eq_zero_of_compProd_eq_prod` (independence),
  `pointwiseMaxLeakage_deterministic`, `pointwiseMaxLeakageRatio_deterministic`.
* Lemma 1.3 (pre-processing): `pointwiseMaxLeakage_comp_le_comp`,
  `pointwiseMaxLeakageRatio_comp_le_comp`.
* Lemma 1.4 (post-processing): `exists_pointwiseMaxLeakage_comp_le`,
  `pointwiseMaxLeakageRatio_comp_le_iSup`.
* Lemma 1.6 (composition), with the conditional PML of Definition 3 in closed form:
  `pointwiseMaxLeakage_compProd_le`, `pointwiseMaxLeakageRatio_compProd_le`.
* Definition 4 and equation (13): `IsEpsPML`, `isEpsPML_iff_ae`, `isEpsPML_iff_ratio_le`,
  `isEpsPML_iff_forall_le`.
* Lemma 2.1: `isEpsPML_neg_log`, `PointwiseLeakage.log_two_le_neg_log`. Lemma 2.2:
  `isEpsPML_zero_iff`.
* Definition 5: `IsEpsDeltaPML`; `ε`-PML is `(ε, 0)`-PML: `isEpsDeltaPML_zero_iff`.
* Definition 6 (maximal leakage is `log E[exp ℓ(X → Y)]`): `maxLeakage_eq_log_integral_exp`,
  `sum_mul_pointwiseMaxLeakageRatio`; `ε`-PML implies `L(X → Y) ≤ ε`: `IsEpsPML.maxLeakage_le`.
* Proposition 1.1, 1.2, 1.3 (closedness under processing): `IsEpsPML.preprocess`,
  `IsEpsPML.postprocess`, `IsEpsDeltaPML.preprocess`. Proposition 1.4 is the data-processing
  inequality for maximal leakage, `maxLeakage_comp_le` and `maxLeakage_comp_le_comp`.
* Theorem 4.1 (adaptive composition of `ε`-PML): `IsEpsPML.compProd`.
* Proposition 6: `isEpsPML_of_ldp` (LDP part), `isEpsPML_of_ldi` (LDI part).
* Proposition 7: `mutualInfo_compProd_le_ofReal_integral_pointwiseMaxLeakage`,
  `toReal_mutualInfo_compProd_le_integral_pointwiseMaxLeakage` (`I(X; Y) ≤ E[ℓ(X → Y)]`),
  `IsEpsPML.mutualInfo_le` (7.1), `IsEpsDeltaPML.mutualInfo_le` (7.2).

## Notes on the paper

* Lemma 2.1 (arXiv v2, Section III), a caveat rather than an error: the bound
  `ε_max = -log min_{x ∈ supp P_X} P_X(x) ≥ log 2` needs at least two support points, while the
  lemma is stated for an "arbitrary but fixed prior", which includes point masses (then
  `ε_max = 0`). This is an editorial slip; `PointwiseLeakage.log_two_le_neg_log` proves the bound
  under the two-point hypothesis. The rest of Lemma 2.1 is unaffected.

## Not formalized

* The gain-function view (Theorem 2, Corollary 1), the equality conditions of Lemma 1.1 (upper
  bound), Lemmas 1.3, 1.4, 1.6 and Proposition 7, the "if and only if" part of Lemma 2.1,
  Lemma 1.5, the closedness/EML results (Definitions 7–11, Theorem 3, Propositions 2–4),
  Theorems 4.2–4.5, max-information (Proposition 5), and the `f`-information and
  total-variation results (Propositions 8–9).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β}

section Definitions

/-- The multiplicative form `exp ℓ(X → y) = max_{x ∈ supp P_X} P_{Y|X}(y | x) / P_Y(y)` of the
pointwise maximal leakage from an input `X ∼ μ` to the outcome `y` of the channel `κ`
(Theorem 1 and Remark 1 of Saeidian–Cervia–Oechtering–Skoglund). It is only meaningful for an
outcome `y` with `P_Y(y) ≠ 0`; the supremum ranges over the atoms of `μ`. -/
noncomputable def pointwiseMaxLeakageRatio (μ : Measure α) (κ : Kernel α β) (y : β) : ℝ≥0∞ :=
  ⨆ (x) (_ : μ {x} ≠ 0), κ x {y} / (κ ∘ₘ μ) {y}

/-- The **pointwise maximal leakage** `ℓ(X → y) = log max_{x ∈ supp P_X} P_{X|Y=y}(x) / P_X(x)`
from an input `X ∼ μ` to the outcome `y` of the channel `κ`, in nats (closed form of Theorem 1 of
Saeidian–Cervia–Oechtering–Skoglund; `Operational.lean` proves that it equals their operational
Definition 1). It is only meaningful for an outcome `y` with `P_Y(y) ≠ 0`. -/
noncomputable def pointwiseMaxLeakage (μ : Measure α) (κ : Kernel α β) (y : β) : ℝ :=
  Real.log (pointwiseMaxLeakageRatio μ κ y).toReal

/-- **`ε`-PML** (the almost-sure guarantee, Definition 4 of Saeidian–Cervia–Oechtering–Skoglund):
for the prior `μ`, the mechanism `κ` satisfies `ε`-PML if `ℓ(X → y) ≤ ε` for every outcome `y`
with `P_Y(y) > 0`. For a countable output alphabet this is `P_Y[ℓ(X → Y) ≤ ε] = 1`
(`isEpsPML_iff_ae`). Only atoms of `P_Y` are constrained, so for an atomless output law the
condition is vacuous: the definition is meant for countable (in the paper, finite) alphabets. -/
def IsEpsPML (μ : Measure α) (κ : Kernel α β) (ε : ℝ) : Prop :=
  ∀ y, (κ ∘ₘ μ) {y} ≠ 0 → pointwiseMaxLeakage μ κ y ≤ ε

end Definitions

section Bounds

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ]

namespace PointwiseLeakage

omit [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
/-- The atom `x` contributes `κ x {y} * μ {x}` to `P_Y(y)`. -/
lemma mul_le_comp_apply_singleton (x : α) (y : β) : κ x {y} * μ {x} ≤ (κ ∘ₘ μ) {y} := by
  have := Fintype.ofFinite α
  rw [comp_apply_singleton]
  exact Finset.single_le_sum (f := fun x ↦ κ x {y} * μ {x}) (fun _ _ ↦ zero_le)
    (Finset.mem_univ x)

omit [Finite α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
/-- An outcome of probability zero has probability zero under every atom of the input law. -/
lemma apply_eq_zero_of_comp_eq_zero {x : α} (hx : μ {x} ≠ 0) {y : β}
    (hy : (κ ∘ₘ μ) {y} = 0) : κ x {y} = 0 := by
  by_contra h
  exact Measure.comp_apply_ne_zero (measurableSet_singleton y) hx h hy

end PointwiseLeakage

open PointwiseLeakage

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
/-- Every atom `x` of `μ` gives the lower bound `P_{Y|X}(y | x) / P_Y(y) ≤ exp ℓ(X → y)`. -/
lemma div_le_pointwiseMaxLeakageRatio {x : α} (hx : μ {x} ≠ 0) (y : β) :
    κ x {y} / (κ ∘ₘ μ) {y} ≤ pointwiseMaxLeakageRatio μ κ y :=
  le_iSup₂ (f := fun x (_ : μ {x} ≠ 0) ↦ κ x {y} / (κ ∘ₘ μ) {y}) x hx

omit [Finite α] [MeasurableSingletonClass α] in
/-- Every atom `x` of `μ` satisfies `P_{Y|X}(y | x) ≤ exp ℓ(X → y) · P_Y(y)`. -/
lemma apply_le_pointwiseMaxLeakageRatio_mul {x : α} (hx : μ {x} ≠ 0) (y : β) :
    κ x {y} ≤ pointwiseMaxLeakageRatio μ κ y * (κ ∘ₘ μ) {y} := by
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · simp [apply_eq_zero_of_comp_eq_zero hx hy]
  · exact (ENNReal.div_le_iff hy (measure_ne_top _ _)).1 (div_le_pointwiseMaxLeakageRatio hx y)

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] in
/-- `exp ℓ(X → y) ≤ 1 / P_Y(y)`. -/
lemma pointwiseMaxLeakageRatio_le_inv (y : β) :
    pointwiseMaxLeakageRatio μ κ y ≤ ((κ ∘ₘ μ) {y})⁻¹ :=
  iSup₂_le fun x _ ↦ by
    rw [ENNReal.div_eq_inv_mul]
    exact mul_le_of_le_one_right' prob_le_one

omit [Finite α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
/-- Off the support of `P_Y` the (meaningless) ratio is `0`. -/
lemma pointwiseMaxLeakageRatio_eq_zero {y : β} (hy : (κ ∘ₘ μ) {y} = 0) :
    pointwiseMaxLeakageRatio μ κ y = 0 :=
  le_antisymm (iSup₂_le fun x hx ↦ by simp [apply_eq_zero_of_comp_eq_zero hx hy]) zero_le

omit [Finite α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- `exp ℓ(X → y)` is finite. -/
lemma pointwiseMaxLeakageRatio_ne_top (y : β) : pointwiseMaxLeakageRatio μ κ y ≠ ∞ := by
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · simp [pointwiseMaxLeakageRatio_eq_zero hy]
  · exact ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 hy) (pointwiseMaxLeakageRatio_le_inv y)

/-- **Lemma 1.1 (lower bound)** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form:
`1 ≤ exp ℓ(X → y)` for every outcome `y` with `P_Y(y) > 0`. -/
theorem one_le_pointwiseMaxLeakageRatio {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    1 ≤ pointwiseMaxLeakageRatio μ κ y := by
  have := Fintype.ofFinite α
  set R := pointwiseMaxLeakageRatio μ κ y
  have h : 1 * (κ ∘ₘ μ) {y} ≤ R * (κ ∘ₘ μ) {y} :=
    calc 1 * (κ ∘ₘ μ) {y} = ∑ x, κ x {y} * μ {x} := by rw [one_mul, comp_apply_singleton]
      _ ≤ ∑ x, R * (κ ∘ₘ μ) {y} * μ {x} := Finset.sum_le_sum fun x _ ↦ by
          by_cases hx : μ {x} = 0
          · simp [hx]
          · exact mul_le_mul_left (apply_le_pointwiseMaxLeakageRatio_mul hx y) _
      _ = R * (κ ∘ₘ μ) {y} := by
          rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
  exact (ENNReal.mul_le_mul_iff_left hy (measure_ne_top _ _)).1 h

/-- Real-valued form of `one_le_pointwiseMaxLeakageRatio`. -/
lemma one_le_toReal_pointwiseMaxLeakageRatio {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    1 ≤ (pointwiseMaxLeakageRatio μ κ y).toReal := by
  simpa using ENNReal.toReal_mono (pointwiseMaxLeakageRatio_ne_top y)
    (one_le_pointwiseMaxLeakageRatio hy)

/-- **Lemma 1.1 (lower bound)** of Saeidian–Cervia–Oechtering–Skoglund: pointwise maximal leakage
is nonnegative, `0 ≤ ℓ(X → y)` for every outcome `y` with `P_Y(y) > 0`. -/
theorem pointwiseMaxLeakage_nonneg {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    0 ≤ pointwiseMaxLeakage μ κ y :=
  Real.log_nonneg (one_le_toReal_pointwiseMaxLeakageRatio hy)

omit [IsMarkovKernel κ] in
/-- **Lemma 1.1 (upper bound)** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form:
`exp ℓ(X → y) ≤ max_{x ∈ supp P_X} 1 / P_X(x)`, for every outcome `y`. -/
theorem pointwiseMaxLeakageRatio_le_iSup_inv (y : β) :
    pointwiseMaxLeakageRatio μ κ y ≤ ⨆ (x) (_ : μ {x} ≠ 0), (μ {x})⁻¹ := by
  refine iSup₂_mono fun x hx ↦ ENNReal.div_le_of_le_mul ?_
  calc κ x {y} = (μ {x})⁻¹ * (κ x {y} * μ {x}) := by
        rw [mul_comm (κ x {y}), ← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _),
          one_mul]
    _ ≤ (μ {x})⁻¹ * (κ ∘ₘ μ) {y} := by gcongr; exact mul_le_comp_apply_singleton x y

/-- `ℓ(X → y) ≤ c` iff `exp ℓ(X → y) ≤ e^c`, for an outcome with `P_Y(y) > 0`. -/
lemma pointwiseMaxLeakage_le_iff {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) {c : ℝ} :
    pointwiseMaxLeakage μ κ y ≤ c ↔
      pointwiseMaxLeakageRatio μ κ y ≤ ENNReal.ofReal (Real.exp c) := by
  have hpos : 0 < (pointwiseMaxLeakageRatio μ κ y).toReal := by
    linarith [one_le_toReal_pointwiseMaxLeakageRatio hy]
  rw [pointwiseMaxLeakage, Real.log_le_iff_le_exp hpos,
    ENNReal.le_ofReal_iff_toReal_le (pointwiseMaxLeakageRatio_ne_top y) (Real.exp_pos c).le]

/-- **Lemma 1.1 (upper bound)** of Saeidian–Cervia–Oechtering–Skoglund:
`ℓ(X → y) ≤ -log min_{x ∈ supp P_X} P_X(x)`. The minimum is taken at an atom `x₀` of `μ` of
smallest mass. -/
theorem pointwiseMaxLeakage_le_neg_log {x₀ : α} (hx₀ : μ {x₀} ≠ 0)
    (hmin : ∀ x, μ {x} ≠ 0 → μ {x₀} ≤ μ {x}) {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakage μ κ y ≤ -Real.log (μ {x₀}).toReal := by
  have hR : pointwiseMaxLeakageRatio μ κ y ≤ (μ {x₀})⁻¹ :=
    (pointwiseMaxLeakageRatio_le_iSup_inv y).trans
      (iSup₂_le fun x hx ↦ ENNReal.inv_le_inv.2 (hmin x hx))
  rw [pointwiseMaxLeakage, ← Real.log_inv]
  refine Real.log_le_log (by linarith [one_le_toReal_pointwiseMaxLeakageRatio hy]) ?_
  rw [← ENNReal.toReal_inv]
  exact ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hx₀) hR


omit [Finite α] [MeasurableSingletonClass β] [IsMarkovKernel κ] in
/-- If the support of `P_X` has two points, its smallest mass is at most `1 / 2`, so that
`ε_max = -log min_{x ∈ supp P_X} P_X(x) ≥ log 2` (Lemma 2.1). -/
lemma PointwiseLeakage.log_two_le_neg_log {x₀ x₁ : α} (hx₀ : μ {x₀} ≠ 0) (hne : x₁ ≠ x₀)
    (hmin : ∀ x, μ {x} ≠ 0 → μ {x₀} ≤ μ {x}) (hx₁ : μ {x₁} ≠ 0) :
    Real.log 2 ≤ -Real.log (μ {x₀}).toReal := by
  have hp : 0 < (μ {x₀}).toReal := ENNReal.toReal_pos hx₀ (measure_ne_top _ _)
  have h_sum : μ {x₀} + μ {x₁} ≤ 1 := by
    rw [← measure_union (Set.disjoint_singleton.2 hne.symm) (measurableSet_singleton x₁)]
    exact prob_le_one
  have h2 : 2 * (μ {x₀}).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top
      ((add_le_add_right (hmin x₁ hx₁) _).trans h_sum)
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one,
      ← two_mul] at h
  rw [← Real.log_inv]
  refine Real.log_le_log two_pos ?_
  rw [le_inv_comm₀ two_pos hp]
  linarith

end Bounds

section ZeroLeakage

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ]

open PointwiseLeakage

/-- **Lemma 1.1 (equality in the lower bound)** of Saeidian–Cervia–Oechtering–Skoglund,
multiplicative form: `exp ℓ(X → y) = 1` iff `P_{Y|X}(y | x) = P_{Y|X}(y | x')` for all
`x, x' ∈ supp P_X`. -/
theorem pointwiseMaxLeakageRatio_eq_one_iff {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakageRatio μ κ y = 1 ↔
      ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → κ x {y} = κ x' {y} := by
  have := Fintype.ofFinite α
  have hp_top : (κ ∘ₘ μ) {y} ≠ ∞ := measure_ne_top _ _
  have hp_sum : (κ ∘ₘ μ) {y} = ∑ x, κ x {y} * μ {x} := comp_apply_singleton _ _ _
  constructor
  · intro h
    -- Every atom has `κ x {y} ≤ P_Y(y)`, and the `μ`-average of `κ · {y}` is `P_Y(y)`.
    have h_le (x : α) : κ x {y} * μ {x} ≤ (κ ∘ₘ μ) {y} * μ {x} := by
      by_cases hx : μ {x} = 0
      · simp [hx]
      · simpa [h] using
          mul_le_mul_left (apply_le_pointwiseMaxLeakageRatio_mul (κ := κ) hx y) (μ {x})
    have h_ne_top (x : α) : (κ ∘ₘ μ) {y} * μ {x} ≠ ∞ :=
      ENNReal.mul_ne_top hp_top (measure_ne_top _ _)
    have h_sum : ∑ x, (κ x {y} * μ {x}).toReal = ∑ x, ((κ ∘ₘ μ) {y} * μ {x}).toReal := by
      rw [← ENNReal.toReal_sum fun x _ ↦ ne_top_of_le_ne_top (h_ne_top x) (h_le x),
        ← ENNReal.toReal_sum fun x _ ↦ h_ne_top x, ← hp_sum, ← Finset.mul_sum,
        sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
    have h_eq (x : α) (hx : μ {x} ≠ 0) : κ x {y} = (κ ∘ₘ μ) {y} := by
      have h_x := (Finset.sum_eq_sum_iff_of_le fun x _ ↦
        ENNReal.toReal_mono (h_ne_top x) (h_le x)).1 h_sum x (Finset.mem_univ x)
      rw [ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top (h_ne_top x) (h_le x))
        (h_ne_top x)] at h_x
      exact (ENNReal.mul_left_inj hx (measure_ne_top _ _)).1 h_x
    intro x x' hx hx'
    rw [h_eq x hx, h_eq x' hx']
  · intro h
    obtain ⟨x₀, hx₀⟩ := μ.exists_measure_singleton_ne_zero
    have hp_eq : (κ ∘ₘ μ) {y} = κ x₀ {y} := by
      rw [hp_sum]
      calc ∑ x, κ x {y} * μ {x} = ∑ x, κ x₀ {y} * μ {x} := Finset.sum_congr rfl fun x _ ↦ by
            by_cases hx : μ {x} = 0
            · simp [hx]
            · rw [h x x₀ hx hx₀]
        _ = κ x₀ {y} := by
            rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
    refine le_antisymm (iSup₂_le fun x hx ↦ ?_) ?_
    · rw [h x x₀ hx hx₀, ← hp_eq, ENNReal.div_self hy hp_top]
    · calc (1 : ℝ≥0∞) = κ x₀ {y} / (κ ∘ₘ μ) {y} := by rw [← hp_eq, ENNReal.div_self hy hp_top]
        _ ≤ _ := div_le_pointwiseMaxLeakageRatio hx₀ y

/-- **Lemma 1.1 (equality in the lower bound)** of Saeidian–Cervia–Oechtering–Skoglund:
`ℓ(X → y) = 0` iff `P_{Y|X}(y | x) = P_{Y|X}(y | x')` for all `x, x' ∈ supp P_X`. -/
theorem pointwiseMaxLeakage_eq_zero_iff {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakage μ κ y = 0 ↔
      ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → κ x {y} = κ x' {y} := by
  rw [← pointwiseMaxLeakageRatio_eq_one_iff hy, ← ENNReal.toReal_eq_one_iff]
  exact ⟨Real.eq_one_of_pos_of_log_eq_zero
    (by linarith [one_le_toReal_pointwiseMaxLeakageRatio hy]),
    fun h ↦ by rw [pointwiseMaxLeakage, h, Real.log_one]⟩

/-- **Lemma 1.2 (independence)** of Saeidian–Cervia–Oechtering–Skoglund: if `X` and `Y` are
independent, i.e. `P_{XY} = P_X × P_Y`, then `ℓ(X → y) = 0` for every outcome `y` with
`P_Y(y) > 0`. -/
theorem pointwiseMaxLeakage_eq_zero_of_compProd_eq_prod [Finite β]
    (h : μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ)) {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakage μ κ y = 0 := by
  have := Fintype.ofFinite β
  have hrow := maxLeakage_eq_zero_iff.1 (maxLeakage_eq_zero_iff_compProd_eq_prod.2 h)
  exact (pointwiseMaxLeakage_eq_zero_iff hy).2 fun x x' hx hx' ↦ by rw [hrow x x' hx hx']

omit [IsProbabilityMeasure μ] in
/-- **Lemma 1.2 (deterministic mappings)** of Saeidian–Cervia–Oechtering–Skoglund,
multiplicative form: if `Y = f(X)`, then `exp ℓ(X → y) = 1 / P_Y(y)`. -/
theorem pointwiseMaxLeakageRatio_deterministic {f : α → β} (hf : Measurable f) {y : β}
    (hy : (Kernel.deterministic f hf ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakageRatio μ (Kernel.deterministic f hf) y =
      ((Kernel.deterministic f hf ∘ₘ μ) {y})⁻¹ := by
  classical
  have := Fintype.ofFinite α
  have hκ (x : α) : Kernel.deterministic f hf x {y} = if f x = y then 1 else 0 := by
    simp [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
      Set.indicator]
  obtain ⟨x₀, hx₀, hfx₀⟩ : ∃ x, μ {x} ≠ 0 ∧ f x = y := by
    by_contra! h
    refine hy ?_
    rw [comp_apply_singleton]
    exact Finset.sum_eq_zero fun x _ ↦ by
      by_cases hx : μ {x} = 0
      · simp [hx]
      · simp [hκ, h x hx]
  refine le_antisymm (pointwiseMaxLeakageRatio_le_inv y) ?_
  calc ((Kernel.deterministic f hf ∘ₘ μ) {y})⁻¹
      = Kernel.deterministic f hf x₀ {y} / (Kernel.deterministic f hf ∘ₘ μ) {y} := by
        simp [hκ, hfx₀]
    _ ≤ _ := div_le_pointwiseMaxLeakageRatio hx₀ y

omit [IsProbabilityMeasure μ] in
/-- **Lemma 1.2 (deterministic mappings)** of Saeidian–Cervia–Oechtering–Skoglund: if `Y = f(X)`,
then `ℓ(X → y) = -log P_Y(y)` for every outcome `y` with `P_Y(y) > 0`. -/
theorem pointwiseMaxLeakage_deterministic {f : α → β} (hf : Measurable f) {y : β}
    (hy : (Kernel.deterministic f hf ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakage μ (Kernel.deterministic f hf) y =
      -Real.log ((Kernel.deterministic f hf ∘ₘ μ) {y}).toReal := by
  rw [pointwiseMaxLeakage, pointwiseMaxLeakageRatio_deterministic hf hy, ENNReal.toReal_inv,
    Real.log_inv]

end ZeroLeakage

section DataProcessing

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
  (η : Kernel β γ) [IsMarkovKernel η]

open PointwiseLeakage

omit [Finite α] [MeasurableSingletonClass α] in
/-- **Lemma 1.3 (pre-processing)** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form:
for a Markov chain `X - Y - Z`, with `Y` the output of `κ` and `Z` the output of `η`,
`exp ℓ(X → z) ≤ exp ℓ(Y → z)`, where `ℓ(Y → z)` is computed for the law `P_Y = κ ∘ₘ μ` of `Y`. -/
theorem pointwiseMaxLeakageRatio_comp_le_comp (z : γ) :
    pointwiseMaxLeakageRatio μ (η ∘ₖ κ) z ≤ pointwiseMaxLeakageRatio (κ ∘ₘ μ) η z := by
  have := Fintype.ofFinite β
  set R := pointwiseMaxLeakageRatio (κ ∘ₘ μ) η z
  refine iSup₂_le fun x hx ↦ ENNReal.div_le_of_le_mul ?_
  rw [← Measure.comp_assoc, Kernel.comp_apply_eq_sum _ _ _ (measurableSet_singleton z)]
  calc ∑ y, η y {z} * κ x {y} ≤ ∑ y, R * (η ∘ₘ (κ ∘ₘ μ)) {z} * κ x {y} :=
        Finset.sum_le_sum fun y _ ↦ by
          by_cases hy : (κ ∘ₘ μ) {y} = 0
          · simp [apply_eq_zero_of_comp_eq_zero hx hy]
          · exact mul_le_mul_left (apply_le_pointwiseMaxLeakageRatio_mul hy z) _
    _ = R * (η ∘ₘ (κ ∘ₘ μ)) {z} := by
        rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]

/-- **Lemma 1.3 (pre-processing)** of Saeidian–Cervia–Oechtering–Skoglund: for a Markov chain
`X - Y - Z`, with `Y` the output of `κ` and `Z` the output of `η`, `ℓ(X → z) ≤ ℓ(Y → z)` for
every outcome `z` with `P_Z(z) > 0`, where `ℓ(Y → z)` is computed for the law `P_Y = κ ∘ₘ μ`. -/
theorem pointwiseMaxLeakage_comp_le_comp {z : γ} (hz : ((η ∘ₖ κ) ∘ₘ μ) {z} ≠ 0) :
    pointwiseMaxLeakage μ (η ∘ₖ κ) z ≤ pointwiseMaxLeakage (κ ∘ₘ μ) η z := by
  refine Real.log_le_log (by linarith [one_le_toReal_pointwiseMaxLeakageRatio hz]) ?_
  exact ENNReal.toReal_mono (pointwiseMaxLeakageRatio_ne_top z)
    (pointwiseMaxLeakageRatio_comp_le_comp η z)

omit [Finite α] [MeasurableSingletonClass α] [IsMarkovKernel η] in
/-- **Lemma 1.4 (post-processing)** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form:
for a Markov chain `X - Y - Z`, with `Y` the output of `κ` and `Z` the output of `η`,
`exp ℓ(X → z) ≤ max_{y ∈ supp P_Y} exp ℓ(X → y)`. -/
theorem pointwiseMaxLeakageRatio_comp_le_iSup (z : γ) :
    pointwiseMaxLeakageRatio μ (η ∘ₖ κ) z ≤
      ⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0), pointwiseMaxLeakageRatio μ κ y := by
  have := Fintype.ofFinite β
  set M := ⨆ (y) (_ : (κ ∘ₘ μ) {y} ≠ 0), pointwiseMaxLeakageRatio μ κ y
  refine iSup₂_le fun x hx ↦ ENNReal.div_le_of_le_mul ?_
  rw [Kernel.comp_apply_eq_sum _ _ _ (measurableSet_singleton z), ← Measure.comp_assoc,
    comp_apply_singleton, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  rw [mul_left_comm]
  gcongr
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · simp [apply_eq_zero_of_comp_eq_zero hx hy]
  · exact (apply_le_pointwiseMaxLeakageRatio_mul hx y).trans <| mul_le_mul_left
      (le_iSup₂ (f := fun y (_ : (κ ∘ₘ μ) {y} ≠ 0) ↦ pointwiseMaxLeakageRatio μ κ y) y hy) _

/-- **Lemma 1.4 (post-processing)** of Saeidian–Cervia–Oechtering–Skoglund: for a Markov chain
`X - Y - Z`, with `Y` the output of `κ` and `Z` the output of `η`, every outcome `z` with
`P_Z(z) > 0` satisfies `ℓ(X → z) ≤ max_{y ∈ supp P_Y} ℓ(X → y)`: some `y ∈ supp P_Y` has
`ℓ(X → z) ≤ ℓ(X → y)`. -/
theorem exists_pointwiseMaxLeakage_comp_le {z : γ} (hz : ((η ∘ₖ κ) ∘ₘ μ) {z} ≠ 0) :
    ∃ y, (κ ∘ₘ μ) {y} ≠ 0 ∧ pointwiseMaxLeakage μ (η ∘ₖ κ) z ≤ pointwiseMaxLeakage μ κ y := by
  classical
  have := Fintype.ofFinite β
  set S := Finset.univ.filter fun y : β ↦ (κ ∘ₘ μ) {y} ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨y, hy⟩ := (κ ∘ₘ μ).exists_measure_singleton_ne_zero
    exact ⟨y, by simpa [S] using hy⟩
  obtain ⟨y, hyS, hy_max⟩ := S.exists_max_image (pointwiseMaxLeakageRatio μ κ) hS
  have hy : (κ ∘ₘ μ) {y} ≠ 0 := by simpa [S] using hyS
  refine ⟨y, hy, Real.log_le_log (by linarith [one_le_toReal_pointwiseMaxLeakageRatio hz]) ?_⟩
  refine ENNReal.toReal_mono (pointwiseMaxLeakageRatio_ne_top y)
    ((pointwiseMaxLeakageRatio_comp_le_iSup η z).trans (iSup₂_le fun y' hy' ↦ ?_))
  exact hy_max y' (by simpa [S] using hy')

end DataProcessing

section Guarantees

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] {ε : ℝ}

open PointwiseLeakage

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] in
/-- An `ε`-PML mechanism is `ε'`-PML for every `ε' ≥ ε`. -/
lemma IsEpsPML.mono {ε' : ℝ} (h : IsEpsPML μ κ ε) (hε : ε ≤ ε') : IsEpsPML μ κ ε' :=
  fun y hy ↦ (h y hy).trans hε

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] [IsProbabilityMeasure μ]
  [IsMarkovKernel κ] in
/-- **Definition 4** of Saeidian–Cervia–Oechtering–Skoglund as stated there: for a countable output
alphabet, `ε`-PML holds iff `P_Y[ℓ(X → Y) ≤ ε] = 1`. -/
theorem isEpsPML_iff_ae [Countable β] :
    IsEpsPML μ κ ε ↔ ∀ᵐ y ∂(κ ∘ₘ μ), pointwiseMaxLeakage μ κ y ≤ ε :=
  ae_iff_of_countable.symm

/-- `ε`-PML in multiplicative form: `exp ℓ(X → y) ≤ e^ε` for every `y ∈ supp P_Y`. -/
theorem isEpsPML_iff_ratio_le : IsEpsPML μ κ ε ↔
    ∀ y, (κ ∘ₘ μ) {y} ≠ 0 → pointwiseMaxLeakageRatio μ κ y ≤ ENNReal.ofReal (Real.exp ε) :=
  forall₂_congr fun _ hy ↦ pointwiseMaxLeakage_le_iff hy

/-- **Equation (13)** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form: `ε`-PML holds
iff the information density `i(x; y) = log P_{Y|X}(y | x) / P_Y(y)` is at most `ε` on the support
of `P_{XY}`, i.e. `P_{Y|X}(y | x) ≤ e^ε P_Y(y)` for every `x ∈ supp P_X` and every `y`. -/
theorem isEpsPML_iff_forall_le : IsEpsPML μ κ ε ↔
    ∀ x, μ {x} ≠ 0 → ∀ y, κ x {y} ≤ ENNReal.ofReal (Real.exp ε) * (κ ∘ₘ μ) {y} := by
  rw [isEpsPML_iff_ratio_le]
  refine ⟨fun h x hx y ↦ ?_, fun h y _ ↦ iSup₂_le fun x hx ↦ ENNReal.div_le_of_le_mul (h x hx y)⟩
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · simp [apply_eq_zero_of_comp_eq_zero hx hy]
  · exact (apply_le_pointwiseMaxLeakageRatio_mul hx y).trans (mul_le_mul_left (h y hy) _)

/-- **Lemma 2.1** of Saeidian–Cervia–Oechtering–Skoglund: every mechanism satisfies
`ε_max`-PML, where `ε_max = -log min_{x ∈ supp P_X} P_X(x)` (attained at the atom `x₀`). -/
theorem isEpsPML_neg_log {x₀ : α} (hx₀ : μ {x₀} ≠ 0) (hmin : ∀ x, μ {x} ≠ 0 → μ {x₀} ≤ μ {x}) :
    IsEpsPML μ κ (-Real.log (μ {x₀}).toReal) :=
  fun _ hy ↦ pointwiseMaxLeakage_le_neg_log hx₀ hmin hy

/-- **Lemma 2.2** of Saeidian–Cervia–Oechtering–Skoglund: a mechanism satisfies `0`-PML iff `X`
and `Y` are independent, i.e. `P_{XY} = P_X × P_Y`. -/
theorem isEpsPML_zero_iff [Finite β] : IsEpsPML μ κ 0 ↔ μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ) := by
  have := Fintype.ofFinite β
  refine ⟨fun h ↦ ?_, fun h y hy ↦ (pointwiseMaxLeakage_eq_zero_of_compProd_eq_prod h hy).le⟩
  refine maxLeakage_eq_zero_iff_compProd_eq_prod.1 (maxLeakage_eq_zero_iff.2 fun x x' hx hx' ↦ ?_)
  refine Measure.ext_of_singleton fun y ↦ ?_
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · rw [apply_eq_zero_of_comp_eq_zero hx hy, apply_eq_zero_of_comp_eq_zero hx' hy]
  · exact (pointwiseMaxLeakage_eq_zero_iff hy).1
      ((h y hy).antisymm (pointwiseMaxLeakage_nonneg hy)) x x' hx hx'

omit [Finite α] [MeasurableSingletonClass α] in
/-- Multiplicative form of `maxLeakage_eq_log_integral_exp`:
`∑_y P_Y(y) exp ℓ(X → y) = ∑_y max_{x ∈ supp P_X} P_{Y|X}(y | x)`. -/
theorem sum_mul_pointwiseMaxLeakageRatio [Fintype β] :
    ∑ y, (κ ∘ₘ μ) {y} * pointwiseMaxLeakageRatio μ κ y = maxLeakageSum μ κ := by
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · rw [hy, zero_mul]
    exact le_antisymm zero_le (iSup₂_le fun x hx ↦ (apply_eq_zero_of_comp_eq_zero hx hy).le)
  · rw [pointwiseMaxLeakageRatio, ENNReal.mul_iSup]
    refine iSup_congr fun x ↦ ?_
    rw [ENNReal.mul_iSup]
    exact iSup_congr fun _ ↦ ENNReal.mul_div_cancel hy (measure_ne_top _ _)

/-- **Definition 6** of Saeidian–Cervia–Oechtering–Skoglund (average-case guarantee): maximal
leakage is the logarithm of the expected exponentiated pointwise maximal leakage,
`L(X → Y) = log E_{Y ∼ P_Y}[exp ℓ(X → Y)]`. -/
theorem maxLeakage_eq_log_integral_exp [Fintype β] :
    maxLeakage μ κ = Real.log (∫ y, Real.exp (pointwiseMaxLeakage μ κ y) ∂(κ ∘ₘ μ)) := by
  rw [maxLeakage, ← sum_mul_pointwiseMaxLeakageRatio, integral_fintype .of_finite,
    ENNReal.toReal_sum fun y _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (pointwiseMaxLeakageRatio_ne_top y)]
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [smul_eq_mul, measureReal_def, ENNReal.toReal_mul]
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · simp [hy]
  · rw [pointwiseMaxLeakage,
      Real.exp_log (by linarith [one_le_toReal_pointwiseMaxLeakageRatio hy])]

/-- The almost-sure guarantee implies the average-case guarantee (Definitions 4 and 6 of
Saeidian–Cervia–Oechtering–Skoglund): if `κ` satisfies `ε`-PML then `L(X → Y) ≤ ε`. -/
theorem IsEpsPML.maxLeakage_le [Fintype β] (h : IsEpsPML μ κ ε) : maxLeakage μ κ ≤ ε := by
  have hS : maxLeakageSum μ κ ≤ ENNReal.ofReal (Real.exp ε) := by
    rw [← sum_mul_pointwiseMaxLeakageRatio]
    calc ∑ y, (κ ∘ₘ μ) {y} * pointwiseMaxLeakageRatio μ κ y
        ≤ ∑ y, (κ ∘ₘ μ) {y} * ENNReal.ofReal (Real.exp ε) := Finset.sum_le_sum fun y _ ↦ by
          by_cases hy : (κ ∘ₘ μ) {y} = 0
          · simp [hy]
          · exact mul_le_mul_right (isEpsPML_iff_ratio_le.1 h y hy) _
      _ = ENNReal.ofReal (Real.exp ε) := by
          rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
  obtain ⟨x, hx⟩ := μ.exists_measure_singleton_ne_zero
  rw [maxLeakage, Real.log_le_iff_le_exp (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx])]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos ε).le hS

/-- **Proposition 6** of Saeidian–Cervia–Oechtering–Skoglund (LDP part): if `κ` satisfies
`ε`-LDP on the support of `P_X` (Definition 14: `P_{Y|X}(y | x) ≤ e^ε P_{Y|X}(y | x')` for all
`x, x' ∈ supp P_X`), then it satisfies `ε'`-PML for every
`ε' ≥ -log (p_min + e^{-ε} (1 - p_min))`, where `p_min = min_{x ∈ supp P_X} P_X(x)` is attained
at `x₀`. -/
theorem isEpsPML_of_ldp (hε : 0 ≤ ε) {ε' : ℝ} {x₀ : α} (hx₀ : μ {x₀} ≠ 0)
    (hmin : ∀ x, μ {x} ≠ 0 → μ {x₀} ≤ μ {x})
    (hldp : ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → ∀ y,
      κ x {y} ≤ ENNReal.ofReal (Real.exp ε) * κ x' {y})
    (hε' : -Real.log ((μ {x₀}).toReal + Real.exp (-ε) * (1 - (μ {x₀}).toReal)) ≤ ε') :
    IsEpsPML μ κ ε' := by
  classical
  have := Fintype.ofFinite α
  rw [isEpsPML_iff_forall_le]
  intro x hx y
  -- Work with the real numbers `a x' = P_{Y|X}(y | x')` and `m x' = P_X(x')`.
  set m : α → ℝ := fun x' ↦ (μ {x'}).toReal
  set a : α → ℝ := fun x' ↦ (κ x' {y}).toReal
  set p := m x₀
  set c := p + Real.exp (-ε) * (1 - p)
  have hm_sum : ∑ x', m x' = 1 := by
    simp only [m]
    rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _, sum_measure_singleton,
      Finset.coe_univ, measure_univ, ENNReal.toReal_one]
  have hm_le_one (x' : α) : m x' ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := {x'}))
  have hp : 0 < p := ENNReal.toReal_pos hx₀ (measure_ne_top _ _)
  have hp_le : p ≤ m x := ENNReal.toReal_mono (measure_ne_top _ _) (hmin x hx)
  have he : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- `e^{-ε} P_{Y|X}(y | x) ≤ P_{Y|X}(y | x')` on the support.
  have h_ldp (x' : α) : Real.exp (-ε) * a x * m x' ≤ a x' * m x' := by
    by_cases hx' : μ {x'} = 0
    · simp [m, hx']
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (hldp x x' hx hx' y)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos ε).le] at h
    calc Real.exp (-ε) * a x ≤ Real.exp (-ε) * (Real.exp ε * a x') := by gcongr
      _ = a x' := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  -- `P_Y(y) ≥ P_{Y|X}(y | x) (P_X(x) + e^{-ε} (1 - P_X(x)))`.
  have h_PY : ((κ ∘ₘ μ) {y}).toReal = ∑ x', a x' * m x' := by
    rw [comp_apply_singleton, ENNReal.toReal_sum fun _ _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    simp only [ENNReal.toReal_mul, a, m]
  have h_erase : ∑ x' ∈ Finset.univ.erase x, m x' = 1 - m x := by
    rw [← hm_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    ring
  have h_low : a x * (m x + Real.exp (-ε) * (1 - m x)) ≤ ∑ x', a x' * m x' := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    calc a x * (m x + Real.exp (-ε) * (1 - m x))
        = a x * m x + ∑ x' ∈ Finset.univ.erase x, Real.exp (-ε) * a x * m x' := by
          rw [← Finset.mul_sum, h_erase]
          ring
      _ ≤ a x * m x + ∑ x' ∈ Finset.univ.erase x, a x' * m x' :=
          add_le_add le_rfl (Finset.sum_le_sum fun x' _ ↦ h_ldp x')
  -- `p_min + e^{-ε} (1 - p_min) ≤ P_X(x) + e^{-ε} (1 - P_X(x))` and `e^{ε'} c ≥ 1`.
  have hc : 0 < c :=
    add_pos_of_pos_of_nonneg hp (mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (hm_le_one x₀)))
  have hc_le : c ≤ m x + Real.exp (-ε) * (1 - m x) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hp_le) (sub_nonneg.2 he)]
  have h_exp : 1 ≤ Real.exp ε' * c := by
    have h := Real.exp_le_exp.2 hε'
    rw [Real.exp_neg, Real.exp_log hc] at h
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ Real.exp ε' * c := by gcongr
  have ha : 0 ≤ a x := ENNReal.toReal_nonneg
  have h_real : a x ≤ Real.exp ε' * ((κ ∘ₘ μ) {y}).toReal := by
    rw [h_PY]
    calc a x ≤ a x * (Real.exp ε' * c) := le_mul_of_one_le_right ha h_exp
      _ ≤ a x * (Real.exp ε' * (m x + Real.exp (-ε) * (1 - m x))) := by gcongr
      _ = Real.exp ε' * (a x * (m x + Real.exp (-ε) * (1 - m x))) := by ring
      _ ≤ Real.exp ε' * ∑ x', a x' * m x' := by gcongr
  calc κ x {y} = ENNReal.ofReal (a x) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp ε' * ((κ ∘ₘ μ) {y}).toReal) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (Real.exp ε') * (κ ∘ₘ μ) {y} := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]

omit [Finite α] in
/-- **Proposition 6** of Saeidian–Cervia–Oechtering–Skoglund (LDI part): if `κ` satisfies
`ε`-local differential identifiability (Definition 16,
`P_{X|Y=y}(x) ≤ e^ε P_{X|Y=y}(x')` for all `x, x' ∈ supp P_X`, stated here in the equivalent form
`P_{XY}(x, y) ≤ e^ε P_{XY}(x', y)`), then it satisfies `ε̃`-PML for every
`ε̃ ≥ -log (p_min (1 + e^{-ε} (|supp P_X| - 1)))`, where `p_min = min_{x ∈ supp P_X} P_X(x)` is
attained at `x₀`. -/
theorem isEpsPML_of_ldi [Fintype α] [DecidablePred fun x : α ↦ μ {x} ≠ 0] {ε' : ℝ} {x₀ : α}
    (hx₀ : μ {x₀} ≠ 0) (hmin : ∀ x, μ {x} ≠ 0 → μ {x₀} ≤ μ {x})
    (hldi : ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → ∀ y,
      κ x {y} * μ {x} ≤ ENNReal.ofReal (Real.exp ε) * (κ x' {y} * μ {x'}))
    (hε' : -Real.log ((μ {x₀}).toReal * (1 + Real.exp (-ε) *
      (((Finset.univ.filter fun x : α ↦ μ {x} ≠ 0).card : ℝ) - 1))) ≤ ε') :
    IsEpsPML μ κ ε' := by
  classical
  rw [isEpsPML_iff_forall_le]
  intro x hx y
  set S := Finset.univ.filter fun x : α ↦ μ {x} ≠ 0
  set m : α → ℝ := fun x' ↦ (μ {x'}).toReal
  set a : α → ℝ := fun x' ↦ (κ x' {y}).toReal
  set d := 1 + Real.exp (-ε) * ((S.card : ℝ) - 1)
  set c := m x₀ * d
  have hxS : x ∈ S := by simp [S, hx]
  have hn : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hxS⟩
  have hp : 0 < m x₀ := ENNReal.toReal_pos hx₀ (measure_ne_top _ _)
  have hp_le : m x₀ ≤ m x := ENNReal.toReal_mono (measure_ne_top _ _) (hmin x hx)
  have hd : 0 < d := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hn
    have := Real.exp_pos (-ε)
    positivity
  -- `e^{-ε} P_{XY}(x, y) ≤ P_{XY}(x', y)` on the support.
  have h_ldi (x' : α) (hx' : μ {x'} ≠ 0) : Real.exp (-ε) * (a x * m x) ≤ a x' * m x' := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))) (hldi x x' hx hx' y)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos ε).le] at h
    calc Real.exp (-ε) * (a x * m x) ≤ Real.exp (-ε) * (Real.exp ε * (a x' * m x')) := by gcongr
      _ = a x' * m x' := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have h_PY : ((κ ∘ₘ μ) {y}).toReal = ∑ x', a x' * m x' := by
    rw [comp_apply_singleton, ENNReal.toReal_sum fun _ _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    simp only [ENNReal.toReal_mul, a, m]
  have h_low : a x * m x * d ≤ ∑ x', a x' * m x' :=
    calc a x * m x * d = a x * m x + ∑ x' ∈ S.erase x, Real.exp (-ε) * (a x * m x) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hxS, nsmul_eq_mul, Nat.cast_sub hn,
            Nat.cast_one]
          ring
      _ ≤ a x * m x + ∑ x' ∈ S.erase x, a x' * m x' :=
          add_le_add le_rfl (Finset.sum_le_sum fun x' hx' ↦
            h_ldi x' (Finset.mem_filter.1 (Finset.mem_of_mem_erase hx')).2)
      _ = ∑ x' ∈ S, a x' * m x' := Finset.add_sum_erase S (fun x' ↦ a x' * m x') hxS
      _ ≤ ∑ x', a x' * m x' := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hc : 0 < c := mul_pos hp hd
  have h_exp : 1 ≤ Real.exp ε' * c := by
    have h := Real.exp_le_exp.2 hε'
    rw [Real.exp_neg, Real.exp_log hc] at h
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ Real.exp ε' * c := by gcongr
  have ha : 0 ≤ a x := ENNReal.toReal_nonneg
  have h_real : a x ≤ Real.exp ε' * ((κ ∘ₘ μ) {y}).toReal := by
    rw [h_PY]
    calc a x ≤ a x * (Real.exp ε' * c) := le_mul_of_one_le_right ha h_exp
      _ ≤ a x * (Real.exp ε' * (m x * d)) := by
          gcongr
          exact mul_le_mul_of_nonneg_right hp_le hd.le
      _ = Real.exp ε' * (a x * m x * d) := by ring
      _ ≤ Real.exp ε' * ∑ x', a x' * m x' := by gcongr
  calc κ x {y} = ENNReal.ofReal (a x) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp ε' * ((κ ∘ₘ μ) {y}).toReal) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (Real.exp ε') * (κ ∘ₘ μ) {y} := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end Guarantees

section Closure

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [IsProbabilityMeasure μ] [IsMarkovKernel κ] {η : Kernel β γ}
  [IsMarkovKernel η] {ε : ℝ}

/-- **Proposition 1.1** of Saeidian–Cervia–Oechtering–Skoglund (closedness under
pre-processing): for a Markov chain `X - Y - Z`, if the channel `P_{Z|Y} = η` satisfies `ε`-PML
(for the prior `P_Y = κ ∘ₘ μ`), then so does `P_{Z|X} = η ∘ₖ κ` (for the prior `P_X = μ`). -/
theorem IsEpsPML.preprocess (h : IsEpsPML (κ ∘ₘ μ) η ε) : IsEpsPML μ (η ∘ₖ κ) ε :=
  fun z hz ↦ (pointwiseMaxLeakage_comp_le_comp η hz).trans (h z (by rwa [Measure.comp_assoc]))

/-- **Proposition 1.2** of Saeidian–Cervia–Oechtering–Skoglund (closedness under
post-processing): for a Markov chain `X - Y - Z`, if `P_{Y|X} = κ` satisfies `ε`-PML, then so
does `P_{Z|X} = η ∘ₖ κ`. -/
theorem IsEpsPML.postprocess (h : IsEpsPML μ κ ε) (η : Kernel β γ) [IsMarkovKernel η] :
    IsEpsPML μ (η ∘ₖ κ) ε := fun z hz ↦ by
  obtain ⟨y, hy, hle⟩ := exists_pointwiseMaxLeakage_comp_le η hz
  exact hle.trans (h y hy)

end Closure

namespace PointwiseLeakage

/-- On a finite alphabet, if `P {y} ≤ c y * Q {y}` for every `y`, then
`KL(P, Q) ≤ ∫ log c dP`. -/
lemma klDiv_le_ofReal_integral_log [Finite γ] [MeasurableSingletonClass γ] {P Q : Measure γ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {c : γ → ℝ≥0∞} (hc : ∀ y, c y ≠ ∞)
    (h : ∀ y, P {y} ≤ c y * Q {y}) :
    klDiv P Q ≤ ENNReal.ofReal (∫ y, Real.log (c y).toReal ∂P) := by
  have hac : P ≪ Q := fun s hs ↦ by
    rw [measure_eq_zero_iff_ae_notMem, ae_iff_of_countable] at hs ⊢
    exact fun y hy ↦ hs y fun hQy ↦ hy (by simpa [hQy] using h y)
  have h_int : Integrable (llr P Q) P := .of_finite
  -- At every atom `y` of `P`, the density `dP/dQ` is positive and at most `c y`.
  have h_llr : ∀ᵐ y ∂P, llr P Q y ≤ Real.log (c y).toReal := by
    refine ae_iff_of_countable.2 fun y hy ↦ ?_
    have hy_eq : P {y} = P.rnDeriv Q y * Q {y} := by
      rw [← Measure.setLIntegral_rnDeriv hac, lintegral_singleton]
    have h_pos : P.rnDeriv Q y ≠ 0 := fun h0 ↦ hy (by simp [hy_eq, h0])
    have hQy : Q {y} ≠ 0 := fun h0 ↦ hy (by simp [hy_eq, h0])
    have h_le : P.rnDeriv Q y ≤ c y :=
      (ENNReal.mul_le_mul_iff_left hQy (measure_ne_top Q _)).1 (hy_eq ▸ h y)
    exact Real.log_le_log (ENNReal.toReal_pos h_pos (ne_top_of_le_ne_top (hc y) h_le))
      (ENNReal.toReal_mono (hc y) h_le)
  calc klDiv P Q = ENNReal.ofReal (∫ y, llr P Q y ∂P) := by
        simp [klDiv_of_ac_of_integrable hac h_int]
    _ ≤ ENNReal.ofReal (∫ y, Real.log (c y).toReal ∂P) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae h_int .of_finite h_llr)

end PointwiseLeakage

section MutualInformation

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] {ε : ℝ}

open PointwiseLeakage

/-- `ℓ(X → Y) ≥ 0` almost surely, under every input atom. -/
lemma ae_nonneg_pointwiseMaxLeakage {x : α} (hx : μ {x} ≠ 0) :
    0 ≤ᵐ[κ x] fun y ↦ pointwiseMaxLeakage μ κ y :=
  ae_iff_of_countable.2 fun y hy ↦
    pointwiseMaxLeakage_nonneg (Measure.comp_apply_ne_zero (measurableSet_singleton y) hx hy)

/-- **Proposition 7** of Saeidian–Cervia–Oechtering–Skoglund (inequality part): mutual
information is at most the expected pointwise maximal leakage, `I(X; Y) ≤ E_{Y ∼ P_Y}[ℓ(X → Y)]`,
in `ℝ≥0∞`. -/
theorem mutualInfo_compProd_le_ofReal_integral_pointwiseMaxLeakage :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal (∫ y, pointwiseMaxLeakage μ κ y ∂(κ ∘ₘ μ)) := by
  have h_meas : Measurable fun y ↦ ENNReal.ofReal (pointwiseMaxLeakage μ κ y) :=
    measurable_of_finite _
  rw [mutualInfo_compProd_eq_condKL, condKL_eq_lintegral,
    ofReal_integral_eq_lintegral_ofReal .of_finite (ae_iff_of_countable.2 fun y hy ↦
      pointwiseMaxLeakage_nonneg hy),
    Measure.lintegral_bind κ.aemeasurable h_meas.aemeasurable]
  refine lintegral_mono_ae (ae_iff_of_countable.2 fun x hx ↦ ?_)
  rw [Kernel.const_apply, ← ofReal_integral_eq_lintegral_ofReal .of_finite
    (ae_nonneg_pointwiseMaxLeakage hx)]
  exact klDiv_le_ofReal_integral_log pointwiseMaxLeakageRatio_ne_top
    fun y ↦ apply_le_pointwiseMaxLeakageRatio_mul hx y

/-- **Proposition 7** of Saeidian–Cervia–Oechtering–Skoglund (inequality part):
`I(X; Y) ≤ E_{Y ∼ P_Y}[ℓ(X → Y)]`. -/
theorem toReal_mutualInfo_compProd_le_integral_pointwiseMaxLeakage :
    (mutualInfo (μ ⊗ₘ κ)).toReal ≤ ∫ y, pointwiseMaxLeakage μ κ y ∂(κ ∘ₘ μ) :=
  ENNReal.toReal_le_of_le_ofReal (integral_nonneg_of_ae (ae_iff_of_countable.2 fun _ hy ↦
    pointwiseMaxLeakage_nonneg hy)) mutualInfo_compProd_le_ofReal_integral_pointwiseMaxLeakage

/-- **Proposition 7.1** of Saeidian–Cervia–Oechtering–Skoglund: if `κ` satisfies `ε`-PML, then
`I(X; Y) ≤ ε`. -/
theorem IsEpsPML.mutualInfo_le (h : IsEpsPML μ κ ε) :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal ε := by
  refine mutualInfo_compProd_le_ofReal_integral_pointwiseMaxLeakage.trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc ∫ y, pointwiseMaxLeakage μ κ y ∂(κ ∘ₘ μ) ≤ ∫ _, ε ∂(κ ∘ₘ μ) :=
        integral_mono_ae .of_finite (integrable_const _) (ae_iff_of_countable.2 fun y hy ↦ h y hy)
    _ = ε := by simp

end MutualInformation

section Posterior

variable [Fintype α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ]

/-- **Theorem 1**, equation (5), of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form:
`exp ℓ(X → y) = max_{x ∈ supp P_X} P_{X|Y=y}(x) / P_X(x)` for every outcome `y` with
`P_Y(y) > 0`. With Remark 1, this identifies `pointwiseMaxLeakage` with the closed form of the
paper. The Lean equality holds for every `y`, as an identity between the totalized ratios in
`ℝ≥0∞`: for `P_Y(y) = 0` both sides are `0` (no `exp ℓ` reading is intended there, since
`pointwiseMaxLeakage` is then `Real.log 0 = 0`). -/
theorem pointwiseMaxLeakageRatio_eq_iSup_posterior (y : β) :
    pointwiseMaxLeakageRatio μ κ y = ⨆ (x) (_ : μ {x} ≠ 0), posterior μ κ y {x} / μ {x} := by
  refine iSup_congr fun x ↦ iSup_congr fun hx ↦ ?_
  rw [posterior_apply_singleton, ← mul_assoc, ENNReal.mul_div_cancel_right hx
    (measure_ne_top _ _), ENNReal.div_eq_inv_mul]

end Posterior

section Composition

variable [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
  (η : Kernel (α × β) γ) [IsMarkovKernel η]

namespace PointwiseLeakage

omit [Fintype α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma compProd_apply_singleton (x : α) (y : β) (z : γ) :
    (κ ⊗ₖ η) x {(y, z)} = κ x {y} * η (x, y) {z} := by
  rw [← Set.singleton_prod_singleton, Kernel.compProd_apply_prod (measurableSet_singleton y)
    (measurableSet_singleton z), lintegral_singleton, mul_comm]

/-- `P_{YZ}(y, z) = P_Y(y) P_{Z|Y=y}(z)`, where `P_{Z|Y=y}` is the law of `Z` given `Y = y`:
`X ∼ P_{X|Y=y}` and `Z` is drawn from `(X, y)` through `η`. -/
lemma compProd_comp_apply_singleton {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) (z : γ) :
    ((κ ⊗ₖ η) ∘ₘ μ) {(y, z)} = (κ ∘ₘ μ) {y} * (η.sectL y ∘ₘ posterior μ κ y) {z} := by
  have hPP : (κ ∘ₘ μ) {y} * ((κ ∘ₘ μ) {y})⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hy (measure_ne_top _ _)
  rw [comp_apply_singleton μ (κ ⊗ₖ η) (y, z), comp_apply_singleton (posterior μ κ y) (η.sectL y) z,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [compProd_apply_singleton, posterior_apply_singleton, Kernel.sectL_apply]
  calc κ x {y} * η (x, y) {z} * μ {x}
      = κ x {y} * η (x, y) {z} * μ {x} * ((κ ∘ₘ μ) {y} * ((κ ∘ₘ μ) {y})⁻¹) := by
        rw [hPP, mul_one]
    _ = _ := by ring

lemma ne_zero_of_compProd_comp_apply_ne_zero {y : β} {z : γ}
    (hyz : ((κ ⊗ₖ η) ∘ₘ μ) {(y, z)} ≠ 0) :
    (κ ∘ₘ μ) {y} ≠ 0 ∧ (η.sectL y ∘ₘ posterior μ κ y) {z} ≠ 0 := by
  have hy : (κ ∘ₘ μ) {y} ≠ 0 := fun h ↦ hyz <| by
    rw [comp_apply_singleton]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : μ {x} = 0
    · simp [hx]
    · simp [compProd_apply_singleton, apply_eq_zero_of_comp_eq_zero hx h]
  exact ⟨hy, right_ne_zero_of_mul (compProd_comp_apply_singleton η hy z ▸ hyz)⟩

end PointwiseLeakage

open PointwiseLeakage

/-- **Lemma 1.6 (composition)** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form: for
an outcome `y` of `Y ∼ κ` with `P_Y(y) > 0` and an outcome `z` of `Z`, drawn from `(X, Y)` through
`η`, `exp ℓ(X → (y, z)) ≤ exp ℓ(X → y) · exp ℓ(X → z | y)`. The conditional pointwise maximal
leakage `ℓ(X → z | y)` (Definition 3 and the closed form after it) is the pointwise maximal
leakage of the channel `P_{Z|X,Y=y} = η.sectL y` for the prior `P_{X|Y=y}`. -/
theorem pointwiseMaxLeakageRatio_compProd_le {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) (z : γ) :
    pointwiseMaxLeakageRatio μ (κ ⊗ₖ η) (y, z) ≤ pointwiseMaxLeakageRatio μ κ y *
      pointwiseMaxLeakageRatio (posterior μ κ y) (η.sectL y) z := by
  have := isProbabilityMeasure_posterior hy
  refine iSup₂_le fun x hx ↦ ENNReal.div_le_of_le_mul ?_
  rw [compProd_apply_singleton, compProd_comp_apply_singleton η hy, mul_mul_mul_comm]
  by_cases hκ : κ x {y} = 0
  · simp [hκ]
  have hpx : posterior μ κ y {x} ≠ 0 := by
    rw [posterior_apply_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) (mul_ne_zero hκ hx)
  exact mul_le_mul' (apply_le_pointwiseMaxLeakageRatio_mul hx y)
    (apply_le_pointwiseMaxLeakageRatio_mul (κ := η.sectL y) hpx z)

/-- **Lemma 1.6 (composition)** of Saeidian–Cervia–Oechtering–Skoglund: for every `(y, z)` with
`P_{YZ}(y, z) > 0`, `ℓ(X → (y, z)) ≤ ℓ(X → y) + ℓ(X → z | y)`, where `Y ∼ κ`, `Z` is drawn from
`(X, Y)` through `η` and `ℓ(X → z | y)` is the pointwise maximal leakage of `P_{Z|X,Y=y}` for the
prior `P_{X|Y=y}` (the paper states it with the roles of `Y` and `Z` exchanged). -/
theorem pointwiseMaxLeakage_compProd_le {y : β} {z : γ}
    (hyz : ((κ ⊗ₖ η) ∘ₘ μ) {(y, z)} ≠ 0) :
    pointwiseMaxLeakage μ (κ ⊗ₖ η) (y, z) ≤
      pointwiseMaxLeakage μ κ y + pointwiseMaxLeakage (posterior μ κ y) (η.sectL y) z := by
  obtain ⟨hy, hz⟩ := ne_zero_of_compProd_comp_apply_ne_zero η hyz
  have := isProbabilityMeasure_posterior hy
  have h₁ := one_le_toReal_pointwiseMaxLeakageRatio hy
  have h₂ := one_le_toReal_pointwiseMaxLeakageRatio (κ := η.sectL y) hz
  rw [pointwiseMaxLeakage, pointwiseMaxLeakage, pointwiseMaxLeakage, ← Real.log_mul
    (by positivity) (by positivity), ← ENNReal.toReal_mul]
  refine Real.log_le_log (by linarith [one_le_toReal_pointwiseMaxLeakageRatio hyz]) ?_
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (pointwiseMaxLeakageRatio_ne_top _)
    (pointwiseMaxLeakageRatio_ne_top _)) (pointwiseMaxLeakageRatio_compProd_le η hy z)

/-- **Theorem 4.1** of Saeidian–Cervia–Oechtering–Skoglund (adaptive composition): if `P_{Y|X} = κ`
satisfies `ε₁`-PML and, for every `y ∈ supp P_Y`, the channel `P_{Z|X,Y=y} = η.sectL y`
satisfies `ε₂`-PML for the prior `P_{X|Y=y}`, then `P_{YZ|X} = κ ⊗ₖ η` satisfies
`(ε₁ + ε₂)`-PML. -/
theorem IsEpsPML.compProd {ε₁ ε₂ : ℝ} (h₁ : IsEpsPML μ κ ε₁)
    (h₂ : ∀ y, (κ ∘ₘ μ) {y} ≠ 0 → IsEpsPML (posterior μ κ y) (η.sectL y) ε₂) :
    IsEpsPML μ (κ ⊗ₖ η) (ε₁ + ε₂) := by
  rintro ⟨y, z⟩ hyz
  obtain ⟨hy, hz⟩ := ne_zero_of_compProd_comp_apply_ne_zero η hyz
  exact (pointwiseMaxLeakage_compProd_le η hyz).trans (add_le_add (h₁ y hy) (h₂ y hy z hz))

end Composition

section TailBound

/-- **`(ε, δ)`-PML** (the tail-bound guarantee, Definition 5 of
Saeidian–Cervia–Oechtering–Skoglund): for the prior `μ`, the mechanism `κ` satisfies
`(ε, δ)`-PML if `P_{Y}[ℓ(X → Y) ≤ ε] ≥ 1 - δ`. It is meant for countable (in the paper, finite)
output alphabets, where `pointwiseMaxLeakage` is meaningful on the atoms of `P_Y`.

The paper's parameter domain is `ε ≥ 0` and `δ ∈ [0, 1]`. The predicate accepts arbitrary real
`ε` and `δ` and is then an unrestricted extension: for `δ ≥ 1` it holds vacuously, for every
`ε` (e.g. `ε = -1, δ = 1`). Results that need the paper's range assume it
explicitly (e.g. `0 ≤ ε` in `IsEpsDeltaPML.mutualInfo_le`). -/
def IsEpsDeltaPML (μ : Measure α) (κ : Kernel α β) (ε δ : ℝ) : Prop :=
  1 - δ ≤ (κ ∘ₘ μ).real {y | pointwiseMaxLeakage μ κ y ≤ ε}

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ] {ε δ : ℝ}

open PointwiseLeakage

omit [Finite α] [MeasurableSingletonClass α] [Finite β] in
/-- `ε`-PML and `(ε, 0)`-PML are equivalent (after Definition 5 of
Saeidian–Cervia–Oechtering–Skoglund). -/
theorem isEpsDeltaPML_zero_iff [Countable β] : IsEpsDeltaPML μ κ ε 0 ↔ IsEpsPML μ κ ε := by
  set G := {y | pointwiseMaxLeakage μ κ y ≤ ε}
  have hG : MeasurableSet G := (Set.to_countable _).measurableSet
  have h_iff : (∀ᵐ y ∂(κ ∘ₘ μ), y ∈ G) ↔ IsEpsPML μ κ ε := ae_iff_of_countable
  rw [← h_iff, ae_iff, ← measureReal_eq_zero_iff, IsEpsDeltaPML, sub_zero]
  have h_compl := probReal_compl_eq_one_sub (μ := κ ∘ₘ μ) hG
  have h_le : (κ ∘ₘ μ).real G ≤ 1 := measureReal_le_one
  change _ ↔ (κ ∘ₘ μ).real Gᶜ = 0
  constructor <;> intro h <;> linarith

/-- **Proposition 1.3** of Saeidian–Cervia–Oechtering–Skoglund (closedness of the tail-bound
guarantee under pre-processing): for a Markov chain `X - Y - Z`, if the channel `P_{Z|Y} = η`
satisfies `(ε, δ)`-PML (for the prior `P_Y = κ ∘ₘ μ`), then so does `P_{Z|X} = η ∘ₖ κ`. -/
theorem IsEpsDeltaPML.preprocess [MeasurableSingletonClass γ] {η : Kernel β γ}
    [IsMarkovKernel η] [Finite γ] (h : IsEpsDeltaPML (κ ∘ₘ μ) η ε δ) :
    IsEpsDeltaPML μ (η ∘ₖ κ) ε δ := by
  refine h.trans ?_
  rw [Measure.comp_assoc, measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  refine ae_iff_of_countable.2 fun z hz hle ↦ ?_
  exact (pointwiseMaxLeakage_comp_le_comp η hz).trans hle

/-- **Proposition 7.2** of Saeidian–Cervia–Oechtering–Skoglund: if `κ` satisfies `(ε, δ)`-PML
with `ε ≥ 0`, then `I(X; Y) ≤ ε + δ ε_max`, where `ε_max = -log min_{x ∈ supp P_X} P_X(x)` (the
minimum is attained at the atom `x₀`). -/
theorem IsEpsDeltaPML.mutualInfo_le (h : IsEpsDeltaPML μ κ ε δ) (hε : 0 ≤ ε) {x₀ : α}
    (hx₀ : μ {x₀} ≠ 0) (hmin : ∀ x, μ {x} ≠ 0 → μ {x₀} ≤ μ {x}) :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal (ε + δ * -Real.log (μ {x₀}).toReal) := by
  set εmax := -Real.log (μ {x₀}).toReal
  set G := {y | pointwiseMaxLeakage μ κ y ≤ ε}
  have hG : MeasurableSet G := (Set.toFinite _).measurableSet
  have hεmax : 0 ≤ εmax := neg_nonneg.2 (Real.log_nonpos ENNReal.toReal_nonneg
    (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := {x₀}))))
  refine mutualInfo_compProd_le_ofReal_integral_pointwiseMaxLeakage.trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc ∫ y, pointwiseMaxLeakage μ κ y ∂(κ ∘ₘ μ)
      ≤ ∫ y, (G.indicator (fun _ ↦ ε) y + Gᶜ.indicator (fun _ ↦ εmax) y) ∂(κ ∘ₘ μ) := by
        refine integral_mono_ae .of_finite .of_finite (ae_iff_of_countable.2 fun y hy ↦ ?_)
        dsimp only
        by_cases hyG : y ∈ G
        · rw [Set.indicator_of_mem hyG, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hyG),
            add_zero]
          exact hyG
        · rw [Set.indicator_of_notMem hyG, Set.indicator_of_mem (Set.mem_compl hyG), zero_add]
          exact pointwiseMaxLeakage_le_neg_log hx₀ hmin hy
    _ = (κ ∘ₘ μ).real G * ε + (κ ∘ₘ μ).real Gᶜ * εmax := by
        rw [integral_add .of_finite .of_finite, integral_indicator_const _ hG,
          integral_indicator_const _ hG.compl, smul_eq_mul, smul_eq_mul]
    _ ≤ 1 * ε + δ * εmax := by
        gcongr
        · exact measureReal_le_one
        · rw [probReal_compl_eq_one_sub hG]
          unfold IsEpsDeltaPML at h
          linarith
    _ = ε + δ * εmax := by rw [one_mul]

end TailBound

end InformationTheory
