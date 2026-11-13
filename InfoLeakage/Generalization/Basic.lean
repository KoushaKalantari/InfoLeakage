/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Differential privacy implies generalization in expectation

This file formalizes, for finite data alphabets, the "differential privacy implies generalization
in expectation" results of

* R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, *Algorithmic stability for
  adaptive data analysis*, STOC 2016, [arXiv:1511.02513](https://arxiv.org/abs/1511.02513);
  result numbers follow arXiv v1;
* C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, *Preserving statistical
  validity in adaptive data analysis*, STOC 2015,
  [arXiv:1411.2664](https://arxiv.org/abs/1411.2664); result numbers follow arXiv v3.

A dataset is `S : ι → 𝒳`, a tuple of `n = |ι|` records from a finite alphabet `𝒳` with measurable
singletons, drawn i.i.d. from a distribution `P`: `S ∼ Pⁿ = Measure.pi (fun _ ↦ P)`. A mechanism is
a Markov kernel `M : Kernel (ι → 𝒳) Z` to an arbitrary measurable space `Z`, and `(ε, δ)`-
differential privacy (Definition 2.3 of Bassily et al., "max-KL stability"; Definition 5 of Dwork
et al.) is the library's `IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ`: neighbours differ
in exactly one record. A statistical query is `x ↦ Q z x ∈ [0, 1]`, where `z` is the output of
the mechanism and `Q z x` is measurable in `z`. Expectations over the dataset and the coins of the
mechanism are integrals against the joint law `Pⁿ ⊗ₘ M` of `(S, M(S))`. The papers' conditional
notation `E[q(x) | q = W(x)]` and `E[q(P) | q = W(x)]` reads, here,
`∫ q, empiricalMean (Q q.2) q.1 ∂(Pⁿ ⊗ₘ M)` and `∫ q, ∫ x, Q q.2 x ∂P ∂(Pⁿ ⊗ₘ M)`.

## Main definitions

* `Generalization.empiricalMean q S`: the empirical mean `E_S[q] = (1/n) ∑ᵢ q(Sᵢ)`.

## Main statements

* `IsEpsDeltaDP.integral_le_exp_mul_integral_add`, `IsEpsDeltaDP.integral_sub_integral_le`:
  replace-one stability, `E[g(M(S))] ≤ e^ε E[g(M(S'))] + δ` for neighbours `S, S'` and
  `g : Z → [0, 1]`.
* `IsEpsDeltaDP.integral_sum_le`, `IsEpsDeltaDP.integral_sum_integral_le`: the de-correlated
  expectation lemma in a general form, `E[∑ᵢ gᵢ(M(S), Sᵢ)] ≤ e^ε E[∑ᵢ P[gᵢ(M(S), ·)]] + n δ`
  and the reverse inequality, for `gᵢ : Z × 𝒳 → [0, 1]`.
* `IsEpsDeltaDP.integral_empiricalMean_le`, `IsEpsDeltaDP.integral_le_integral_empiricalMean`,
  `IsEpsDeltaDP.abs_integral_empiricalMean_sub_integral_le`: differential privacy implies
  generalization in expectation, `|E[E_S[Q_{M(S)}]] - E[P[Q_{M(S)}]]| ≤ e^ε - 1 + δ`.
* `IsEpsDeltaDP.integral_empiricalMean_sample_le`,
  `IsEpsDeltaDP.integral_le_integral_empiricalMean_sample`,
  `IsEpsDeltaDP.abs_integral_sub_integral_empiricalMean_sample_le`: the multi-sample version, for
  a mechanism that sees `T` samples and selects one of them.

## Paper → Lean

Bassily et al. (arXiv v1):
* Definition 2.3 → `IsEpsDeltaDP` with the Hamming neighbouring relation.
* Lemma 3.1 (finite-alphabet special case) →
  `IsEpsDeltaDP.abs_integral_empiricalMean_sub_integral_le`; the two inequalities of its proof
  (finite-alphabet special case) → `IsEpsDeltaDP.integral_empiricalMean_le` and
  `IsEpsDeltaDP.integral_le_integral_empiricalMean`.
* Lemma 3.2 (finite-alphabet special case) →
  `IsEpsDeltaDP.abs_integral_sub_integral_empiricalMean_sample_le`, with the two inequalities of
  its proof (finite-alphabet special case) `IsEpsDeltaDP.integral_empiricalMean_sample_le` and
  `IsEpsDeltaDP.integral_le_integral_empiricalMean_sample`. The `T` samples
  `X = (x₁, …, x_T) ∈ (𝒳ⁿ)^T` are one dataset `κ × ι → 𝒳` with `T = |κ|` and `n = |ι|`, so
  that neighbours differ in exactly one of the `T n` records, and `W(X) = (q, t)` is a kernel to
  `Z × κ`.

Dwork et al. (arXiv v3):
* Definition 5 → `IsEpsDeltaDP` with the Hamming neighbouring relation.
* Lemma 6 → `IsEpsDeltaDP.integral_le_exp_mul_integral_add`; its inequality (1) →
  `IsEpsDeltaDP.integral_sub_integral_le`. The paper's `E[A(S)(x)]` is `∫ z, g z ∂M S` with
  `g = (· x)`; here `g` is any measurable `[0, 1]`-valued function on an arbitrary output space.
* Corollary 7 (finite-alphabet special case) →
  `IsEpsDeltaDP.abs_integral_empiricalMean_sub_integral_le`; one direction of its proof →
  `IsEpsDeltaDP.integral_empiricalMean_le`.

## Implementation notes

* The papers allow an arbitrary data domain `𝒳` and distribution `P`; every result here is the
  special case of a finite `𝒳` with measurable singletons.
* All results assume `0 ≤ ε` and `0 ≤ δ`, as the papers do implicitly; the replace-one argument
  compares `M(S)` with `M(S[i ↦ x'])`, which is `M(S)` itself, not a neighbour, when `Sᵢ = x'`.
  The empirical-mean statements assume `n ≥ 1` (`[Nonempty ι]`).
* The replace-one argument of both papers is carried out with finite sums over datasets:
  `Generalization.sum_sum_update_swap` says that `(S, x') ↦ (S[i ↦ x'], Sᵢ)` is an involution
  preserving the weight of `Pⁿ ⊗ P` ("the pairs `(xᵢ, x_{i→x'})` and `(x', x)` are identically
  distributed"). Differential privacy is applied to expectations through the layer-cake lemma
  `DP.lintegral_le_of_forall_measure_le`, in place of the paper's `∫₀¹ P[q(xᵢ) > z] dz`.

## Notes on the paper

* Lemma 3.1 of Bassily et al. (Section 3.1, p. 9 of arXiv v1) declares the algorithm as
  `W : (𝒳ⁿ)^T → Q`, but the lemma and its proof concern a single sample `x ← Pⁿ` (`T = 1`), so the
  domain should be `𝒳ⁿ`. Likewise, the second expectation in the statement is subscripted `X, W`,
  where it should be `x, W`, as in the first. The lemma is true as intended
  (`IsEpsDeltaDP.abs_integral_empiricalMean_sub_integral_le`).

## Not formalized

Lemma 3.3 (`Δ`-sensitive queries), Theorem 3.4 and the monitoring argument (interactive
mechanisms), and Sections 4–7 of Bassily et al.; the high-probability results of Dwork et al.
(Lemma 8, Theorems 9–11, Corollary 12; see `InfoLeakage.Generalization.HighProbability` for a
transfer theorem through max-information) and their Section 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real Function
open scoped ENNReal

namespace InformationTheory

variable {ι 𝒳 Z : Type*} {m𝒳 : MeasurableSpace 𝒳} {mZ : MeasurableSpace Z}

namespace Generalization

/-- A number in `[0, 1]` has absolute value at most `1`. -/
lemma abs_le_one_of_mem_Icc {a : ℝ} (h : a ∈ Icc (0 : ℝ) 1) : |a| ≤ 1 :=
  abs_le.2 ⟨by linarith [h.1], h.2⟩

/-- The expectation of a `[0, 1]`-valued function under a probability measure lies in `[0, 1]`. -/
lemma integral_mem_Icc {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    ∫ x, g x ∂μ ∈ Icc (0 : ℝ) 1 :=
  ⟨integral_nonneg fun x ↦ (hg x).1, (integral_mono_of_nonneg (ae_of_all _ fun x ↦ (hg x).1)
    (integrable_const 1) (ae_of_all _ fun x ↦ (hg x).2)).trans_eq (by simp)⟩

end Generalization

/-! ### Replace-one stability -/

section Stability

variable {𝒟 : Type*} {m𝒟 : MeasurableSpace 𝒟} {M : Kernel 𝒟 Z} {Adj : 𝒟 → 𝒟 → Prop} {ε δ : ℝ}
  {S S' : 𝒟}

/-- **Lemma 6 of Dwork et al. (STOC 2015)**: if `M` is `(ε, δ)`-differentially private and
`S, S'` are neighbours, then `E[g(M(S))] ≤ e^ε E[g(M(S'))] + δ` for every measurable
`g : Z → [0, 1]`. (The paper states it for an output `A(S)` that is a function `X → [0, 1]`
evaluated at a fixed point `x`, i.e. `g = (· x)`; the output space here is arbitrary.) -/
theorem IsEpsDeltaDP.integral_le_exp_mul_integral_add [IsFiniteKernel M]
    (hM : IsEpsDeltaDP M Adj ε δ) (hS : Adj S S') {g : Z → ℝ} (hg : Measurable g)
    (hg₁ : ∀ z, g z ∈ Icc (0 : ℝ) 1) :
    ∫ z, g z ∂M S ≤ exp ε * ∫ z, g z ∂M S' + δ := by
  have hδ := hM.nonneg hS
  have h := DP.lintegral_le_of_forall_measure_le (fun E _ ↦ hM.measure_le hS E)
    (g := fun z ↦ ENNReal.ofReal (g z)) hg.ennreal_ofReal
    fun z ↦ ENNReal.ofReal_le_one.2 (hg₁ z).2
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ (hg₁ z).1)
      hg.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ (hg₁ z).1) hg.aestronglyMeasurable]
  have hfin : ∫⁻ z, ENNReal.ofReal (g z) ∂M S' ≠ ∞ :=
    (lintegral_mono fun z ↦ ENNReal.ofReal_le_one.2 (hg₁ z).2).trans_lt
      (by simp [measure_lt_top]) |>.ne
  refine (ENNReal.toReal_mono (by finiteness) h).trans_eq ?_
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (exp_pos ε).le, ENNReal.toReal_ofReal hδ]

/-- **Lemma 6 of Dwork et al. (STOC 2015)**, inequality (1): an `(ε, δ)`-differentially private
algorithm is replace-one stable with rate `e^ε - 1 + δ`:
`E[g(M(S))] - E[g(M(S'))] ≤ e^ε - 1 + δ` for neighbours `S, S'` and measurable `g : Z → [0, 1]`. -/
theorem IsEpsDeltaDP.integral_sub_integral_le [IsMarkovKernel M] (hM : IsEpsDeltaDP M Adj ε δ)
    (hS : Adj S S') (hε : 0 ≤ ε) {g : Z → ℝ} (hg : Measurable g)
    (hg₁ : ∀ z, g z ∈ Icc (0 : ℝ) 1) :
    ∫ z, g z ∂M S - ∫ z, g z ∂M S' ≤ exp ε - 1 + δ := by
  have h := hM.integral_le_exp_mul_integral_add hS hg hg₁
  have h₁ := Generalization.integral_mem_Icc (μ := M S') hg₁
  nlinarith [one_le_exp hε, h₁.1, h₁.2]

end Stability

namespace Generalization

/-- Swapping the `i`-th record of a dataset `S` with a fresh sample `x` preserves the product
weight `(∏ⱼ p(Sⱼ)) p(x)`: summing `G (S[i ↦ x], Sᵢ)` against it is the same as summing `G (S, x)`.
This is the exchangeability step of the replace-one argument. -/
lemma sum_sum_update_swap [Fintype ι] [DecidableEq ι] [Fintype 𝒳] (p : 𝒳 → ℝ)
    (G : (ι → 𝒳) → 𝒳 → ℝ) (i : ι) :
    ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * G (update S i x) (S i) =
      ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * G S x := by
  set e : (ι → 𝒳) × 𝒳 → (ι → 𝒳) × 𝒳 := fun q ↦ (update q.1 i q.2, q.1 i) with he
  have hinv : Involutive e := fun q ↦ by simp [he]
  have hw (q : (ι → 𝒳) × 𝒳) :
      (∏ j, p ((e q).1 j)) * p (e q).2 = (∏ j, p (q.1 j)) * p q.2 := by
    have h1 : ∏ j, p (update q.1 i q.2 j) = p q.2 * ∏ j ∈ Finset.univ \ {i}, p (q.1 j) := by
      simp_rw [apply_update (fun _ ↦ p)]
      exact Finset.prod_update_of_mem (Finset.mem_univ i) _ _
    have h2 : ∏ j, p (q.1 j) = p (q.1 i) * ∏ j ∈ Finset.univ \ {i}, p (q.1 j) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ {i}), Finset.prod_singleton, mul_comm]
    simp only [he, h1, h2]
    ring
  simp_rw [← Fintype.sum_prod_type']
  calc ∑ q : (ι → 𝒳) × 𝒳, (∏ j, p (q.1 j)) * p q.2 * G (e q).1 (e q).2
      = ∑ q : (ι → 𝒳) × 𝒳, (∏ j, p ((e q).1 j)) * p (e q).2 * G (e q).1 (e q).2 := by
        simp_rw [hw]
    _ = ∑ q : (ι → 𝒳) × 𝒳, (∏ j, p (q.1 j)) * p q.2 * G q.1 q.2 :=
        Equiv.sum_comp (hinv.toPerm e) fun q ↦ (∏ j, p (q.1 j)) * p q.2 * G q.1 q.2

/-- The algebraic core of the replace-one argument (Lemma 3.1 of Bassily et al., Corollary 7 of
Dwork et al.). Let `p` be a probability vector on `𝒳` and let `F S y` (the expected value of the
query at the point `y` when the mechanism runs on `S`) satisfy `F S y ≤ c F (S[i ↦ x]) y + d`.
Then the expected value of the query at the `i`-th record, `∑_S pⁿ(S) F S (Sᵢ)`, is at most `c`
times its expected population value `∑_S pⁿ(S) ∑_x p(x) F S x`, plus `d`. -/
lemma sum_le_mul_sum_add [Fintype ι] [DecidableEq ι] [Fintype 𝒳] {p : 𝒳 → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1) {F : (ι → 𝒳) → 𝒳 → ℝ} {c d : ℝ} (i : ι)
    (hF : ∀ S x y, F S y ≤ c * F (update S i x) y + d) :
    ∑ S : ι → 𝒳, (∏ j, p (S j)) * F S (S i) ≤
      c * ∑ S : ι → 𝒳, (∏ j, p (S j)) * ∑ x, p x * F S x + d := by
  have hw : ∑ S : ι → 𝒳, ∏ j, p (S j) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : ι) x ↦ p x), hp₁, Finset.prod_const_one]
  calc ∑ S : ι → 𝒳, (∏ j, p (S j)) * F S (S i)
      = ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * F S (S i) := by
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, hp₁, mul_one]
    _ ≤ ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * (c * F (update S i x) (S i) + d) := by
        gcongr with S _ x
        · exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ hp _) (hp x)
        · exact hF S x (S i)
    _ = c * ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * F (update S i x) (S i) +
          d * ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x := by
        simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
        ring
    _ = c * ∑ S : ι → 𝒳, (∏ j, p (S j)) * ∑ x, p x * F S x + d := by
        have h1 : ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x = 1 := by
          simp_rw [← Finset.mul_sum, hp₁, mul_one, hw]
        rw [sum_sum_update_swap p F i, h1, mul_one]
        simp_rw [Finset.mul_sum, mul_assoc]

/-- The reverse inequality: if `F (S[i ↦ x]) y ≤ c F S y + d`, then the expected population value
of the query is at most `c` times its expected value at the `i`-th record, plus `d`. -/
lemma sum_le_mul_sum_add' [Fintype ι] [DecidableEq ι] [Fintype 𝒳] {p : 𝒳 → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1) {F : (ι → 𝒳) → 𝒳 → ℝ} {c d : ℝ} (i : ι)
    (hF : ∀ S x y, F (update S i x) y ≤ c * F S y + d) :
    ∑ S : ι → 𝒳, (∏ j, p (S j)) * ∑ x, p x * F S x ≤
      c * ∑ S : ι → 𝒳, (∏ j, p (S j)) * F S (S i) + d := by
  have hw : ∑ S : ι → 𝒳, ∏ j, p (S j) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : ι) x ↦ p x), hp₁, Finset.prod_const_one]
  calc ∑ S : ι → 𝒳, (∏ j, p (S j)) * ∑ x, p x * F S x
      = ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * F (update S i x) (S i) := by
        rw [sum_sum_update_swap p F i]
        simp_rw [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ S : ι → 𝒳, ∑ x, (∏ j, p (S j)) * p x * (c * F S (S i) + d) := by
        gcongr with S _ x
        · exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ hp _) (hp x)
        · exact hF S x (S i)
    _ = c * ∑ S : ι → 𝒳, (∏ j, p (S j)) * F S (S i) + d := by
        have hsum (S : ι → 𝒳) (K : ℝ) : ∑ x, (∏ j, p (S j)) * p x * K = (∏ j, p (S j)) * K := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hp₁, mul_one]
        simp_rw [hsum, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul,
          Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun S _ ↦ by ring

end Generalization

/-! ### The de-correlated expectation lemma -/

section Expectation

variable [Fintype ι] {P : Measure 𝒳} [IsProbabilityMeasure P] {M : Kernel (ι → 𝒳) Z}
  [IsMarkovKernel M] {ε δ : ℝ}

/-- The **empirical mean** `E_S[q] = (1/n) ∑ᵢ q(Sᵢ)` of `q : 𝒳 → ℝ` on a dataset `S : ι → 𝒳` of
`n = |ι|` records (`E_S[ψ]` in Dwork et al., `q(x)` for a statistical query in Bassily et al.). -/
noncomputable def Generalization.empiricalMean (q : 𝒳 → ℝ) (S : ι → 𝒳) : ℝ :=
  (∑ i, q (S i)) / Fintype.card ι

namespace Generalization

/-- The empirical mean of a `[0, 1]`-valued function lies in `[0, 1]`. -/
lemma empiricalMean_mem_Icc [Nonempty ι] {q : 𝒳 → ℝ} (hq : ∀ x, q x ∈ Icc (0 : ℝ) 1)
    (S : ι → 𝒳) : empiricalMean q S ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ ↦ (hq _).1) hn.le, (div_le_one hn).2 ?_⟩
  calc ∑ i, q (S i) ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (hq _).2
    _ = Fintype.card ι := by simp

/-- `E_S[1 - ψ] = 1 - E_S[ψ]`. -/
lemma empiricalMean_one_sub [Nonempty ι] (ψ : 𝒳 → ℝ) (S : ι → 𝒳) :
    empiricalMean (fun x ↦ 1 - ψ x) S = 1 - empiricalMean ψ S := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := (Nat.cast_pos.2 Fintype.card_pos).ne'
  simp only [empiricalMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  field_simp

/-- Replacing the `i`-th record of `S` by a different value gives a neighbouring dataset. -/
lemma hammingDist_update_of_ne [DecidableEq ι] [DecidableEq 𝒳] {S : ι → 𝒳} {i : ι} {x : 𝒳}
    (h : S i ≠ x) :
    hammingDist S (update S i x) = 1 := by
  rw [hammingDist, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext k
  by_cases hk : k = i
  · simp [hk, h]
  · simp [hk, update_apply]

/-- Replace-one stability of a differentially private mechanism, in both directions: replacing
one record changes `E[g(M(S))]` by at most the factor `e^ε` and the additive `δ`. -/
lemma integral_le_update [DecidableEq ι] [DecidableEq 𝒳]
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) {g : Z → ℝ} (hg : Measurable g) (hg₁ : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (S : ι → 𝒳) (i : ι) (x : 𝒳) :
    ∫ z, g z ∂M S ≤ exp ε * ∫ z, g z ∂M (update S i x) + δ ∧
      ∫ z, g z ∂M (update S i x) ≤ exp ε * ∫ z, g z ∂M S + δ := by
  by_cases h : S i = x
  · have hS : update S i x = S := by rw [← h, update_eq_self]
    have h0 : 0 ≤ ∫ z, g z ∂M S := integral_nonneg fun z ↦ (hg₁ z).1
    have h1 : ∫ z, g z ∂M S ≤ exp ε * ∫ z, g z ∂M S + δ := by nlinarith [one_le_exp hε]
    rw [hS]
    exact ⟨h1, h1⟩
  · have h1 := hammingDist_update_of_ne h
    exact ⟨hM.integral_le_exp_mul_integral_add h1 hg hg₁,
      hM.integral_le_exp_mul_integral_add ((hammingDist_comm _ _).trans h1) hg hg₁⟩

/-- A function on `(ι → 𝒳) × Z` that is bounded and measurable in its second argument is
integrable for the joint law of the dataset and the output. -/
lemma integrable_of_abs_le [Finite 𝒳] [MeasurableSingletonClass 𝒳] {f : (ι → 𝒳) × Z → ℝ}
    (hf : ∀ S, Measurable fun z ↦ f (S, z))
    {C : ℝ} (hC : ∀ q, |f q| ≤ C) : Integrable f (Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) :=
  Integrable.of_bound (measurable_from_prod_countable_right hf).aestronglyMeasurable C
    (ae_of_all _ fun q ↦ (Real.norm_eq_abs _).trans_le (hC q))

/-- The joint expectation of a bounded function as a finite sum over datasets. -/
lemma integral_compProd_eq_sum [DecidableEq ι] [Fintype 𝒳] [MeasurableSingletonClass 𝒳]
    {f : (ι → 𝒳) × Z → ℝ}
    (hf : ∀ S, Measurable fun z ↦ f (S, z)) {C : ℝ} (hC : ∀ q, |f q| ≤ C) :
    ∫ q, f q ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) =
      ∑ S : ι → 𝒳, (∏ j, P.real {S j}) * ∫ z, f (S, z) ∂M S := by
  rw [Measure.integral_compProd (integrable_of_abs_le hf hC),
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [smul_eq_mul, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

/-- On a finite alphabet, the population mean `P[g] = ∫ g dP` is a finite sum. -/
lemma integral_eq_sum [Fintype 𝒳] [MeasurableSingletonClass 𝒳] (g : 𝒳 → ℝ) :
    ∫ x, g x ∂P = ∑ x, P.real {x} * g x := by
  simp [integral_fintype Integrable.of_finite]

/-- The population mean `z ↦ P[Q z]` of a measurable family of queries is measurable. -/
lemma measurable_integral [Finite 𝒳] [MeasurableSingletonClass 𝒳] {g : Z → 𝒳 → ℝ}
    (hg : ∀ x, Measurable fun z ↦ g z x) :
    Measurable fun z ↦ ∫ x, g z x ∂P := by
  have := Fintype.ofFinite 𝒳
  simp_rw [integral_eq_sum]
  exact Finset.measurable_sum _ fun x _ ↦ (hg x).const_mul _

/-- The de-correlated expectation lemma at one record `i`, in both directions. -/
lemma integral_apply_le [Finite 𝒳] [MeasurableSingletonClass 𝒳] [DecidableEq 𝒳]
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) {g : Z → 𝒳 → ℝ} (hg : ∀ x, Measurable fun z ↦ g z x)
    (hg₁ : ∀ z x, g z x ∈ Icc (0 : ℝ) 1) (i : ι) :
    ∫ q, g q.2 (q.1 i) ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) ≤
        exp ε * ∫ q, ∫ x, g q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) + δ ∧
      ∫ q, ∫ x, g q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) ≤
        exp ε * ∫ q, g q.2 (q.1 i) ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) + δ := by
  classical
  have := Fintype.ofFinite 𝒳
  have hint (x : 𝒳) (S : ι → 𝒳) : Integrable (fun z ↦ g z x) (M S) :=
    Integrable.of_mem_Icc 0 1 (hg x).aemeasurable (ae_of_all _ fun z ↦ hg₁ z x)
  have hA : ∫ q, g q.2 (q.1 i) ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) =
      ∑ S : ι → 𝒳, (∏ j, P.real {S j}) * ∫ z, g z (S i) ∂M S :=
    integral_compProd_eq_sum (f := fun q ↦ g q.2 (q.1 i)) (fun S ↦ hg (S i))
      fun q ↦ abs_le_one_of_mem_Icc (hg₁ _ _)
  have hB : ∫ q, ∫ x, g q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) =
      ∑ S : ι → 𝒳, (∏ j, P.real {S j}) * ∑ x, P.real {x} * ∫ z, g z x ∂M S := by
    rw [integral_compProd_eq_sum (f := fun q ↦ ∫ x, g q.2 x ∂P) (fun S ↦ measurable_integral hg)
      fun q ↦ abs_le_one_of_mem_Icc (integral_mem_Icc (hg₁ q.2))]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp_rw [integral_eq_sum (P := P)]
    rw [integral_finsetSum _ fun x _ ↦ (hint x S).const_mul _]
    simp_rw [integral_const_mul]
  have hp (x : 𝒳) : 0 ≤ P.real {x} := measureReal_nonneg
  have hp₁ : ∑ x, P.real {x} = 1 := by simp
  rw [hA, hB]
  exact ⟨sum_le_mul_sum_add hp hp₁ i fun S x y ↦
      (integral_le_update hM hε hδ (hg y) (fun z ↦ hg₁ z y) S i x).1,
    sum_le_mul_sum_add' hp hp₁ i fun S x y ↦
      (integral_le_update hM hε hδ (hg y) (fun z ↦ hg₁ z y) S i x).2⟩

/-- The value `Q_{M(S)}(Sᵢ)` of the query at the `i`-th record is integrable. -/
lemma integrable_apply [Finite 𝒳] [MeasurableSingletonClass 𝒳] {g : Z → 𝒳 → ℝ}
    (hg : ∀ x, Measurable fun z ↦ g z x) (hg₁ : ∀ z x, g z x ∈ Icc (0 : ℝ) 1) (i : ι) :
    Integrable (fun q : (ι → 𝒳) × Z ↦ g q.2 (q.1 i)) (Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) :=
  integrable_of_abs_le (fun S ↦ hg (S i)) fun _ ↦ abs_le_one_of_mem_Icc (hg₁ _ _)

/-- The population value `P[Q_{M(S)}]` of the query is integrable. -/
lemma integrable_integral [Finite 𝒳] [MeasurableSingletonClass 𝒳] {g : Z → 𝒳 → ℝ}
    (hg : ∀ x, Measurable fun z ↦ g z x) (hg₁ : ∀ z x, g z x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun q : (ι → 𝒳) × Z ↦ ∫ x, g q.2 x ∂P) (Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) :=
  integrable_of_abs_le (fun _ ↦ measurable_integral hg)
    fun q ↦ abs_le_one_of_mem_Icc (integral_mem_Icc (hg₁ q.2))

/-- The query of Lemma 3.2 seen at a record `(m, i)`, namely `Q z x` if the selected sample `t` is
`m` and `0` otherwise, is measurable in the output `(z, t)`. -/
lemma measurable_ite {κ : Type*} [DecidableEq κ] {mκ : MeasurableSpace κ}
    [MeasurableSingletonClass κ] {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x) (m : κ)
    (x : 𝒳) : Measurable fun zt : Z × κ ↦ if zt.2 = m then Q zt.1 x else 0 :=
  Measurable.ite ((measurableSet_singleton m).preimage measurable_snd)
    ((hQ x).comp measurable_fst) measurable_const

/-- The query of Lemma 3.2 seen at a record takes values in `[0, 1]`. -/
lemma ite_mem_Icc {κ : Type*} [DecidableEq κ] {Q : Z → 𝒳 → ℝ}
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) (m : κ) (zt : Z × κ) (x : 𝒳) :
    (if zt.2 = m then Q zt.1 x else 0) ∈ Icc (0 : ℝ) 1 := by
  split_ifs
  · exact hQ₁ _ _
  · simp

/-- Summing the query of Lemma 3.2 over all records gives the sum over the selected sample. -/
lemma sum_ite_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (Q : Z → 𝒳 → ℝ)
    (q : (κ × ι → 𝒳) × (Z × κ)) :
    ∑ mi : κ × ι, (if q.2.2 = mi.1 then Q q.2.1 (q.1 mi) else 0) =
      ∑ i, Q q.2.1 (q.1 (q.2.2, i)) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

omit [IsProbabilityMeasure P] in
/-- Summing the population values of the query of Lemma 3.2 over all records gives `n P[Q_z]`. -/
lemma sum_integral_ite {κ : Type*} [Fintype κ] [DecidableEq κ] (Q : Z → 𝒳 → ℝ) (zt : Z × κ) :
    ∑ mi : κ × ι, ∫ x, (if zt.2 = mi.1 then Q zt.1 x else 0) ∂P =
      Fintype.card ι * ∫ x, Q zt.1 x ∂P := by
  have h (m : κ) : ∫ x, (if zt.2 = m then Q zt.1 x else 0) ∂P =
      if zt.2 = m then ∫ x, Q zt.1 x ∂P else 0 := by
    split_ifs <;> simp
  simp only [Fintype.sum_prod_type, h]
  rw [Finset.sum_comm]
  simp

end Generalization

variable [Finite 𝒳] [MeasurableSingletonClass 𝒳] [DecidableEq 𝒳]

/-- **The de-correlated expectation lemma**, general form behind Lemmas 3.1 and 3.2 of Bassily et
al.: let `M` be `(ε, δ)`-differentially private on datasets `S ∈ 𝒳^ι` (neighbours differ in
exactly one record), let `S ∼ Pⁿ` with `n = |ι|`, and let `gᵢ : Z × 𝒳 → [0, 1]`. Then
`E[∑ᵢ gᵢ(M(S), Sᵢ)] ≤ e^ε E[∑ᵢ E_{x∼P}[gᵢ(M(S), x)]] + n δ`, where the outer expectations are
over the joint law of `(S, M(S))`. -/
theorem IsEpsDeltaDP.integral_sum_le
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {g : ι → Z → 𝒳 → ℝ} (hg : ∀ i x, Measurable fun z ↦ g i z x)
    (hg₁ : ∀ i z x, g i z x ∈ Icc (0 : ℝ) 1) :
    ∫ q, ∑ i, g i q.2 (q.1 i) ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) ≤
      exp ε * ∫ q, ∑ i, ∫ x, g i q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) +
        Fintype.card ι * δ := by
  rw [integral_finsetSum _ fun i _ ↦ Generalization.integrable_apply (hg i) (hg₁ i) i,
    integral_finsetSum _ fun i _ ↦ Generalization.integrable_integral (hg i) (hg₁ i),
    Finset.mul_sum]
  refine (Finset.sum_le_sum fun i _ ↦
    (Generalization.integral_apply_le hM hε hδ (hg i) (hg₁ i) i).1).trans_eq ?_
  simp [Finset.sum_add_distrib]

/-- **The de-correlated expectation lemma**, reverse direction (the "identical argument" in the
proofs of Lemmas 3.1 and 3.2 of Bassily et al.):
`E[∑ᵢ E_{x∼P}[gᵢ(M(S), x)]] ≤ e^ε E[∑ᵢ gᵢ(M(S), Sᵢ)] + n δ`. -/
theorem IsEpsDeltaDP.integral_sum_integral_le
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {g : ι → Z → 𝒳 → ℝ} (hg : ∀ i x, Measurable fun z ↦ g i z x)
    (hg₁ : ∀ i z x, g i z x ∈ Icc (0 : ℝ) 1) :
    ∫ q, ∑ i, ∫ x, g i q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) ≤
      exp ε * ∫ q, ∑ i, g i q.2 (q.1 i) ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) +
        Fintype.card ι * δ := by
  rw [integral_finsetSum _ fun i _ ↦ Generalization.integrable_apply (hg i) (hg₁ i) i,
    integral_finsetSum _ fun i _ ↦ Generalization.integrable_integral (hg i) (hg₁ i),
    Finset.mul_sum]
  refine (Finset.sum_le_sum fun i _ ↦
    (Generalization.integral_apply_le hM hε hδ (hg i) (hg₁ i) i).2).trans_eq ?_
  simp [Finset.sum_add_distrib]


/-- **Lemma 3.1 of Bassily et al.** (finite-alphabet special case), first inequality of its
proof, and one direction of the proof of **Corollary 7 of Dwork et al. (STOC 2015)**: if `M` is
`(ε, δ)`-differentially private on datasets of `n ≥ 1` records and outputs a statistical query
`Q z : 𝒳 → [0, 1]`, and `S ∼ Pⁿ`, then
`E[E_S[Q_{M(S)}]] ≤ e^ε E[P[Q_{M(S)}]] + δ`. -/
theorem IsEpsDeltaDP.integral_empiricalMean_le [Nonempty ι]
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x)
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) :
    ∫ q, Generalization.empiricalMean (Q q.2) q.1 ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) ≤
      exp ε * ∫ q, ∫ x, Q q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) + δ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have h := hM.integral_sum_le (P := P) hε hδ (g := fun _ ↦ Q) (fun _ ↦ hQ) fun _ ↦ hQ₁
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, integral_const_mul] at h
  simp only [Generalization.empiricalMean, integral_div]
  rw [div_le_iff₀ hn]
  linarith

/-- **Lemma 3.1 of Bassily et al.** (finite-alphabet special case), reverse inequality ("an
identical argument shows"):
`E[P[Q_{M(S)}]] ≤ e^ε E[E_S[Q_{M(S)}]] + δ`, i.e.
`E[E_S[Q_{M(S)}]] ≥ e^{-ε} (E[P[Q_{M(S)}]] - δ)`. -/
theorem IsEpsDeltaDP.integral_le_integral_empiricalMean [Nonempty ι]
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x)
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) :
    ∫ q, ∫ x, Q q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) ≤
      exp ε * ∫ q, Generalization.empiricalMean (Q q.2) q.1 ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) +
        δ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have h := hM.integral_sum_integral_le (P := P) hε hδ (g := fun _ ↦ Q) (fun _ ↦ hQ) fun _ ↦ hQ₁
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, integral_const_mul] at h
  simp only [Generalization.empiricalMean, integral_div]
  rw [mul_div_assoc', div_add' _ _ _ hn.ne', le_div_iff₀ hn]
  linarith

/-- **Corollary 7 of Dwork et al. (STOC 2015)** and the conclusion of **Lemma 3.1 of Bassily et
al.** (finite-alphabet special case): differential privacy implies generalization in
expectation. If `M` is `(ε, δ)`-differentially private on datasets of `n ≥ 1` records and outputs
a statistical query `Q z : 𝒳 → [0, 1]`, and `S ∼ Pⁿ`, then
`|E[E_S[Q_{M(S)}]] - E[P[Q_{M(S)}]]| ≤ e^ε - 1 + δ`. -/
theorem IsEpsDeltaDP.abs_integral_empiricalMean_sub_integral_le [Nonempty ι]
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x)
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) :
    |∫ q, Generalization.empiricalMean (Q q.2) q.1 ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M) -
      ∫ q, ∫ x, Q q.2 x ∂P ∂(Measure.pi (fun _ : ι ↦ P) ⊗ₘ M)| ≤ exp ε - 1 + δ := by
  have h₁ := hM.integral_empiricalMean_le (P := P) hε hδ hQ hQ₁
  have h₂ := hM.integral_le_integral_empiricalMean (P := P) hε hδ hQ hQ₁
  have hA := Generalization.integral_mem_Icc (μ := Measure.pi (fun _ : ι ↦ P) ⊗ₘ M)
    fun q ↦ Generalization.empiricalMean_mem_Icc (hQ₁ q.2) q.1
  have hB := Generalization.integral_mem_Icc (μ := Measure.pi (fun _ : ι ↦ P) ⊗ₘ M)
    fun q ↦ Generalization.integral_mem_Icc (μ := P) (hQ₁ q.2)
  have he := one_le_exp hε
  rw [abs_le]
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]

/-! ### Several samples: Lemma 3.2 of Bassily et al. -/

section MultiSample

variable {κ : Type*} [Fintype κ] {mκ : MeasurableSpace κ}
  [MeasurableSingletonClass κ] [Nonempty ι] {M : Kernel (κ × ι → 𝒳) (Z × κ)} [IsMarkovKernel M]

/-- **Lemma 3.2 of Bassily et al.** (multi-sample de-correlated expectation lemma;
finite-alphabet special case), first inequality of its proof: let `M` be
`(ε, δ)`-differentially private on collections `S ∈ (𝒳ⁿ)^T` of `T = |κ|` samples of
`n = |ι| ≥ 1` records each (indexed by `κ × ι`; neighbours differ in exactly one of the `T n`
records), output a statistical query `Q z : 𝒳 → [0, 1]` together with the index `t` of one sample,
and let `S ∼ (Pⁿ)^T`. Then `E[E_{S_t}[Q_z]] ≤ e^ε E[P[Q_z]] + T δ`. -/
theorem IsEpsDeltaDP.integral_empiricalMean_sample_le
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x)
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) :
    ∫ q, Generalization.empiricalMean (Q q.2.1) (fun i ↦ q.1 (q.2.2, i))
        ∂(Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M) ≤
      exp ε * ∫ q, ∫ x, Q q.2.1 x ∂P ∂(Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M) +
        Fintype.card κ * δ := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have h := hM.integral_sum_le (P := P) hε hδ
    (g := fun mi zt x ↦ if zt.2 = mi.1 then Q zt.1 x else 0)
    (fun mi x ↦ Generalization.measurable_ite hQ mi.1 x)
    fun mi zt x ↦ Generalization.ite_mem_Icc hQ₁ mi.1 zt x
  simp only [Generalization.sum_ite_apply, Generalization.sum_integral_ite, integral_const_mul,
    Fintype.card_prod, Nat.cast_mul] at h
  simp only [Generalization.empiricalMean, integral_div]
  rw [div_le_iff₀ hn]
  linarith

/-- **Lemma 3.2 of Bassily et al.** (finite-alphabet special case), reverse inequality ("an
identical argument shows"):
`E[P[Q_z]] ≤ e^ε E[E_{S_t}[Q_z]] + T δ`. -/
theorem IsEpsDeltaDP.integral_le_integral_empiricalMean_sample
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x)
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) :
    ∫ q, ∫ x, Q q.2.1 x ∂P ∂(Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M) ≤
      exp ε * ∫ q, Generalization.empiricalMean (Q q.2.1) (fun i ↦ q.1 (q.2.2, i))
        ∂(Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M) + Fintype.card κ * δ := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have h := hM.integral_sum_integral_le (P := P) hε hδ
    (g := fun mi zt x ↦ if zt.2 = mi.1 then Q zt.1 x else 0)
    (fun mi x ↦ Generalization.measurable_ite hQ mi.1 x)
    fun mi zt x ↦ Generalization.ite_mem_Icc hQ₁ mi.1 zt x
  simp only [Generalization.sum_ite_apply, Generalization.sum_integral_ite, integral_const_mul,
    Fintype.card_prod, Nat.cast_mul] at h
  simp only [Generalization.empiricalMean, integral_div]
  rw [mul_div_assoc', div_add' _ _ _ hn.ne', le_div_iff₀ hn]
  linarith

/-- **Lemma 3.2 of Bassily et al.** (finite-alphabet special case): in the setting of
`IsEpsDeltaDP.integral_empiricalMean_sample_le`,
`|E[P[Q_z]] - E[E_{S_t}[Q_z]]| ≤ e^ε - 1 + T δ`. -/
theorem IsEpsDeltaDP.abs_integral_sub_integral_empiricalMean_sample_le
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε δ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    {Q : Z → 𝒳 → ℝ} (hQ : ∀ x, Measurable fun z ↦ Q z x)
    (hQ₁ : ∀ z x, Q z x ∈ Icc (0 : ℝ) 1) :
    |∫ q, ∫ x, Q q.2.1 x ∂P ∂(Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M) -
      ∫ q, Generalization.empiricalMean (Q q.2.1) (fun i ↦ q.1 (q.2.2, i))
        ∂(Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M)| ≤ exp ε - 1 + Fintype.card κ * δ := by
  have h₁ := hM.integral_empiricalMean_sample_le (P := P) hε hδ hQ hQ₁
  have h₂ := hM.integral_le_integral_empiricalMean_sample (P := P) hε hδ hQ hQ₁
  have hA := Generalization.integral_mem_Icc (μ := Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M)
    fun q ↦ Generalization.empiricalMean_mem_Icc (hQ₁ q.2.1) fun i ↦ q.1 (q.2.2, i)
  have hB := Generalization.integral_mem_Icc (μ := Measure.pi (fun _ : κ × ι ↦ P) ⊗ₘ M)
    fun q ↦ Generalization.integral_mem_Icc (μ := P) (hQ₁ q.2.1)
  have he := one_le_exp hε
  rw [abs_le]
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]

end MultiSample

end Expectation

end InformationTheory
