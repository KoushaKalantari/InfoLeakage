/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.FInformation.Pinsker
public import InfoLeakage.LocalPrivacy.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Pinsker's inequality and the mutual-information step of the private local Fano bound

This file closes the gap left in `InfoLeakage.LocalPrivacy.Basic` in the formalization of
J. C. Duchi, M. I. Jordan and M. J. Wainwright, *Local privacy, data processing inequalities, and
minimax rates*, [arXiv:1302.3203v4](https://arxiv.org/abs/1302.3203) (conference version *Local
privacy and statistical minimax rates*, FOCS 2013). Result and equation numbers refer to arXiv v4.

There, the mutual information step of **Corollary 3** (private form of the local Fano inequality)
was formalized (`mutualInfoUniform_seqMarginal_le_four_mul`) under the total variation bound
`‖P_ν - P_ν'‖²_TV ≤ κ² δ² / 2`, which the paper derives from the `(δ, κ)` local packing condition
(17), `D_kl(P_ν ‖ P_ν') ≤ κ² δ²` for `ν ≠ ν'`, by Pinsker's inequality. Here we prove Pinsker's
inequality for the finite-sum total variation distance `tvDistSum` from the measure-theoretic
Pinsker inequality of `InfoLeakage.FInformation.Pinsker` (through the bridge
`klDiv_eq_ofReal_klDivSum`), and state the mutual information step of Corollary 3 under the packing
condition (17) itself. Only the divergence bound of (17) is assumed: the `2δ`-separation
`ρ(θ(P_ν), θ(P_ν')) ≥ 2δ` of a `(δ, κ)` local packing and `κ > 0` are not, which makes the
results stronger (they are only needed for the Fano bound (19), which is not formalized). The
alphabets are finite: both the data alphabet `α` and the private output alphabet `β`, which
excludes continuous channels such as additive Laplace noise.

## Main statements

* `ofReal_two_mul_sq_tvDistSum_real_le_klDiv`: Pinsker's inequality
  `2 ‖μ - ν‖²_TV ≤ D_kl(μ ‖ ν)` for probability measures on a finite alphabet, with the total
  variation distance `tvDistSum` of their point masses and Mathlib's `klDiv`.
* `two_mul_sq_tvDistSum_le_klDivSum`: the same for probability vectors `p ≪ q`, with `klDivSum`.
* `mutualInfoUniform_seqMarginal_le_four_mul_of_klDiv_le`: the mutual information step of
  **Corollary 3**, `I(Z_{1:n}; V) ≤ 4 n ε² κ² δ²` for `ε ∈ [0, 22/35]`, for i.i.d. samples from a
  family satisfying the divergence bound of the `(δ, κ)` local packing condition (17) (the
  `2δ`-separation and `κ > 0` are not assumed).

## Correspondence with the paper

* Pinsker's inequality in the form `‖P₁ - P₂‖²_TV ≤ D_kl(P₁ ‖ P₂) / 2` used after Corollary 2 and
  in the proof of Corollary 3: `ofReal_two_mul_sq_tvDistSum_real_le_klDiv` (measures) and
  `two_mul_sq_tvDistSum_le_klDivSum` (vectors).
* Corollary 3, the bound `I(Z_{1:n}; V) ≤ 4 n α² κ² δ²` of its proof (the paper's privacy level `α`
  is `ε` here), from the packing condition (17):
  `mutualInfoUniform_seqMarginal_le_four_mul_of_klDiv_le`, in the paper's i.i.d. setting
  `P_{ν,i} ≡ P_ν`, with (17) stated with Mathlib's `klDiv` of the laws `P_ν` (no absolute
  continuity hypothesis is needed: a finite divergence forces it). The non-identically
  distributed version with finite sums, where (17) is asked for every sample `i` and the absolute
  continuity `P_ν' ≫ P_ν` (implied by (17) for the true divergence) is a hypothesis since
  `klDivSum` uses `log 0 = 0`: `mutualInfoUniform_seqMarginal_le_four_mul_of_klDivSum_le`.

## Implementation notes

The finite-sum Pinsker inequality is obtained from the event form
`ofReal_two_mul_sq_measureReal_sub_le_klDiv` of `InfoLeakage.FInformation.Pinsker`, applied to the
event `{x | ν {x} < μ {x}}`, which attains the total variation distance
(`sum_filter_lt_sub_eq_tvDistSum`). For vectors, the probability measures with point masses `p` and
`q` are built as `PMF.toMeasure` for the discrete σ-algebra. An independent elementary proof of the
vector form is `SemanticSecurity.two_mul_sq_tvDistSum_le` (in `InfoLeakage.SemanticSecurity.Basic`).

## Not formalized

The Fano lower bound (19) on the private minimax risk itself, and the classical local Fano bound
(18), which concern estimators and minimax risks.
-/

@[expose] public section

open Finset Real MeasureTheory

open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [Fintype α]

/-! ### Pinsker's inequality on a finite alphabet -/

section Pinsker

/-- **Pinsker's inequality** on a finite alphabet, in nats, for probability measures:
`2 ‖μ - ν‖²_TV ≤ D_kl(μ ‖ ν)`, where `‖μ - ν‖_TV = (1/2) ∑_x |μ {x} - ν {x}|` is `tvDistSum` of the
point masses (the normalization of Duchi–Jordan–Wainwright) and `D_kl` is Mathlib's `klDiv`. It is
the measure-theoretic Pinsker inequality `ofReal_two_mul_sq_measureReal_sub_le_klDiv` for the event
`{x | ν {x} < μ {x}}`. -/
theorem ofReal_two_mul_sq_tvDistSum_real_le_klDiv [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * tvDistSum (fun x ↦ μ.real {x}) (fun x ↦ ν.real {x}) ^ 2) ≤ klDiv μ ν := by
  have h : ∑ x, μ.real {x} = ∑ x, ν.real {x} := by
    rw [sum_measureReal_singleton, sum_measureReal_singleton, coe_univ, probReal_univ,
      probReal_univ]
  have htv := sum_filter_lt_sub_eq_tvDistSum h
  rw [sum_measureReal_singleton, sum_measureReal_singleton] at htv
  rw [← htv]
  exact ofReal_two_mul_sq_measureReal_sub_le_klDiv (Finset.measurableSet _)

/-- **Pinsker's inequality** on a finite alphabet, in nats, for probability vectors: if `p` and `q`
are probability vectors with `p ≪ q` (`q x = 0 → p x = 0`), then
`2 ‖p - q‖²_TV ≤ D_kl(p ‖ q) = ∑_x p x log (p x / q x)`, where `‖p - q‖_TV = tvDistSum p q`. This
is the inequality `‖P₁ - P₂‖²_TV ≤ D_kl(P₁ ‖ P₂) / 2` used by Duchi–Jordan–Wainwright after
Corollary 2 and in the proof of Corollary 3. -/
theorem two_mul_sq_tvDistSum_le_klDivSum {p q : α → ℝ} (hp₀ : ∀ x, 0 ≤ p x)
    (hp₁ : ∑ x, p x = 1) (hq₀ : ∀ x, 0 ≤ q x) (hq₁ : ∑ x, q x = 1)
    (hpq : ∀ x, q x = 0 → p x = 0) :
    2 * tvDistSum p q ^ 2 ≤ klDivSum p q := by
  let : MeasurableSpace α := ⊤
  have hsum {r : α → ℝ} (hr₀ : ∀ x, 0 ≤ r x) (hr₁ : ∑ x, r x = 1) :
      ∑ x, ENNReal.ofReal (r x) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hr₀ x, hr₁, ENNReal.ofReal_one]
  -- the probability measures with point masses `p` and `q`
  set μ := (PMF.ofFintype _ (hsum hp₀ hp₁)).toMeasure
  set ν := (PMF.ofFintype _ (hsum hq₀ hq₁)).toMeasure
  have hμ (x : α) : μ {x} = ENNReal.ofReal (p x) := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), PMF.ofFintype_apply]
  have hν (x : α) : ν {x} = ENNReal.ofReal (q x) := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), PMF.ofFintype_apply]
  have hμr : (fun x ↦ μ.real {x}) = p := funext fun x ↦ by
    rw [measureReal_def, hμ, ENNReal.toReal_ofReal (hp₀ x)]
  have hνr : (fun x ↦ ν.real {x}) = q := funext fun x ↦ by
    rw [measureReal_def, hν, ENNReal.toReal_ofReal (hq₀ x)]
  have hac : μ ≪ ν := by
    intro s hs
    rw [measure_eq_zero_iff_ae_notMem, ae_iff_of_countable] at hs ⊢
    refine fun x hx ↦ hs x fun hνx ↦ hx ?_
    rw [hν, ENNReal.ofReal_eq_zero] at hνx
    rw [hμ, hpq x (le_antisymm hνx (hq₀ x)), ENNReal.ofReal_zero]
  have hkl := klDiv_eq_ofReal_klDivSum hac
  have h := ofReal_two_mul_sq_tvDistSum_real_le_klDiv μ ν
  rw [ENNReal.ofReal_le_iff_le_toReal (by rw [hkl]; exact ENNReal.ofReal_ne_top),
    toReal_klDiv_of_measure_eq hac (by rw [measure_univ, measure_univ]),
    integral_llr_eq_klDivSum hac, hμr, hνr] at h
  exact h

end Pinsker

/-! ### The mutual-information step of the private local Fano bound -/

section Fano

variable {ι β : Type*} [Fintype ι] [Nonempty ι] [Fintype β]
  {Q : (i : ℕ) → (Fin i → β) → α → β → ℝ} {ε κ δ : ℝ}

/-- The mutual information step of **Corollary 3** (private local Fano) of
Duchi–Jordan–Wainwright, on finite alphabets (finite data alphabet `α` and finite private output
alphabet `β`, which excludes continuous channels such as additive Laplace noise), from the
divergence bound of the `(δ, κ)` local packing condition (17) (the `2δ`-separation and `κ > 0` are
not assumed): let
`V` be uniform on the finite set `ι` and, given `V = ν`, let the samples `X_1, …, X_n` be i.i.d.
with law `P_ν` and released through a sequentially interactive channel each of whose steps is
`ε`-locally differentially private. If `D_kl(P_ν ‖ P_ν') ≤ κ² δ²` for all `ν ≠ ν'` (Mathlib's
`klDiv`) and `ε ∈ [0, 22/35]`, then `I(Z_{1:n}; V) ≤ 4 n ε² κ² δ²`. The law of `X_i` is given to
`seqMarginal` through its point masses `x ↦ P_ν {x}`. The channel hypotheses are assumed for all
`i : ℕ`; only `i < n` matters. This is not the Fano lower bound (19) itself. -/
theorem mutualInfoUniform_seqMarginal_le_four_mul_of_klDiv_le [MeasurableSpace α]
    [MeasurableSingletonClass α] {P : ι → Measure α} [∀ ν, IsProbabilityMeasure (P ν)]
    (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z) (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1)
    (hQ : ∀ i h, IsLocalDP (Q i h) ε) (hε₀ : 0 ≤ ε) (hε : ε ≤ 22 / 35)
    (hP : ∀ ν ν', ν ≠ ν' → klDiv (P ν) (P ν') ≤ ENNReal.ofReal (κ ^ 2 * δ ^ 2)) (n : ℕ) :
    mutualInfoUniform (fun ν ↦ seqMarginal (fun _ x ↦ (P ν).real {x}) Q n) ≤
      4 * n * ε ^ 2 * κ ^ 2 * δ ^ 2 := by
  refine mutualInfoUniform_seqMarginal_le_four_mul hQ₀ hQ₁ hQ (fun _ _ _ ↦ measureReal_nonneg)
    (fun ν _ ↦ by rw [sum_measureReal_singleton, coe_univ, probReal_univ]) hε₀ hε
    (fun ν ν' _ ↦ ?_) n
  rcases eq_or_ne ν ν' with rfl | hνν'
  · simp only [tvDistSum, sub_self, abs_zero, sum_const_zero, zero_div, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · have h := (ofReal_two_mul_sq_tvDistSum_real_le_klDiv (P ν) (P ν')).trans (hP ν ν' hνν')
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    linarith

/-- The mutual information step of **Corollary 3** (private local Fano) of
Duchi–Jordan–Wainwright, on finite alphabets (finite data alphabet `α` and finite private output
alphabet `β`, which excludes continuous channels such as additive Laplace noise), for independent
but not necessarily identically distributed samples, from the divergence bound of the packing
condition (17) for every sample (the `2δ`-separation and `κ > 0` are not assumed), with finite
sums: if
`V` is uniform on the finite set `ι`, the samples `X_i ∼ P ν i` given `V = ν` are released
through a sequentially interactive channel each of whose steps is `ε`-locally differentially
private, `P ν' i ≫ P ν i` and `D_kl(P ν i ‖ P ν' i) ≤ κ² δ²` for all `ν ≠ ν'` and all `i : ℕ`
(only `i < n` matters), and `ε ∈ [0, 22/35]`, then `I(Z_{1:n}; V) ≤ 4 n ε² κ² δ²`. The absolute
continuity hypothesis is implied by (17) for the true divergence; it is needed here because
`klDivSum` uses the convention `log 0 = 0`. -/
theorem mutualInfoUniform_seqMarginal_le_four_mul_of_klDivSum_le {P : ι → ℕ → α → ℝ}
    (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z) (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1)
    (hQ : ∀ i h, IsLocalDP (Q i h) ε) (hP₀ : ∀ ν i x, 0 ≤ P ν i x)
    (hP₁ : ∀ ν i, ∑ x, P ν i x = 1) (hε₀ : 0 ≤ ε) (hε : ε ≤ 22 / 35)
    (hac : ∀ ν ν' i x, ν ≠ ν' → P ν' i x = 0 → P ν i x = 0)
    (hP : ∀ ν ν' i, ν ≠ ν' → klDivSum (P ν i) (P ν' i) ≤ κ ^ 2 * δ ^ 2) (n : ℕ) :
    mutualInfoUniform (fun ν ↦ seqMarginal (P ν) Q n) ≤ 4 * n * ε ^ 2 * κ ^ 2 * δ ^ 2 := by
  refine mutualInfoUniform_seqMarginal_le_four_mul hQ₀ hQ₁ hQ hP₀ hP₁ hε₀ hε
    (fun ν ν' i ↦ ?_) n
  rcases eq_or_ne ν ν' with rfl | hνν'
  · simp only [tvDistSum, sub_self, abs_zero, sum_const_zero, zero_div, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · have h := two_mul_sq_tvDistSum_le_klDivSum (hP₀ ν i) (hP₁ ν i) (hP₀ ν' i) (hP₁ ν' i)
      fun x ↦ hac ν ν' i x hνν'
    linarith [hP ν ν' i hνν']

end Fano

end InformationTheory
