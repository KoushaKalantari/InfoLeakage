/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Laplace
public import InfoLeakage.RenyiDP.Basic

/-!
# Rényi differential privacy of the Laplace mechanism

This file formalizes the Laplace part (Section VI.B) of I. Mironov, *Rényi differential privacy*,
IEEE 30th Computer Security Foundations Symposium (CSF), 2017
([arXiv:1702.07476](https://arxiv.org/abs/1702.07476)); result numbers follow arXiv v3. It computes
the Rényi divergence between two Laplace distributions with the same scale in closed form and
deduces the Rényi differential privacy of the Laplace mechanism `laplaceMechanism` of
`InfoLeakage.DP.Laplace`.

The Laplace distribution `Lap(μ, b) = laplaceMeasure μ b` (the paper's `Λ(μ, λ)`) has density
`(2b)⁻¹ exp (-|y - μ| / b)` with respect to Lebesgue measure on `ℝ`. The divergence is Statlib's
`renyiDiv` (in nats, with values in `ℝ≥0∞`; `renyiDiv 1` is the Kullback–Leibler divergence) and
privacy is `IsRenyiDP` from `InfoLeakage.RenyiDP.Basic`. The space of datasets is an arbitrary
measurable space and the neighbouring relation is arbitrary.

## Main statements (paper result → Lean name)

* Proposition 6 (order `α > 1`), for arbitrary locations `μ, μ'` and `d = |μ - μ'|`:
  `D_α(Lap(μ, b) ‖ Lap(μ', b))
    = (α - 1)⁻¹ log (α / (2α - 1) exp ((α - 1) d / b) + (α - 1) / (2α - 1) exp (-α d / b))`:
  `RenyiDP.renyiDiv_laplaceMeasure`; the paper's case `Λ(0, λ)`, `Λ(1, λ)`:
  `RenyiDP.renyiDiv_laplaceMeasure_zero_one`.
* The integral computed in the proof of Proposition 6 (the Hellinger integral), for every order
  `α ≠ 1/2`: `RenyiDP.integral_laplacePDFReal_rpow_mul_rpow`.
* Table II, row "Laplace mechanism", order `α = 1`: `D_1 = d / b + exp (-d / b) - 1`:
  `RenyiDP.klDiv_laplaceMeasure`, `RenyiDP.renyiDiv_one_laplaceMeasure`; the paper's case
  `1 / λ + exp (-1 / λ) - 1`: `RenyiDP.renyiDiv_one_laplaceMeasure_zero_one`.
* The limits stated after Corollary 2: `lim_{α → ∞} D_α = d / b` (`1 / λ` in the paper's case):
  `RenyiDP.tendsto_renyiDiv_laplaceMeasure_atTop`; `lim_{α → 1⁺} D_α = D_1`:
  `RenyiDP.tendsto_renyiDiv_laplaceMeasure_one`.
* Corollary 2 (the Laplace mechanism is `(α, ε(α))`-RDP), for a sensitivity bound `Δ` and a noise
  scale `b > 0` (the paper has `Δ = 1` and `b = λ`): `isRenyiDP_laplaceMechanism` (`α > 1`) and
  `isRenyiDP_one_laplaceMechanism` (`α = 1`, Table II).
* Auxiliary results on Laplace distributions: mutual absolute continuity with Lebesgue measure
  (`RenyiDP.absolutelyContinuous_volume_laplaceMeasure`,
  `RenyiDP.laplaceMeasure_absolutelyContinuous_volume`) and the Radon–Nikodym derivative
  `RenyiDP.rnDeriv_laplaceMeasure_ae_eq`.

## Implementation notes

* As in the paper's proof, the integrals are split over `(-∞, 0]`, `[0, d]` and `[d, ∞)`, after a
  translation and a reflection reduce the locations `μ, μ'` to `0` and `d = |μ - μ'| ≥ 0`.
* Corollary 2 also uses that the closed form is nondecreasing in `d` (for `α > 1` and for
  `α = 1`), proved here by calculus; the paper leaves this step implicit.
* The privacy parameter of `IsRenyiDP` is in `ℝ≥0`, so the budgets of Corollary 2 are wrapped in
  `Real.toNNReal`. For `Δ ≥ 0` they are nonnegative (`RenyiDP.inv_sub_one_mul_log_laplace_nonneg`,
  `RenyiDP.div_add_exp_neg_div_sub_one_nonneg`), so this does not change them.
* Statlib has no Rényi divergence of order `∞`, so `D_∞ = 1 / λ` is not stated; the
  corresponding privacy statement, `Δ / b`-differential privacy of the Laplace mechanism, is
  `isEpsDeltaDP_laplaceMechanism_of_le`.

## Notes on the paper

* Proposition 6 (arXiv v3, Section VI.B) is stated "for any `α ≥ 1`", but its formula contains
  the factor `1 / (α - 1)` and is undefined at `α = 1`; the value at `α = 1` is given separately,
  as a limit, after Corollary 2 and in Table II. The proposition is true for `α > 1`
  (`RenyiDP.renyiDiv_laplaceMeasure`), and so is the value at `α = 1`
  (`RenyiDP.renyiDiv_one_laplaceMeasure`).
* Section VI.B, before Proposition 6: "to derive the RDP budget curve for the exponential
  mechanism" refers to the Laplace mechanism (the computation that follows is for the Laplace
  distribution and its offset); this is a wording slip with no effect on the results.

## Not formalized

The approximation `1 / λ + exp (-1 / λ) - 1 = .5 / λ² + O(1 / λ³)` of Table II and the plots and
numerical comparisons of Sections VI–VII.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace InformationTheory

namespace RenyiDP

variable {b d α : ℝ}

/-! ### Integrals of functions of `|y - μ|` and `|y - μ'|` -/

/-- By translation and reflection, an integral of a function of `|y - μ|` and `|y - μ'|` only
depends on `|μ - μ'|`. -/
private lemma integral_comp_abs_sub_abs_sub (F : ℝ → ℝ → ℝ) (μ μ' : ℝ) :
    ∫ y, F |y - μ| |y - μ'| = ∫ y, F |y| |y - (|μ - μ'|)| := by
  have h₁ : ∫ y, F |y - μ| |y - μ'| = ∫ y, F |y| |y - (μ' - μ)| := by
    rw [← integral_sub_right_eq_self (fun y ↦ F |y| |y - (μ' - μ)|) μ]
    congr 1
    ext y
    congr 2
    ring
  rw [h₁]
  rcases le_total μ μ' with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
  · rw [abs_of_nonneg (sub_nonneg.2 h), ← integral_neg_eq_self (fun y ↦ F |y| |y - (μ - μ')|)]
    congr 1
    ext y
    rw [abs_neg, show -y - (μ - μ') = -(y - (μ' - μ)) by ring, abs_neg]

/-- Splitting an integral over `ℝ` at `0` and `d`. -/
private lemma integral_eq_Iic_add_intervalIntegral_add_Ioi {f : ℝ → ℝ} (hf : Integrable f)
    (d : ℝ) :
    ∫ y, f y = (∫ y in Iic 0, f y) + (∫ y in (0 : ℝ)..d, f y) + ∫ y in Ioi d, f y := by
  rw [add_assoc, intervalIntegral.integral_interval_add_Ioi hf.integrableOn hf.integrableOn,
    intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn]

/-- `y ↦ exp (-|y| / b)` is integrable for `b > 0`. -/
private lemma integrable_exp_neg_abs_div (hb : 0 < b) :
    Integrable fun y : ℝ ↦ exp (-|y| / b) := by
  refine ((integrable_laplacePDFReal 0 hb).const_mul (2 * b)).congr (ae_of_all _ fun y ↦ ?_)
  simp only [laplacePDFReal, sub_zero]
  field_simp

/-! ### The Hellinger integral of two Laplace distributions -/

/-- The integrand `exp (-(α |y| + (1 - α) |y - d|) / b)` of the Hellinger integral of two Laplace
distributions is integrable. -/
private lemma integrable_exp_neg_mul_abs_add (hb : 0 < b) (α d : ℝ) :
    Integrable fun y ↦ exp (-(α * |y| + (1 - α) * |y - d|) / b) := by
  refine ((integrable_exp_neg_abs_div hb).const_mul (exp (|1 - α| * |d| / b))).mono'
    (by fun_prop) (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  gcongr
  rw [← add_div, div_le_div_iff_of_pos_right hb]
  have h₁ : |y| - |d| ≤ |y - d| := abs_sub_abs_le_abs_sub y d
  have h₂ : |y - d| ≤ |y| + |d| := abs_sub _ _
  rcases le_total 0 (1 - α) with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_nonpos h]
    nlinarith

/-- The integral `∫ exp (-(α |y| + (1 - α) |y - d|) / b) dy` for `d ≥ 0`, `b > 0` and
`α ≠ 1/2`, computed separately over `(-∞, 0]`, `[0, d]` and `[d, ∞)` as in the proof of
Proposition 6 of Mironov. -/
private lemma integral_exp_neg_mul_abs_add (hb : 0 < b) (hd : 0 ≤ d) (hα : 2 * α - 1 ≠ 0) :
    ∫ y, exp (-(α * |y| + (1 - α) * |y - d|) / b) =
      b * (exp ((α - 1) * d / b) + exp (-α * d / b)
        + (exp ((α - 1) * d / b) - exp (-α * d / b)) / (2 * α - 1)) := by
  set A := exp ((α - 1) * d / b)
  set B := exp (-α * d / b)
  rw [integral_eq_Iic_add_intervalIntegral_add_Ioi (integrable_exp_neg_mul_abs_add hb α d) d]
  -- on `(-∞, 0]`
  have h₁ : ∫ y in Iic 0, exp (-(α * |y| + (1 - α) * |y - d|) / b) = b * A := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun y ↦ A * exp (b⁻¹ * y))
      fun y hy ↦ ?_, integral_const_mul, integral_exp_mul_Iic (inv_pos.2 hb), mul_zero, exp_zero]
    · field_simp
    · simp only [mem_Iic] at hy
      rw [abs_of_nonpos hy, abs_of_nonpos (by linarith)]
      simp only [A, ← exp_add]
      congr 1
      field_simp
      ring
  -- on `[d, ∞)`
  have h₃ : ∫ y in Ioi d, exp (-(α * |y| + (1 - α) * |y - d|) / b) = b * B := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun y ↦ exp ((1 - α) * d / b) * exp (-b⁻¹ * y)) fun y hy ↦ ?_, integral_const_mul,
      integral_exp_mul_Ioi (neg_lt_zero.2 (inv_pos.2 hb)), neg_div_neg_eq, ← mul_div_assoc,
      ← exp_add, show (1 - α) * d / b + -b⁻¹ * d = -α * d / b by field_simp; ring]
    · field_simp
      simp only [B, neg_mul, neg_div]
    · simp only [mem_Ioi] at hy
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      simp only [← exp_add]
      congr 1
      field_simp
      ring
  -- on `[0, d]`
  have h₂ : ∫ y in (0 : ℝ)..d, exp (-(α * |y| + (1 - α) * |y - d|) / b) =
      b * (A - B) / (2 * α - 1) := by
    have hc : -(2 * α - 1) / b ≠ 0 := div_ne_zero (neg_ne_zero.2 hα) hb.ne'
    rw [intervalIntegral.integral_congr (g := fun y ↦ A * exp (-(2 * α - 1) / b * y))
      fun y hy ↦ ?_, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun y ↦ exp y) hc, integral_exp, mul_zero,
      exp_zero, smul_eq_mul]
    · have hAB : A * exp (-(2 * α - 1) / b * d) = B := by
        simp only [A, B, ← exp_add]
        congr 1
        field_simp
        ring
      rw [← hAB]
      field_simp
      ring
    · rw [uIcc_of_le hd] at hy
      rw [abs_of_nonneg hy.1, abs_of_nonpos (by linarith [hy.2])]
      simp only [A, ← exp_add]
      congr 1
      field_simp
      ring
  rw [h₁, h₂, h₃]
  field_simp
  ring

/-- Pointwise form of the Hellinger integrand of two Laplace densities:
`Lap(y | μ, b) ^ α Lap(y | μ', b) ^ (1 - α) = (2b)⁻¹ exp (-(α |y - μ| + (1 - α) |y - μ'|) / b)`. -/
private lemma laplacePDFReal_rpow_mul_rpow (hb : 0 < b) (μ μ' α y : ℝ) :
    laplacePDFReal μ b y ^ α * laplacePDFReal μ' b y ^ (1 - α) =
      (2 * b)⁻¹ * exp (-(α * |y - μ| + (1 - α) * |y - μ'|) / b) := by
  have h2b : 0 < (2 * b)⁻¹ := by positivity
  unfold laplacePDFReal
  rw [mul_rpow h2b.le (exp_pos _).le, mul_rpow h2b.le (exp_pos _).le, ← exp_mul, ← exp_mul,
    mul_mul_mul_comm, ← rpow_add h2b, add_sub_cancel, rpow_one, ← exp_add]
  congr 2
  field_simp
  ring

/-- The **Hellinger integral** of two Laplace distributions with the same scale `b > 0` (the
computation in the proof of Proposition 6 of Mironov, for arbitrary locations), for every order
`α ≠ 1/2`: with `d = |μ - μ'|`,
`∫ Lap(y | μ, b) ^ α Lap(y | μ', b) ^ (1 - α) dy
  = α / (2α - 1) exp ((α - 1) d / b) + (α - 1) / (2α - 1) exp (-α d / b)`. -/
theorem integral_laplacePDFReal_rpow_mul_rpow (μ μ' : ℝ) (hb : 0 < b) (hα : 2 * α - 1 ≠ 0) :
    ∫ y, laplacePDFReal μ b y ^ α * laplacePDFReal μ' b y ^ (1 - α) =
      α / (2 * α - 1) * exp ((α - 1) * |μ - μ'| / b) +
        (α - 1) / (2 * α - 1) * exp (-α * |μ - μ'| / b) := by
  simp_rw [laplacePDFReal_rpow_mul_rpow hb]
  rw [integral_const_mul,
    integral_comp_abs_sub_abs_sub (fun u v ↦ exp (-(α * u + (1 - α) * v) / b)) μ μ',
    integral_exp_neg_mul_abs_add hb (abs_nonneg _) hα]
  field_simp
  ring

/-! ### The Radon–Nikodym derivative of two Laplace distributions -/

/-- Lebesgue measure is absolutely continuous with respect to a Laplace distribution. -/
lemma absolutelyContinuous_volume_laplaceMeasure (μ : ℝ) (hb : 0 < b) :
    (volume : Measure ℝ) ≪ laplaceMeasure μ b :=
  withDensity_absolutelyContinuous' (measurable_laplacePDF μ b).aemeasurable
    (ae_of_all _ fun y ↦ (ENNReal.ofReal_pos.2 (laplacePDFReal_pos hb y)).ne')

/-- A Laplace distribution is absolutely continuous with respect to Lebesgue measure. -/
lemma laplaceMeasure_absolutelyContinuous_volume (μ b : ℝ) :
    laplaceMeasure μ b ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- The Radon–Nikodym derivative of `Lap(μ, b)` with respect to `Lap(μ', b)` is the ratio of the
densities, Lebesgue-almost everywhere. -/
lemma rnDeriv_laplaceMeasure_ae_eq (μ μ' : ℝ) (hb : 0 < b) :
    (laplaceMeasure μ b).rnDeriv (laplaceMeasure μ' b) =ᵐ[volume]
      fun y ↦ laplacePDF μ b y / laplacePDF μ' b y := by
  have := isProbabilityMeasure_laplaceMeasure μ' hb
  have hne (y : ℝ) : laplacePDF μ' b y ≠ 0 :=
    (ENNReal.ofReal_pos.2 (laplacePDFReal_pos hb y)).ne'
  have h₁ := Measure.rnDeriv_withDensity_left (μ := volume) (ν := laplaceMeasure μ' b)
    (measurable_laplacePDF μ b).aemeasurable (ae_of_all _ fun y ↦ ENNReal.ofReal_ne_top)
  have h₂ := Measure.rnDeriv_withDensity_right volume volume
    (measurable_laplacePDF μ' b).aemeasurable (ae_of_all _ hne)
    (ae_of_all _ fun y ↦ ENNReal.ofReal_ne_top)
  filter_upwards [(absolutelyContinuous_volume_laplaceMeasure μ' hb).ae_le h₁, h₂,
    Measure.rnDeriv_self (volume : Measure ℝ)] with y hy₁ hy₂ hy₃
  simp only [laplaceMeasure] at hy₁ hy₂ ⊢
  rw [hy₁, hy₂, hy₃, mul_one, div_eq_mul_inv]

/-! ### Proposition 6: the Rényi divergence of two Laplace distributions -/

/-- **Proposition 6** of Mironov (Rényi divergence of the Laplace distribution and its offset,
order `α > 1`), for arbitrary locations `μ, μ'` and scale `b > 0`: with `d = |μ - μ'|`,
`D_α(Lap(μ, b) ‖ Lap(μ', b))
  = (α - 1)⁻¹ log (α / (2α - 1) exp ((α - 1) d / b) + (α - 1) / (2α - 1) exp (-α d / b))`.
The paper's statement is the case `μ = 0`, `μ' = 1`, `b = λ` (`renyiDiv_laplaceMeasure_zero_one`).
-/
theorem renyiDiv_laplaceMeasure (μ μ' : ℝ) (hb : 0 < b) (hα : 1 < α) :
    renyiDiv α (laplaceMeasure μ b) (laplaceMeasure μ' b) = ENNReal.ofReal ((α - 1)⁻¹ *
      log (α / (2 * α - 1) * exp ((α - 1) * |μ - μ'| / b) +
        (α - 1) / (2 * α - 1) * exp (-α * |μ - μ'| / b))) := by
  have := isProbabilityMeasure_laplaceMeasure μ hb
  have := isProbabilityMeasure_laplaceMeasure μ' hb
  have hα' : 2 * α - 1 ≠ 0 := by linarith
  have hac : laplaceMeasure μ b ≪ laplaceMeasure μ' b :=
    (laplaceMeasure_absolutelyContinuous_volume μ b).trans
      (absolutelyContinuous_volume_laplaceMeasure μ' hb)
  have hq (y : ℝ) : (laplacePDF μ' b y).toReal = laplacePDFReal μ' b y :=
    ENNReal.toReal_ofReal (laplacePDFReal_pos hb y).le
  have hfin : ∀ᵐ y ∂(volume : Measure ℝ), laplacePDF μ' b y < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  -- the integrand `(∂P/∂Q) ^ α` in terms of the densities
  have heq : (fun y ↦ ((laplaceMeasure μ b).rnDeriv (laplaceMeasure μ' b) y).toReal ^ α)
      =ᵐ[laplaceMeasure μ' b] fun y ↦ (laplacePDFReal μ b y / laplacePDFReal μ' b y) ^ α := by
    filter_upwards [(laplaceMeasure_absolutelyContinuous_volume μ' b).ae_le
      (rnDeriv_laplaceMeasure_ae_eq μ μ' hb)] with y hy
    rw [hy, ENNReal.toReal_div, hq, laplacePDF, ENNReal.toReal_ofReal (laplacePDFReal_pos hb y).le]
  have hpt (y : ℝ) : (laplacePDF μ' b y).toReal • (laplacePDFReal μ b y / laplacePDFReal μ' b y) ^ α
      = laplacePDFReal μ b y ^ α * laplacePDFReal μ' b y ^ (1 - α) := by
    have hp := laplacePDFReal_pos (μ := μ) hb y
    have hq' := laplacePDFReal_pos (μ := μ') hb y
    rw [hq, smul_eq_mul, div_rpow hp.le hq'.le, rpow_sub hq', rpow_one]
    field_simp
  have hpos : 0 < α / (2 * α - 1) * exp ((α - 1) * |μ - μ'| / b) +
      (α - 1) / (2 * α - 1) * exp (-α * |μ - μ'| / b) := by
    have : 0 < 2 * α - 1 := by linarith
    have : 0 < α - 1 := by linarith
    positivity
  have hint : Integrable
      (fun y ↦ ((laplaceMeasure μ b).rnDeriv (laplaceMeasure μ' b) y).toReal ^ α)
      (laplaceMeasure μ' b) := by
    rw [integrable_congr heq, laplaceMeasure,
      integrable_withDensity_iff_integrable_smul' (measurable_laplacePDF μ' b) hfin]
    simp_rw [hpt]
    exact Integrable.of_integral_ne_zero
      (by rw [integral_laplacePDFReal_rpow_mul_rpow μ μ' hb hα']; exact hpos.ne')
  rw [renyiDiv_eq_log_integral_of_one_lt hα hint hac]
  simp only [measure_univ, ENNReal.toReal_one, log_one, mul_zero, add_zero, sub_zero]
  rw [integral_congr_ae heq, laplaceMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_laplacePDF μ' b) hfin]
  simp_rw [hpt]
  rw [integral_laplacePDFReal_rpow_mul_rpow μ μ' hb hα']

/-! ### The case `α = 1`: the Kullback–Leibler divergence -/

/-- The integrand `exp (-|y - μ| / b) (|y - μ'| - |y - μ|)` of the Kullback–Leibler divergence of
two Laplace distributions is integrable. -/
private lemma integrable_exp_neg_abs_mul_sub (hb : 0 < b) (μ μ' : ℝ) :
    Integrable fun y ↦ exp (-|y - μ| / b) * (|y - μ'| - |y - μ|) := by
  refine ((integrable_laplacePDFReal μ hb).const_mul (2 * b * |μ - μ'|)).mono' (by fun_prop)
    (ae_of_all _ fun y ↦ ?_)
  have h : |(|y - μ'| - |y - μ|)| ≤ |μ - μ'| :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans_eq (by ring_nf)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _), laplacePDFReal]
  calc exp (-|y - μ| / b) * |(|y - μ'| - |y - μ|)| ≤ exp (-|y - μ| / b) * |μ - μ'| := by gcongr
    _ = 2 * b * |μ - μ'| * ((2 * b)⁻¹ * exp (-|y - μ| / b)) := by field_simp

/-- The integral `∫ exp (-|y| / b) (|y - d| - |y|) dy = 2b (d + b exp (-d / b) - b)` for `d ≥ 0`
and `b > 0`, computed separately over `(-∞, 0]`, `[0, d]` and `[d, ∞)`. -/
private lemma integral_exp_neg_abs_mul_sub (hb : 0 < b) (hd : 0 ≤ d) :
    ∫ y, exp (-|y| / b) * (|y - d| - |y|) = 2 * b * (d + b * exp (-d / b) - b) := by
  set E := exp (-d / b)
  rw [integral_eq_Iic_add_intervalIntegral_add_Ioi
    (by simpa using integrable_exp_neg_abs_mul_sub hb 0 d) d]
  -- on `(-∞, 0]`
  have h₁ : ∫ y in Iic 0, exp (-|y| / b) * (|y - d| - |y|) = d * b := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun y ↦ d * exp (b⁻¹ * y)) fun y hy ↦ ?_,
      integral_const_mul, integral_exp_mul_Iic (inv_pos.2 hb), mul_zero, exp_zero]
    · field_simp
    · simp only [mem_Iic] at hy
      rw [abs_of_nonpos hy, abs_of_nonpos (by linarith), neg_neg, div_eq_inv_mul]
      ring
  -- on `[d, ∞)`
  have h₃ : ∫ y in Ioi d, exp (-|y| / b) * (|y - d| - |y|) = -(d * b * E) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y ↦ -d * exp (-b⁻¹ * y))
      fun y hy ↦ ?_, integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.2 (inv_pos.2 hb)),
      neg_div_neg_eq, show -b⁻¹ * d = -d / b by ring]
    · field_simp
      simp only [E, neg_div]
    · simp only [mem_Ioi] at hy
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), neg_div, div_eq_inv_mul]
      simp only [neg_mul]
      ring
  -- on `[0, d]`, by the fundamental theorem of calculus
  have h₂ : ∫ y in (0 : ℝ)..d, exp (-|y| / b) * (|y - d| - |y|) =
      E * (b * d + 2 * b ^ 2) - 2 * b ^ 2 + b * d := by
    have hF (y : ℝ) : HasDerivAt (fun y ↦ exp (-y / b) * (2 * b * y + 2 * b ^ 2 - b * d))
        (exp (-y / b) * (d - 2 * y)) y := by
      have h₁ : HasDerivAt (fun y ↦ -y / b) (-1 / b) y := (hasDerivAt_id y).neg.div_const b
      have h₂ : HasDerivAt (fun y ↦ 2 * b * y + 2 * b ^ 2 - b * d) (2 * b * 1) y :=
        (((hasDerivAt_id y).const_mul (2 * b)).add_const _).sub_const _
      convert h₁.exp.mul h₂ using 1
      field_simp
      ring
    rw [intervalIntegral.integral_congr (g := fun y ↦ exp (-y / b) * (d - 2 * y)) fun y hy ↦ ?_,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hF y)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
    · simp only [E, neg_zero, zero_div, exp_zero]
      ring
    · rw [uIcc_of_le hd] at hy
      simp only
      rw [abs_of_nonneg hy.1, abs_of_nonpos (by linarith [hy.2])]
      ring
  rw [h₁, h₂, h₃]
  ring

/-- **Mironov, Table II, row "Laplace mechanism", case `α = 1`** (the limit `α → 1` of
Proposition 6), for arbitrary locations `μ, μ'` and scale `b > 0`: with `d = |μ - μ'|`, the
Kullback–Leibler divergence is `D_KL(Lap(μ, b) ‖ Lap(μ', b)) = d / b + exp (-d / b) - 1`. -/
theorem klDiv_laplaceMeasure (μ μ' : ℝ) (hb : 0 < b) :
    klDiv (laplaceMeasure μ b) (laplaceMeasure μ' b) =
      ENNReal.ofReal (|μ - μ'| / b + exp (-|μ - μ'| / b) - 1) := by
  have := isProbabilityMeasure_laplaceMeasure μ hb
  have := isProbabilityMeasure_laplaceMeasure μ' hb
  have hac : laplaceMeasure μ b ≪ laplaceMeasure μ' b :=
    (laplaceMeasure_absolutelyContinuous_volume μ b).trans
      (absolutelyContinuous_volume_laplaceMeasure μ' hb)
  have hfin : ∀ᵐ y ∂(volume : Measure ℝ), laplacePDF μ b y < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  -- the log-likelihood ratio
  have hllr : llr (laplaceMeasure μ b) (laplaceMeasure μ' b) =ᵐ[laplaceMeasure μ b]
      fun y ↦ (|y - μ'| - |y - μ|) / b := by
    filter_upwards [(laplaceMeasure_absolutelyContinuous_volume μ b).ae_le
      (rnDeriv_laplaceMeasure_ae_eq μ μ' hb)] with y hy
    have h2b : (2 * b)⁻¹ ≠ 0 := by positivity
    simp only [llr_def]
    rw [hy, ENNReal.toReal_div, laplacePDF, laplacePDF,
      ENNReal.toReal_ofReal (laplacePDFReal_pos hb y).le,
      ENNReal.toReal_ofReal (laplacePDFReal_pos hb y).le, laplacePDFReal, laplacePDFReal,
      mul_div_mul_left _ _ h2b, ← exp_sub, log_exp]
    ring
  have hpt (y : ℝ) : (laplacePDF μ b y).toReal • ((|y - μ'| - |y - μ|) / b) =
      (2 * b)⁻¹ * b⁻¹ * (exp (-|y - μ| / b) * (|y - μ'| - |y - μ|)) := by
    rw [laplacePDF, ENNReal.toReal_ofReal (laplacePDFReal_pos hb y).le, laplacePDFReal,
      smul_eq_mul]
    ring
  have hint : Integrable (llr (laplaceMeasure μ b) (laplaceMeasure μ' b)) (laplaceMeasure μ b) := by
    rw [integrable_congr hllr, laplaceMeasure,
      integrable_withDensity_iff_integrable_smul' (measurable_laplacePDF μ b) hfin]
    simp_rw [hpt]
    exact (integrable_exp_neg_abs_mul_sub hb μ μ').const_mul _
  rw [klDiv_of_ac_of_integrable hac hint]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr, laplaceMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_laplacePDF μ b) hfin]
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_abs_sub_abs_sub (fun u v ↦ exp (-u / b) * (v - u)) μ μ',
    integral_exp_neg_abs_mul_sub hb (abs_nonneg _), neg_div]
  congr 1
  field_simp

/-- **Mironov, Table II, row "Laplace mechanism", case `α = 1`**, as a Rényi divergence of order
`1` (Statlib's `renyiDiv 1` is the Kullback–Leibler divergence): with `d = |μ - μ'|`,
`D_1(Lap(μ, b) ‖ Lap(μ', b)) = d / b + exp (-d / b) - 1`. -/
theorem renyiDiv_one_laplaceMeasure (μ μ' : ℝ) (hb : 0 < b) :
    renyiDiv 1 (laplaceMeasure μ b) (laplaceMeasure μ' b) =
      ENNReal.ofReal (|μ - μ'| / b + exp (-|μ - μ'| / b) - 1) := by
  have := isProbabilityMeasure_laplaceMeasure μ hb
  have := isProbabilityMeasure_laplaceMeasure μ' hb
  rw [renyiDiv_one_of_isProbabilityMeasure, klDiv_laplaceMeasure μ μ' hb]

/-- **Proposition 6** of Mironov, as stated (order `α > 1`): for `λ > 0` (here `b`),
`D_α(Λ(0, λ) ‖ Λ(1, λ))
  = (α - 1)⁻¹ log (α / (2α - 1) exp ((α - 1) / λ) + (α - 1) / (2α - 1) exp (-α / λ))`. -/
theorem renyiDiv_laplaceMeasure_zero_one (hb : 0 < b) (hα : 1 < α) :
    renyiDiv α (laplaceMeasure 0 b) (laplaceMeasure 1 b) = ENNReal.ofReal ((α - 1)⁻¹ *
      log (α / (2 * α - 1) * exp ((α - 1) / b) + (α - 1) / (2 * α - 1) * exp (-α / b))) := by
  rw [renyiDiv_laplaceMeasure 0 1 hb hα]
  norm_num

/-- **Mironov, Table II, row "Laplace mechanism", case `α = 1`**, as stated: for `λ > 0` (here
`b`), `D_1(Λ(0, λ) ‖ Λ(1, λ)) = 1 / λ + exp (-1 / λ) - 1`. -/
theorem renyiDiv_one_laplaceMeasure_zero_one (hb : 0 < b) :
    renyiDiv 1 (laplaceMeasure 0 b) (laplaceMeasure 1 b) =
      ENNReal.ofReal (1 / b + exp (-1 / b) - 1) := by
  rw [renyiDiv_one_laplaceMeasure 0 1 hb]
  norm_num

/-! ### Monotonicity in the distance between the locations -/

/-- For `α > 1`, the Hellinger integral
`α / (2α - 1) exp ((α - 1) d / b) + (α - 1) / (2α - 1) exp (-α d / b)` of two Laplace
distributions at distance `d` is positive. -/
private lemma laplaceHellinger_pos (hα : 1 < α) (d : ℝ) :
    0 < α / (2 * α - 1) * exp ((α - 1) * d / b) + (α - 1) / (2 * α - 1) * exp (-α * d / b) := by
  have : 0 < 2 * α - 1 := by linarith
  have : 0 < α - 1 := by linarith
  have : 0 < α := by linarith
  positivity

/-- For `α > 1` and `b > 0`, the Hellinger integral of two Laplace distributions is a nondecreasing
function of the distance `d ≥ 0` between their locations. -/
private lemma monotoneOn_laplaceHellinger (hb : 0 < b) (hα : 1 < α) :
    MonotoneOn (fun d ↦ α / (2 * α - 1) * exp ((α - 1) * d / b) +
      (α - 1) / (2 * α - 1) * exp (-α * d / b)) (Ici 0) := by
  have hderiv (d : ℝ) : HasDerivAt (fun d ↦ α / (2 * α - 1) * exp ((α - 1) * d / b) +
      (α - 1) / (2 * α - 1) * exp (-α * d / b))
      (α / (2 * α - 1) * (exp ((α - 1) * d / b) * ((α - 1) / b)) +
        (α - 1) / (2 * α - 1) * (exp (-α * d / b) * (-α / b))) d := by
    have h₁ : HasDerivAt (fun d ↦ (α - 1) * d / b) ((α - 1) / b) d := by
      simpa using ((hasDerivAt_id d).const_mul (α - 1)).div_const b
    have h₂ : HasDerivAt (fun d ↦ -α * d / b) (-α / b) d := by
      simpa using ((hasDerivAt_id d).const_mul (-α)).div_const b
    exact (h₁.exp.const_mul _).add (h₂.exp.const_mul _)
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun d _ ↦ (hderiv d).continuousAt.continuousWithinAt)
    (fun d _ ↦ (hderiv d).differentiableAt.differentiableWithinAt) fun d hd ↦ ?_
  rw [interior_Ici, mem_Ioi] at hd
  have h2α : 0 < 2 * α - 1 := by linarith
  have hα₁ : 0 < α - 1 := by linarith
  have hexp : exp (-α * d / b) ≤ exp ((α - 1) * d / b) :=
    exp_le_exp.2 ((div_le_div_iff_of_pos_right hb).2 (by nlinarith))
  rw [(hderiv d).deriv, show α / (2 * α - 1) * (exp ((α - 1) * d / b) * ((α - 1) / b)) +
      (α - 1) / (2 * α - 1) * (exp (-α * d / b) * (-α / b)) =
      α * (α - 1) / ((2 * α - 1) * b) * (exp ((α - 1) * d / b) - exp (-α * d / b)) by
    field_simp
    ring]
  have : 0 < α := by linarith
  exact mul_nonneg (by positivity) (sub_nonneg.2 hexp)

/-- `t ↦ t + exp (-t)` is nondecreasing on `[0, ∞)`. -/
private lemma add_exp_neg_le_add_exp_neg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    s + exp (-s) ≤ t + exp (-t) := by
  have h₁ : exp (-t) = exp (-s) * exp (-(t - s)) := by
    rw [← exp_add]
    ring_nf
  have h₂ : -(t - s) + 1 ≤ exp (-(t - s)) := add_one_le_exp _
  have h₃ : exp (-s) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have h₄ : exp (-(t - s)) ≤ 1 := exp_le_one_iff.2 (by linarith)
  rw [h₁]
  nlinarith [mul_nonneg (sub_nonneg.2 h₃) (sub_nonneg.2 h₄), exp_pos (-s)]

/-! ### The limits `α → ∞` and `α → 1` -/

/-- For `α > 1`, the closed form of Proposition 6 lies in `[d / b - log 2 / (α - 1), d / b]`. -/
private lemma laplaceRenyi_bounds (hb : 0 < b) (hd : 0 ≤ d) (hα : 1 < α) :
    d / b - log 2 * (α - 1)⁻¹ ≤ (α - 1)⁻¹ * log (α / (2 * α - 1) * exp ((α - 1) * d / b) +
        (α - 1) / (2 * α - 1) * exp (-α * d / b)) ∧
      (α - 1)⁻¹ * log (α / (2 * α - 1) * exp ((α - 1) * d / b) +
        (α - 1) / (2 * α - 1) * exp (-α * d / b)) ≤ d / b := by
  have h2α : 0 < 2 * α - 1 := by linarith
  have hα₁ : 0 < α - 1 := by linarith
  set r := α / (2 * α - 1) + (α - 1) / (2 * α - 1) * exp (-(2 * α - 1) * d / b) with hr
  have hE₁ : exp (-(2 * α - 1) * d / b) ≤ 1 :=
    exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hb.le)
  have hr₁ : 1 / 2 < r := by
    have : 1 / 2 < α / (2 * α - 1) := by
      rw [lt_div_iff₀ h2α]
      linarith
    have : 0 ≤ (α - 1) / (2 * α - 1) * exp (-(2 * α - 1) * d / b) := by positivity
    linarith
  have hr₂ : r ≤ 1 := by
    have : 0 ≤ (α - 1) / (2 * α - 1) := by positivity
    calc r ≤ α / (2 * α - 1) + (α - 1) / (2 * α - 1) * 1 := by
          rw [hr]
          gcongr
      _ = 1 := by
        rw [mul_one, ← add_div, div_eq_one_iff_eq h2α.ne']
        ring
  have hsplit : α / (2 * α - 1) * exp ((α - 1) * d / b) +
      (α - 1) / (2 * α - 1) * exp (-α * d / b) = exp ((α - 1) * d / b) * r := by
    rw [hr, show -α * d / b = (α - 1) * d / b + -(2 * α - 1) * d / b by ring, exp_add]
    ring
  rw [hsplit, log_mul (exp_pos _).ne' (by linarith), log_exp, mul_add,
    show (α - 1)⁻¹ * ((α - 1) * d / b) = d / b by field_simp]
  have hlog₁ : log r ≤ 0 := log_nonpos (by linarith) hr₂
  have hlog₂ : -log 2 ≤ log r := by
    rw [← log_inv]
    exact log_le_log (by norm_num) (by linarith)
  have hinv : 0 ≤ (α - 1)⁻¹ := inv_nonneg.2 hα₁.le
  constructor <;> nlinarith

/-- **Mironov, Section VI.B** (the limit `α → ∞` in Proposition 6): for `b > 0`,
`D_α(Lap(μ, b) ‖ Lap(μ', b)) → |μ - μ'| / b` as `α → ∞`. The paper states this as
`lim_{α → ∞} D_α(Λ(0, λ) ‖ Λ(1, λ)) = D_∞(Λ(0, λ) ‖ Λ(1, λ)) = 1 / λ`; Statlib has no divergence
of order `∞`, and the corresponding privacy statement, that the Laplace mechanism is
`Δ / b`-differentially private, is `isEpsDeltaDP_laplaceMechanism_of_le`. -/
theorem tendsto_renyiDiv_laplaceMeasure_atTop (μ μ' : ℝ) (hb : 0 < b) :
    Tendsto (fun α ↦ renyiDiv α (laplaceMeasure μ b) (laplaceMeasure μ' b)) atTop
      (𝓝 (ENNReal.ofReal (|μ - μ'| / b))) := by
  have hd := abs_nonneg (μ - μ')
  have hinv : Tendsto (fun α : ℝ ↦ (α - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  have hlow : Tendsto (fun α : ℝ ↦ |μ - μ'| / b - log 2 * (α - 1)⁻¹) atTop
      (𝓝 (|μ - μ'| / b)) := by
    simpa using (hinv.const_mul (log 2)).const_sub (|μ - μ'| / b)
  have hF := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    ((eventually_gt_atTop 1).mono fun α hα ↦ (laplaceRenyi_bounds hb hd hα).1)
    ((eventually_gt_atTop 1).mono fun α hα ↦ (laplaceRenyi_bounds hb hd hα).2)
  refine (ENNReal.tendsto_ofReal hF).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with α hα
  rw [renyiDiv_laplaceMeasure μ μ' hb hα]

/-- The closed form of Proposition 6 tends to `d / b + exp (-d / b) - 1` as `α → 1⁺`: it is the
slope at `1` of `α ↦ log (α / (2α - 1) exp ((α - 1) d / b) + (α - 1) / (2α - 1) exp (-α d / b))`,
which vanishes at `α = 1`. -/
private lemma tendsto_laplaceRenyi_one (b d : ℝ) :
    Tendsto (fun α ↦ (α - 1)⁻¹ * log (α / (2 * α - 1) * exp ((α - 1) * d / b) +
      (α - 1) / (2 * α - 1) * exp (-α * d / b))) (𝓝[>] 1) (𝓝 (d / b + exp (-d / b) - 1)) := by
  have hden : HasDerivAt (fun α : ℝ ↦ 2 * α - 1) 2 1 := by
    simpa using ((hasDerivAt_id' (1 : ℝ)).const_mul 2).sub_const 1
  have h₁ := (hasDerivAt_id' (1 : ℝ)).div hden (by norm_num)
  have h₂ := ((hasDerivAt_id' (1 : ℝ)).sub_const 1).div hden (by norm_num)
  have h₃ := ((((hasDerivAt_id' (1 : ℝ)).sub_const 1).mul_const d).div_const b).exp
  have h₄ := ((((hasDerivAt_id' (1 : ℝ)).neg).mul_const d).div_const b).exp
  have hg := ((h₁.mul h₃).add (h₂.mul h₄)).log (by norm_num)
  have hlog : HasDerivAt (fun α : ℝ ↦ log (α / (2 * α - 1) * exp ((α - 1) * d / b) +
      (α - 1) / (2 * α - 1) * exp (-α * d / b))) (d / b + exp (-d / b) - 1) 1 := by
    convert hg using 1
    norm_num
    ring
  refine ((hasDerivAt_iff_tendsto_slope.1 hlog).mono_left (nhdsGT_le_nhdsNE 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  simp only [slope_def_field]
  norm_num
  ring

/-- **Mironov, Section VI.B** (the limit `α → 1⁺` in Proposition 6, which gives the `α = 1` row of
Table II): for `b > 0`, `D_α(Lap(μ, b) ‖ Lap(μ', b)) → D_1(Lap(μ, b) ‖ Lap(μ', b))` as `α → 1⁺`,
where `D_1` is the Kullback–Leibler divergence, equal to `d / b + exp (-d / b) - 1` with
`d = |μ - μ'|` (`renyiDiv_one_laplaceMeasure`). -/
theorem tendsto_renyiDiv_laplaceMeasure_one (μ μ' : ℝ) (hb : 0 < b) :
    Tendsto (fun α ↦ renyiDiv α (laplaceMeasure μ b) (laplaceMeasure μ' b)) (𝓝[>] 1)
      (𝓝 (renyiDiv 1 (laplaceMeasure μ b) (laplaceMeasure μ' b))) := by
  rw [renyiDiv_one_laplaceMeasure μ μ' hb]
  refine (ENNReal.tendsto_ofReal (tendsto_laplaceRenyi_one b _)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α (hα : 1 < α)
  rw [renyiDiv_laplaceMeasure μ μ' hb hα]

/-! ### Nonnegativity of the budgets -/

/-- For `α > 1`, `b > 0` and `d ≥ 0`, the closed form
`(α - 1)⁻¹ log (α / (2α - 1) exp ((α - 1) d / b) + (α - 1) / (2α - 1) exp (-α d / b))` of
Proposition 6 is nonnegative: the argument of the logarithm is nondecreasing in `d` and equals `1`
at `d = 0`. -/
theorem inv_sub_one_mul_log_laplace_nonneg (hb : 0 < b) (hα : 1 < α) (hd : 0 ≤ d) :
    0 ≤ (α - 1)⁻¹ * log (α / (2 * α - 1) * exp ((α - 1) * d / b) +
      (α - 1) / (2 * α - 1) * exp (-α * d / b)) := by
  have h2α : 0 < 2 * α - 1 := by linarith
  have h₀ : α / (2 * α - 1) * exp ((α - 1) * 0 / b) +
      (α - 1) / (2 * α - 1) * exp (-α * 0 / b) = 1 := by
    simp only [mul_zero, zero_div, exp_zero, mul_one]
    rw [← add_div, div_eq_one_iff_eq h2α.ne']
    ring
  have h₁ := monotoneOn_laplaceHellinger hb hα (mem_Ici.2 le_rfl) hd hd
  dsimp only at h₁
  rw [h₀] at h₁
  exact mul_nonneg (inv_nonneg.2 (by linarith)) (log_nonneg h₁)

/-- The closed form `d / b + exp (-d / b) - 1` of the case `α = 1` is nonnegative. -/
theorem div_add_exp_neg_div_sub_one_nonneg (d b : ℝ) : 0 ≤ d / b + exp (-d / b) - 1 := by
  have h := add_one_le_exp (-d / b)
  rw [neg_div] at h ⊢
  linarith

end RenyiDP

open RenyiDP

/-! ### Corollary 2: Rényi differential privacy of the Laplace mechanism -/

section Mechanism

variable {𝒟 : Type*} [MeasurableSpace 𝒟] {f : 𝒟 → ℝ} {Adj : 𝒟 → 𝒟 → Prop} {b α Δ : ℝ}

/-- **Corollary 2** of Mironov (Rényi differential privacy of the Laplace mechanism, order
`α > 1`), for a sensitivity bound `Δ` and a noise scale `b > 0`: if `|f(x) - f(x')| ≤ Δ` for all
neighbouring `x, x'`, the Laplace mechanism `x ↦ f(x) + Lap(b)` is `(α, ε)`-RDP with
`ε = (α - 1)⁻¹ log (α / (2α - 1) exp ((α - 1) Δ / b) + (α - 1) / (2α - 1) exp (-α Δ / b))`. The
paper's statement is the case `Δ = 1`, `b = λ`. The bound is attained by neighbouring `x, x'`
with `|f(x) - f(x')| = Δ` (`RenyiDP.renyiDiv_laplaceMeasure`). For `Δ ≥ 0` the budget `ε` is
nonnegative (`RenyiDP.inv_sub_one_mul_log_laplace_nonneg`), so `Real.toNNReal` does not change
it. -/
theorem isRenyiDP_laplaceMechanism (hf : Measurable f) (hb : 0 < b) (hα : 1 < α)
    (hΔf : ∀ ⦃x x'⦄, Adj x x' → |f x - f x'| ≤ Δ) :
    IsRenyiDP (laplaceMechanism f b) Adj α (Real.toNNReal ((α - 1)⁻¹ *
      log (α / (2 * α - 1) * exp ((α - 1) * Δ / b) +
        (α - 1) / (2 * α - 1) * exp (-α * Δ / b)))) := by
  intro x x' hx
  rw [laplaceMechanism_apply hf, laplaceMechanism_apply hf, renyiDiv_laplaceMeasure _ _ hb hα]
  change _ ≤ ENNReal.ofReal _
  have hd := abs_nonneg (f x - f x')
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (by linarith)))
  exact log_le_log (laplaceHellinger_pos hα _)
    (monotoneOn_laplaceHellinger hb hα hd (hd.trans (hΔf hx)) (hΔf hx))

/-- **Corollary 2** of Mironov at order `α = 1` (Table II, row "Laplace mechanism"): if
`|f(x) - f(x')| ≤ Δ` for all neighbouring `x, x'`, the Laplace mechanism with noise scale `b > 0`
is `(1, ε)`-RDP with `ε = Δ / b + exp (-Δ / b) - 1`, i.e. its output laws on neighbouring inputs
have Kullback–Leibler divergence at most `ε`. The budget `ε` is nonnegative
(`RenyiDP.div_add_exp_neg_div_sub_one_nonneg`), so `Real.toNNReal` does not change it. -/
theorem isRenyiDP_one_laplaceMechanism (hf : Measurable f) (hb : 0 < b)
    (hΔf : ∀ ⦃x x'⦄, Adj x x' → |f x - f x'| ≤ Δ) :
    IsRenyiDP (laplaceMechanism f b) Adj 1 (Real.toNNReal (Δ / b + exp (-Δ / b) - 1)) := by
  intro x x' hx
  rw [laplaceMechanism_apply hf, laplaceMechanism_apply hf, renyiDiv_one_laplaceMeasure _ _ hb]
  change _ ≤ ENNReal.ofReal _
  refine ENNReal.ofReal_le_ofReal ?_
  have h := add_exp_neg_le_add_exp_neg (div_nonneg (abs_nonneg (f x - f x')) hb.le)
    (div_le_div_of_nonneg_right (hΔf hx) hb.le)
  rw [neg_div, neg_div]
  linarith

end Mechanism

end InformationTheory
