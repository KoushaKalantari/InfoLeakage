/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.RenyiDP.Basic
public import InfoLeakage.ZCDP.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Variance
public import Statlib.Divergence.Renyi.Order

/-!
# The discrete Gaussian for differential privacy

This file formalizes C. L. Canonne, G. Kamath and T. Steinke, *The discrete Gaussian for
differential privacy*, NeurIPS 2020 ([arXiv:2004.00010](https://arxiv.org/abs/2004.00010); result
numbers follow arXiv v6): the discrete Gaussian distribution, the theta-function inequality
(Lemma 6) on which its analysis rests, its Rényi divergences (Proposition 5), the concentrated
differential privacy of the discrete Gaussian mechanism (Theorems 4 and 14), and its
sub-Gaussian moment bounds (Lemma 16, Corollary 17).

The discrete Gaussian `N_ℤ(μ, σ²)` with location `μ ∈ ℝ` and scale `σ > 0` is the probability
distribution on `ℤ` with mass `e^{-(x - μ)² / 2σ²} / ∑_{y ∈ ℤ} e^{-(y - μ)² / 2σ²}` at `x`
(Definition 1). As in Mathlib's `gaussianReal μ v`, it is parametrized here by its location `μ`
and the variance parameter `v = σ² : ℝ≥0` of the continuous Gaussian it discretizes.

## Main definitions

* `discreteGaussianPMFReal μ v`: the mass function `x ↦ e^{-(x - μ)² / 2v} / Θ`, where `Θ` is the
  theta sum `∑_{y ∈ ℤ} e^{-(y - μ)² / 2v}` (Definition 1).
* `discreteGaussian μ v`: the discrete Gaussian `N_ℤ(μ, v)` as a measure on `ℤ`, with density
  `discreteGaussianPMFReal μ v` with respect to the counting measure.
* `discreteGaussianMechanism q hq v`: the mechanism `S ↦ N_ℤ(q S, v)`, i.e. `M(S) = q(S) + Y` with
  `Y ∼ N_ℤ(0, v)`, for a measurable query `q : 𝒟 → ℤ` (Theorem 4).
* `discreteGaussianPiMechanism q hq v`: the mechanism `S ↦ ∏_j N_ℤ(q_j(S), v j)`, i.e.
  `M(S) = q(S) + Y` with independent `Y_j ∼ N_ℤ(0, v j)`, for `q : 𝒟 → (ι → ℤ)` (Theorem 14).

## Main statements (paper result → Lean name)

* Definition 1: `discreteGaussian` is a probability measure when `v ≠ 0`
  (`isProbabilityMeasure_discreteGaussian`), with masses `discreteGaussian_real_singleton`; the
  masses sum to one (`hasSum_discreteGaussianPMFReal`), the theta sum converges
  (`DiscreteGaussian.summable_exp_neg_sq_sub`) and is positive.
* "For `μ ∈ ℤ`, the distribution is symmetric and centered at `μ`" (after Definition 1):
  `discreteGaussianPMFReal_intCast_sub` (the mass at `x` depends only on `x - μ`),
  `discreteGaussianPMFReal_neg` (symmetry), `discreteGaussian_intCast_eq_map` (`N_ℤ(μ, v)` is the
  law of `μ + Y` for `Y ∼ N_ℤ(0, v)`), and `integral_discreteGaussian_intCast` (`E[N_ℤ(μ, σ²)] = μ`,
  the integer case of Fact 18; `μ = 0`: `integral_discreteGaussian_zero`).
* Lemma 6 (`∑_{x ∈ ℤ} e^{-(x - μ)² / 2σ²} ≤ ∑_{x ∈ ℤ} e^{-x² / 2σ²}` for every real `μ`):
  `DiscreteGaussian.tsum_exp_neg_sq_sub_le`.
* Proposition 5 (`D_α(N_ℤ(μ, σ²) ‖ N_ℤ(ν, σ²)) ≤ α (μ - ν)² / 2σ²` for `μ, ν ∈ ℤ`, `α ≥ 1`):
  `renyiDiv_discreteGaussian_le`; its equality case (`α (μ - ν) ∈ ℤ`):
  `renyiDiv_discreteGaussian_eq`, and at `α = 1` (Kullback-Leibler)
  `renyiDiv_one_discreteGaussian`.
* Theorem 4 (`N_ℤ(0, Δ² / ε²)` noise on a query of sensitivity `Δ` is `(ε² / 2)`-zCDP):
  `isZCDP_discreteGaussianMechanism`; for a general scale (`(Δ² / 2σ²)`-zCDP) and any kernel
  with these laws, `isZCDP_of_discreteGaussian`.
* The conversion `(ε² / 2)`-zCDP `⇒ (ε² / 2 + ε √(2 log (1 / δ)), δ)`-DP stated after
  Definition 3, applied to Theorem 4: `isEpsDeltaDP_discreteGaussianMechanism`.
* Theorem 14 (multivariate discrete Gaussian, `∑_j (q_j(S) - q_j(S'))² / σ_j² ≤ ε²` gives
  `(ε² / 2)`-zCDP): `isZCDP_discreteGaussianPiMechanism`, and for any kernel with these laws
  `isZCDP_of_discreteGaussian_pi`; the laws are those of `q(S) + Y` with independent
  coordinates (`discreteGaussian_pi_eq_map`).
* Lemma 16 (`E[e^{t X}] ≤ e^{t² σ² / 2}` for `X ∼ N_ℤ(0, σ²)`):
  `hasSubgaussianMGF_discreteGaussian`.
* Corollary 17 (`Var[X] ≤ σ²` and `P[X ≥ λ] ≤ e^{-λ² / 2σ²}` for `λ ≥ 0`):
  `variance_discreteGaussian_le` and `discreteGaussian_real_le_le`.

## Implementation notes

* The parameter `v = σ²` is in `ℝ≥0`, and the results assume `v ≠ 0` (the paper's `σ > 0`). For
  `v = 0` the definition degenerates (division by zero gives every integer weight `1`, the theta
  sum is not summable, Lean's `tsum` is `0`, and `discreteGaussian μ 0 = 0`).
* Lemma 6 is proved, as in the paper, by the Poisson summation formula, in the form of Mathlib's
  `Complex.tsum_exp_neg_quadratic` (Jacobi's transformation formula for the theta function):
  the shifted theta sum equals a sum of positive terms twisted by unimodular phases, and the
  triangle inequality removes the phases.
* The Rényi divergence is Statlib's `renyiDiv`; on the countable alphabet `ℤ` its Hellinger
  integral is the series `∑_x P{x} ^ α Q{x} ^ (1 - α)` of the paper's Definition 3
  (`DiscreteGaussian.renyiDiv_le_ofReal_iff_tsum`). zCDP is `IsZCDP` from
  `InfoLeakage.ZCDP.Basic` (the paper's `(ε² / 2)`-concentrated DP is `IsZCDP M Adj 0 (ε² / 2)`)
  and the neighbouring relation `Adj` is arbitrary.
* Proposition 5 at `α = 1` (the Kullback-Leibler divergence): the inequality is deduced from the
  orders `α > 1` by monotonicity of `α ↦ D_α` and letting `α → 1`; the equality is computed
  from the log-likelihood ratio, which is affine, and the mean `E[N_ℤ(μ, σ²)] = μ`.
* Theorem 14 and `isZCDP_of_discreteGaussian` are stated for any kernel `M` with the stated laws
  (as `isZCDP_of_gaussianReal` in `InfoLeakage.ZCDP.Basic`); the product law
  `∏_j N_ℤ(q_j(S), σ_j²)` is `Measure.pi`.

## Not formalized

The approximate-DP bound of Theorem 7 (with Lemmas 9–11; see the notes on the paper for its
missing integer-sensitivity hypothesis), the improved conversion from
concentrated to approximate DP (Proposition 12, Corollary 13), the exact multivariate bound
(Theorem 15), Facts 18–20 (beyond the mean for integer `μ`), the sharper variance and tail
bounds of Section 3.2 (Proposition 21 onward), the discrete Laplace comparison (Section 4) and
the sampling algorithms (Section 5).

## Notes on the paper

* Proposition 5 (arXiv v6, Section 2.1, p. 7) is stated for `α ≥ 1`, but its proof begins
  "Without loss of generality, `ν = 0` and `α > 1`" and never treats `α = 1`. This is an
  expository gap only: the statement is true at `α = 1`, with equality
  (`renyiDiv_one_discreteGaussian`).
* Theorem 7 (arXiv v6, Section 2.2, p. 8; not formalized here) allows any real sensitivity
  `Δ > 0`, but its formula (4),
  `δ = P[Y > εσ² / Δ - Δ / 2] - e^ε P[Y > εσ² / Δ + Δ / 2]` with `Y ∼ N_ℤ(0, σ²)`, needs `Δ` to be
  an integer. With `Δ = 1/2`, `σ = 1`, `ε = 1/4` (e.g. a constant query) it gives
  `δ = P[Y > 1/4] - e^{1/4} P[Y > 3/4] = (1 - e^{1/4}) P[Y ≥ 1] < 0`, since `Y` is
  integer-valued, and no mechanism is `(ε, δ)`-differentially private with `δ < 0` (take the empty
  event). Likewise, its claim that (4) is "the smallest possible value of `δ`" is a worst-case
  statement over queries of sensitivity `Δ`: for a particular query it is sharp only if that query
  attains the sensitivity `Δ` on some pair of neighbours.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

namespace DiscreteGaussian

/-- The theta sum `∑_{x ∈ ℤ} e^{-(x - μ)² / 2v}` converges for `v > 0`. -/
lemma summable_exp_neg_sq_sub {v : ℝ} (hv : 0 < v) (μ : ℝ) :
    Summable fun x : ℤ ↦ rexp (-(x - μ) ^ 2 / (2 * v)) := by
  have hT : 0 < 1 / (2 * π * v) := by positivity
  refine (summable_pow_mul_jacobiTheta₂_term_bound (|μ| / (2 * π * v)) hT 0).of_nonneg_of_le
    (fun _ ↦ (exp_pos _).le) fun x ↦ ?_
  rw [pow_zero, one_mul, exp_le_exp]
  have hμ : x * μ ≤ |(x : ℝ)| * |μ| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : (0 : ℝ) < 2 * v := by positivity
  have : -π * (1 / (2 * π * v) * x ^ 2 - 2 * (|μ| / (2 * π * v)) * |(x : ℝ)|)
      = (-x ^ 2 + 2 * (|(x : ℝ)| * |μ|)) / (2 * v) := by
    field_simp
    ring
  rw [Int.cast_abs, this, div_le_div_iff_of_pos_right h2]
  nlinarith [sq_nonneg μ]

/-- The theta sum `∑_{x ∈ ℤ} e^{-(x - μ)² / 2v}` is positive for `v > 0`. -/
lemma tsum_exp_neg_sq_sub_pos {v : ℝ} (hv : 0 < v) (μ : ℝ) :
    0 < ∑' x : ℤ, rexp (-(x - μ) ^ 2 / (2 * v)) :=
  (summable_exp_neg_sq_sub hv μ).tsum_pos (fun _ ↦ (exp_pos _).le) 0 (exp_pos _)

/-- For an integer location `μ`, the theta sum does not depend on `μ`. -/
lemma tsum_exp_neg_sq_sub_intCast (v : ℝ) (μ : ℤ) :
    ∑' x : ℤ, rexp (-(x - μ) ^ 2 / (2 * v)) = ∑' x : ℤ, rexp (-x ^ 2 / (2 * v)) := by
  rw [← (Equiv.addRight μ).tsum_eq]
  simp

open Complex in
/-- **Lemma 6** of Canonne–Kamath–Steinke: for `v = σ² > 0` and every real `μ`,
`∑_{x ∈ ℤ} e^{-(x - μ)² / 2σ²} ≤ ∑_{x ∈ ℤ} e^{-x² / 2σ²}`; the theta sum is largest at integer
locations. The proof is the paper's, by Poisson summation (`Complex.tsum_exp_neg_quadratic`). -/
theorem tsum_exp_neg_sq_sub_le {v : ℝ} (hv : 0 < v) (μ : ℝ) :
    ∑' x : ℤ, rexp (-(x - μ) ^ 2 / (2 * v)) ≤ ∑' x : ℤ, rexp (-x ^ 2 / (2 * v)) := by
  set a : ℝ := 1 / (2 * π * v) with ha_def
  have ha : 0 < a := by positivity
  set b : ℝ := a * μ with hb_def
  have hP := Complex.tsum_exp_neg_quadratic (a := (a : ℂ)) (by simpa using ha) (b : ℂ)
  -- the left-hand side of the transformation formula is the shifted theta sum
  have hL : ∀ n : ℤ, cexp (-π * a * n ^ 2 + 2 * π * b * n)
      = ((rexp (μ ^ 2 / (2 * v)) * rexp (-(n - μ) ^ 2 / (2 * v)) : ℝ) : ℂ) := by
    intro n
    rw [← Real.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    simp only [ha_def, hb_def]
    push_cast
    field_simp
    ring
  simp_rw [hL] at hP
  rw [← Complex.ofReal_tsum, tsum_mul_left] at hP
  -- the terms on the right-hand side are positive reals times unimodular phases
  have hN : ∀ n : ℤ, ‖cexp (-π / a * (n + I * b) ^ 2)‖
      = rexp (μ ^ 2 / (2 * v)) * rexp (-π / a * (n : ℝ) ^ 2) := by
    intro n
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have : (-π / (a : ℂ) * (n + I * b) ^ 2)
        = ((-π / a * (n ^ 2 - b ^ 2) : ℝ) : ℂ) + ((-π / a * (2 * n * b) : ℝ) : ℂ) * I := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
    simp only [hb_def, ha_def]
    field_simp
    ring
  have hS : Summable fun n : ℤ ↦ rexp (-π / a * (n : ℝ) ^ 2) := by
    refine (summable_pow_mul_jacobiTheta₂_term_bound 0 (one_div_pos.2 ha) 0).congr fun n ↦ ?_
    simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero]
    ring_nf
  have hSN : Summable fun n : ℤ ↦ ‖cexp (-π / a * (n + I * b) ^ 2)‖ := by
    simp_rw [hN]
    exact hS.mul_left _
  have hle := congrArg norm hP
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul] at hle
  have h1 := norm_tsum_le_tsum_norm hSN
  simp_rw [hN, tsum_mul_left] at h1
  have hsq : ‖(1 : ℂ) / (a : ℂ) ^ (1 / 2 : ℂ)‖ = 1 / a ^ (1 / 2 : ℝ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one, ← Complex.ofReal_div,
      ← Complex.ofReal_cpow ha.le, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hθ' : ∑' n : ℤ, rexp (-(n : ℝ) ^ 2 / (2 * v)) = ∑' n : ℤ, rexp (-π * a * (n : ℝ) ^ 2) :=
    tsum_congr fun n ↦ by
      congr 1
      simp only [ha_def]
      field_simp
  refine le_of_mul_le_mul_left ?_ (exp_pos (μ ^ 2 / (2 * v)))
  rw [hle, hsq, hθ', Real.tsum_exp_neg_mul_int_sq ha]
  calc 1 / a ^ (1 / 2 : ℝ) * ‖∑' n : ℤ, cexp (-π / a * (n + I * b) ^ 2)‖
      ≤ 1 / a ^ (1 / 2 : ℝ) * (rexp (μ ^ 2 / (2 * v)) * ∑' n : ℤ, rexp (-π / a * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

end DiscreteGaussian

open DiscreteGaussian

/-! ### The mass function -/

/-- The mass function of the discrete Gaussian `N_ℤ(μ, v)` (Definition 1 of
Canonne–Kamath–Steinke, with `v = σ²`): `x ↦ e^{-(x - μ)² / 2v} / ∑_{y ∈ ℤ} e^{-(y - μ)² / 2v}`.
It sums to one for `v ≠ 0` (`hasSum_discreteGaussianPMFReal`). -/
noncomputable def discreteGaussianPMFReal (μ : ℝ) (v : ℝ≥0) (x : ℤ) : ℝ :=
  rexp (-(x - μ) ^ 2 / (2 * v)) / ∑' y : ℤ, rexp (-(y - μ) ^ 2 / (2 * v))

variable {μ : ℝ} {v : ℝ≥0}

lemma discreteGaussianPMFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℤ) :
    0 ≤ discreteGaussianPMFReal μ v x :=
  div_nonneg (exp_pos _).le (tsum_nonneg fun _ ↦ (exp_pos _).le)

lemma discreteGaussianPMFReal_pos (hv : v ≠ 0) (μ : ℝ) (x : ℤ) :
    0 < discreteGaussianPMFReal μ v x :=
  div_pos (exp_pos _) (tsum_exp_neg_sq_sub_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)) μ)

/-- **The discrete Gaussian masses sum to one** (for `v ≠ 0`). -/
lemma hasSum_discreteGaussianPMFReal (hv : v ≠ 0) (μ : ℝ) :
    HasSum (discreteGaussianPMFReal μ v) 1 := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have h := ((summable_exp_neg_sq_sub hv' μ).div_const
    (∑' y : ℤ, rexp (-(y - μ) ^ 2 / (2 * v)))).hasSum
  rwa [tsum_div_const, div_self (tsum_exp_neg_sq_sub_pos hv' μ).ne'] at h

lemma tsum_discreteGaussianPMFReal (hv : v ≠ 0) (μ : ℝ) :
    ∑' x, discreteGaussianPMFReal μ v x = 1 :=
  (hasSum_discreteGaussianPMFReal hv μ).tsum_eq

/-- For an integer location `μ`, the normalizing constant is the theta sum
`∑_{y ∈ ℤ} e^{-y² / 2v}`, which does not depend on `μ`. -/
lemma discreteGaussianPMFReal_intCast (μ : ℤ) (v : ℝ≥0) (x : ℤ) :
    discreteGaussianPMFReal μ v x
      = rexp (-(x - μ) ^ 2 / (2 * v)) / ∑' y : ℤ, rexp (-y ^ 2 / (2 * v)) := by
  rw [discreteGaussianPMFReal, tsum_exp_neg_sq_sub_intCast]

/-- For an integer location `μ`, the mass of `N_ℤ(μ, v)` at `x` is that of `N_ℤ(0, v)` at
`x - μ`. -/
lemma discreteGaussianPMFReal_intCast_sub (μ : ℤ) (v : ℝ≥0) (x : ℤ) :
    discreteGaussianPMFReal μ v x = discreteGaussianPMFReal 0 v (x - μ) := by
  have h := discreteGaussianPMFReal_intCast 0 v (x - μ)
  rw [Int.cast_zero] at h
  rw [discreteGaussianPMFReal_intCast, h]
  push_cast
  ring_nf

/-- **Symmetry**: the mass of `N_ℤ(-μ, v)` at `-x` is that of `N_ℤ(μ, v)` at `x`; in particular
`N_ℤ(0, v)` is symmetric. -/
lemma discreteGaussianPMFReal_neg (μ : ℝ) (v : ℝ≥0) (x : ℤ) :
    discreteGaussianPMFReal (-μ) v (-x) = discreteGaussianPMFReal μ v x := by
  have h : ∑' y : ℤ, rexp (-(y - -μ) ^ 2 / (2 * v)) = ∑' y : ℤ, rexp (-(y - μ) ^ 2 / (2 * v)) := by
    rw [← (Equiv.neg ℤ).tsum_eq fun y : ℤ ↦ rexp (-(y - -μ) ^ 2 / (2 * v))]
    refine tsum_congr fun y ↦ ?_
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring_nf
  simp only [discreteGaussianPMFReal, h, Int.cast_neg]
  ring_nf

/-! ### The discrete Gaussian distribution -/

/-- **The discrete Gaussian distribution** `N_ℤ(μ, v)` on `ℤ` (Definition 1 of
Canonne–Kamath–Steinke, with `v = σ²`): the measure with density `discreteGaussianPMFReal μ v`
with respect to the counting measure. It is a probability measure for `v ≠ 0`
(`isProbabilityMeasure_discreteGaussian`). -/
noncomputable def discreteGaussian (μ : ℝ) (v : ℝ≥0) : Measure ℤ :=
  Measure.count.withDensity fun x ↦ ENNReal.ofReal (discreteGaussianPMFReal μ v x)

lemma discreteGaussian_singleton (μ : ℝ) (v : ℝ≥0) (x : ℤ) :
    discreteGaussian μ v {x} = ENNReal.ofReal (discreteGaussianPMFReal μ v x) := by
  rw [discreteGaussian, withDensity_apply _ (MeasurableSet.singleton x),
    Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac]

lemma discreteGaussian_real_singleton (μ : ℝ) (v : ℝ≥0) (x : ℤ) :
    (discreteGaussian μ v).real {x} = discreteGaussianPMFReal μ v x := by
  rw [measureReal_def, discreteGaussian_singleton,
    ENNReal.toReal_ofReal (discreteGaussianPMFReal_nonneg μ v x)]

/-- For `v ≠ 0`, every integer has positive mass under `N_ℤ(μ, v)`. -/
lemma discreteGaussian_singleton_ne_zero (hv : v ≠ 0) (μ : ℝ) (x : ℤ) :
    discreteGaussian μ v {x} ≠ 0 := by
  rw [discreteGaussian_singleton]
  exact (ENNReal.ofReal_pos.2 (discreteGaussianPMFReal_pos hv μ x)).ne'

/-- The discrete Gaussian `N_ℤ(μ, v)` is a probability measure for `v ≠ 0`. -/
lemma isProbabilityMeasure_discreteGaussian (μ : ℝ) (hv : v ≠ 0) :
    IsProbabilityMeasure (discreteGaussian μ v) := by
  constructor
  rw [discreteGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (discreteGaussianPMFReal_nonneg μ v)
    (hasSum_discreteGaussianPMFReal hv μ).summable, tsum_discreteGaussianPMFReal hv,
    ENNReal.ofReal_one]

/-- The degenerate case `v = 0`: the theta sum `∑_{y ∈ ℤ} e^0` diverges, and the definition
gives the zero measure. -/
lemma discreteGaussian_zero_right (μ : ℝ) : discreteGaussian μ 0 = 0 := by
  have h : ∑' _ : ℤ, (1 : ℝ) = 0 :=
    tsum_eq_zero_of_not_summable ((summable_const_iff (1 : ℝ)).not.2 one_ne_zero)
  simp [discreteGaussian, discreteGaussianPMFReal, h]

instance (μ : ℝ) (v : ℝ≥0) : IsZeroOrProbabilityMeasure (discreteGaussian μ v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [discreteGaussian_zero_right]
    infer_instance
  · have := isProbabilityMeasure_discreteGaussian μ hv
    infer_instance

/-- For an integer location `μ`, `N_ℤ(μ, v)` is the law of `μ + Y` for `Y ∼ N_ℤ(0, v)` (the
paper's mechanism `M(x) = q(x) + Y`). -/
theorem discreteGaussian_intCast_eq_map (μ : ℤ) (v : ℝ≥0) :
    discreteGaussian μ v = (discreteGaussian 0 v).map (· + μ) := by
  refine Measure.ext_iff_singleton.2 fun x ↦ ?_
  have hpre : (· + μ) ⁻¹' {x} = {x - μ} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton x), hpre,
    discreteGaussian_singleton, discreteGaussian_singleton,
    discreteGaussianPMFReal_intCast_sub]

/-! ### Moments -/

namespace DiscreteGaussian

/-- A real function on `ℤ` is integrable against `N_ℤ(μ, v)` when `∑_x ‖f x‖ p(x)` converges. -/
lemma integrable_of_summable {f : ℤ → ℝ}
    (hf : Summable fun x ↦ ‖f x‖ * discreteGaussianPMFReal μ v x) :
    Integrable f (discreteGaussian μ v) := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_countable']
  simp_rw [discreteGaussian_singleton, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun _ ↦ mul_nonneg (norm_nonneg _) (discreteGaussianPMFReal_nonneg _ _ _)) hf]
  exact ENNReal.ofReal_lt_top

/-- An expectation under `N_ℤ(μ, v)` is the series `∑_x p(x) f(x)`. -/
lemma integral_eq_tsum {f : ℤ → ℝ} (hf : Integrable f (discreteGaussian μ v)) :
    ∫ x, f x ∂discreteGaussian μ v = ∑' x, discreteGaussianPMFReal μ v x * f x := by
  simp_rw [integral_countable hf, discreteGaussian_real_singleton, smul_eq_mul]

/-- Completing the square in the proof of Lemma 16:
`p_0(x) e^{t x} = e^{v t² / 2} e^{-(x - t v)² / 2v} / Θ`, with `Θ = ∑_{y ∈ ℤ} e^{-y² / 2v}`. -/
lemma pmf_mul_exp (hv : v ≠ 0) (t : ℝ) (x : ℤ) :
    discreteGaussianPMFReal 0 v x * rexp (t * x)
      = rexp (v * t ^ 2 / 2) *
        (rexp (-(x - t * v) ^ 2 / (2 * v)) / ∑' y : ℤ, rexp (-y ^ 2 / (2 * v))) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  simp only [discreteGaussianPMFReal, sub_zero]
  rw [div_mul_eq_mul_div, ← Real.exp_add, mul_div_assoc', ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- `x ↦ p_0(x) e^{t x}` is summable. -/
lemma summable_pmf_mul_exp (hv : v ≠ 0) (t : ℝ) :
    Summable fun x : ℤ ↦ discreteGaussianPMFReal 0 v x * rexp (t * x) := by
  simp_rw [pmf_mul_exp hv]
  exact ((summable_exp_neg_sq_sub (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)) _).div_const
    _).mul_left _

/-- `1 + y² / 2 ≤ cosh y`: the first two terms of the series of `cosh`. -/
lemma one_add_sq_div_two_le_cosh (y : ℝ) : 1 + y ^ 2 / 2 ≤ Real.cosh y := by
  have h := sum_le_hasSum (Finset.range 2) (fun n _ ↦ by rw [pow_mul]; positivity)
    (Real.hasSum_cosh y)
  simpa [Finset.sum_range_succ] using h

end DiscreteGaussian

/-- **Lemma 16** of Canonne–Kamath–Steinke: for `v = σ² ≠ 0` and `X ∼ N_ℤ(0, σ²)`,
`E[e^{t X}] ≤ e^{t² σ² / 2}` for every `t ∈ ℝ`, i.e. `X` is sub-Gaussian with variance proxy
`σ²` in the sense of Mathlib's `HasSubgaussianMGF` (which also records that `e^{t X}` is
integrable). -/
theorem hasSubgaussianMGF_discreteGaussian (hv : v ≠ 0) :
    ProbabilityTheory.HasSubgaussianMGF (fun x : ℤ ↦ (x : ℝ)) v (discreteGaussian 0 v) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hint : ∀ t : ℝ, Integrable (fun x : ℤ ↦ rexp (t * x)) (discreteGaussian 0 v) := fun t ↦
    integrable_of_summable <| by
      simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_comm (rexp _)]
        using summable_pmf_mul_exp hv t
  refine ⟨hint, fun t ↦ ?_⟩
  have hT := tsum_exp_neg_sq_sub_pos hv' 0
  simp only [sub_zero] at hT
  rw [ProbabilityTheory.mgf, integral_eq_tsum (hint t)]
  simp_rw [pmf_mul_exp hv]
  rw [tsum_mul_left, tsum_div_const]
  refine mul_le_of_le_one_right (exp_pos _).le ?_
  exact div_le_one_of_le₀ (tsum_exp_neg_sq_sub_le hv' _) hT.le

/-- **Corollary 17** of Canonne–Kamath–Steinke (tail bound): for `v = σ² ≠ 0`,
`P_{X ∼ N_ℤ(0, σ²)}[X ≥ a] ≤ e^{-a² / 2σ²}` for every `a ≥ 0`. -/
theorem discreteGaussian_real_le_le (hv : v ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    (discreteGaussian 0 v).real {x : ℤ | a ≤ x} ≤ rexp (-a ^ 2 / (2 * v)) :=
  (hasSubgaussianMGF_discreteGaussian hv).measure_ge_le ha

/-- `X ∼ N_ℤ(0, σ²)` is integrable and has mean zero, by symmetry (the case `μ = 0` of Fact 18
of Canonne–Kamath–Steinke). -/
theorem integral_discreteGaussian_zero (hv : v ≠ 0) :
    Integrable (fun x : ℤ ↦ (x : ℝ)) (discreteGaussian 0 v) ∧
      ∫ x, (x : ℝ) ∂discreteGaussian 0 v = 0 := by
  refine ⟨(hasSubgaussianMGF_discreteGaussian hv).integrable, ?_⟩
  rw [integral_eq_tsum (hasSubgaussianMGF_discreteGaussian hv).integrable]
  have h := (Equiv.neg ℤ).tsum_eq fun x ↦ discreteGaussianPMFReal 0 v x * x
  have hneg : ∀ x : ℤ, discreteGaussianPMFReal 0 v (-x) * ((-x : ℤ) : ℝ)
      = -(discreteGaussianPMFReal 0 v x * x) := fun x ↦ by
    have := discreteGaussianPMFReal_neg 0 v x
    rw [neg_zero] at this
    rw [this, Int.cast_neg, mul_neg]
  simp only [Equiv.neg_apply, hneg, tsum_neg] at h
  linarith

/-- For an integer location `μ`, `X ∼ N_ℤ(μ, σ²)` is integrable with mean `E[X] = μ` (stated
after Definition 1 and at the start of Section 3.1 of Canonne–Kamath–Steinke; the integer case of
Fact 18). -/
theorem integral_discreteGaussian_intCast (hv : v ≠ 0) (μ : ℤ) :
    Integrable (fun x : ℤ ↦ (x : ℝ)) (discreteGaussian μ v) ∧
      ∫ x, (x : ℝ) ∂discreteGaussian μ v = μ := by
  have := isProbabilityMeasure_discreteGaussian 0 hv
  obtain ⟨hint, hzero⟩ := integral_discreteGaussian_zero hv
  have hcomp : (fun x : ℤ ↦ ((x : ℤ) : ℝ)) ∘ (· + μ) = fun x : ℤ ↦ (x : ℝ) + μ := by
    ext x
    simp
  rw [discreteGaussian_intCast_eq_map]
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable, hcomp]
    exact hint.add (integrable_const _)
  · rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp only [Int.cast_add]
    rw [integral_add hint (integrable_const _), hzero, integral_const, probReal_univ, one_smul,
      zero_add]

/-- **Corollary 17** of Canonne–Kamath–Steinke (variance bound): for `v = σ² ≠ 0`,
`X ∼ N_ℤ(0, σ²)` is square-integrable and `Var[X] ≤ σ²` (the first conjunct makes Mathlib's
`variance` the genuine variance rather than its junk value `0` for variables outside `L²`). As in
the paper, it follows from Lemma 16: for `t > 0`,
`1 + t² E[X²] / 2 ≤ E[cosh (t X)] ≤ e^{t² σ² / 2}`, and `t → 0`. -/
theorem variance_discreteGaussian_le (hv : v ≠ 0) :
    MemLp (fun x : ℤ ↦ (x : ℝ)) 2 (discreteGaussian 0 v) ∧
      ProbabilityTheory.variance (fun x : ℤ ↦ (x : ℝ)) (discreteGaussian 0 v) ≤ v := by
  have := isProbabilityMeasure_discreteGaussian 0 hv
  have hX := hasSubgaussianMGF_discreteGaussian hv
  refine ⟨hX.memLp 2, ?_⟩
  have hsq : Integrable (fun x : ℤ ↦ (x : ℝ) ^ 2) (discreteGaussian 0 v) :=
    (hX.memLp 2).integrable_sq
  refine (ProbabilityTheory.variance_le_expectation_sq
    (measurable_of_countable _).aestronglyMeasurable).trans ?_
  change ∫ x, (x : ℝ) ^ 2 ∂discreteGaussian 0 v ≤ v
  set E := ∫ x, (x : ℝ) ^ 2 ∂discreteGaussian 0 v
  have key : ∀ t : ℝ, 0 < t → E ≤ v * rexp (v * t ^ 2 / 2) := fun t ht ↦ by
    have h1 : ∫ x, (1 + t ^ 2 / 2 * (x : ℝ) ^ 2) ∂discreteGaussian 0 v
        ≤ ∫ x, (rexp (t * x) + rexp (-t * x)) / 2 ∂discreteGaussian 0 v := by
      refine integral_mono ((integrable_const 1).add (hsq.const_mul _))
        (((hX.integrable_exp_mul t).add (hX.integrable_exp_mul (-t))).div_const 2) fun x ↦ ?_
      have := DiscreteGaussian.one_add_sq_div_two_le_cosh (t * x)
      rw [Real.cosh_eq] at this
      convert this using 2 <;> ring_nf
    rw [integral_add (integrable_const 1) (hsq.const_mul _), integral_const_mul,
      integral_div, integral_add (hX.integrable_exp_mul t) (hX.integrable_exp_mul (-t))] at h1
    have hm := hX.mgf_le t
    have hm' := hX.mgf_le (-t)
    simp only [ProbabilityTheory.mgf, neg_sq] at hm hm'
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    have h2 : rexp (v * t ^ 2 / 2) ≤ 1 + v * t ^ 2 / 2 * rexp (v * t ^ 2 / 2) := by
      have := Real.add_one_le_exp (-(v * t ^ 2 / 2))
      rw [Real.exp_neg] at this
      have hpos := exp_pos (v * t ^ 2 / 2)
      field_simp at this
      nlinarith
    have ht2 : 0 < t ^ 2 / 2 := by positivity
    refine le_of_mul_le_mul_left ?_ ht2
    nlinarith
  have hlim : Filter.Tendsto (fun t : ℝ ↦ (v : ℝ) * rexp (v * t ^ 2 / 2)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((v : ℝ) * rexp (v * 0 ^ 2 / 2))) :=
    ((by fun_prop : Continuous fun t : ℝ ↦ (v : ℝ) * rexp (v * t ^ 2 / 2)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    exp_zero, mul_one] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht ↦ key t ht)


open ProbabilityTheory Filter
open scoped Topology

namespace DiscreteGaussian

/-! ### The Rényi divergence on a countable alphabet -/

section Countable

variable {Y : Type*} [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y]
  {P Q : Measure Y} {α c : ℝ}

/-- On a countable alphabet, the Hellinger integral `∫ (∂P/∂Q) ^ α ∂Q` of `P ≪ Q` is the series
`∑_y P{y} ^ α Q{y} ^ (1 - α)` of Definition 3 of Canonne–Kamath–Steinke. -/
lemma lintegral_rnDeriv_rpow_eq_tsum [IsFiniteMeasure Q] (hac : P ≪ Q)
    (hα : 0 < α) : ∫⁻ y, (∂P/∂Q) y ^ α ∂Q = ∑' y, P {y} ^ α * Q {y} ^ (1 - α) := by
  rw [lintegral_countable']
  refine tsum_congr fun y ↦ ?_
  rcases eq_or_ne (Q {y}) 0 with hQ | hQ
  · simp [hQ, hac hQ, ENNReal.zero_rpow_of_pos hα]
  have hy : P {y} = (∂P/∂Q) y * Q {y} := by
    rw [← Measure.setLIntegral_rnDeriv hac, lintegral_singleton]
  rw [hy, ENNReal.mul_rpow_of_nonneg _ _ hα.le, mul_assoc,
    ← ENNReal.rpow_add _ _ hQ (measure_ne_top _ _), add_sub_cancel, ENNReal.rpow_one]

/-- On a countable alphabet, for probability measures `P ≪ Q` and `α > 1`, `D_α(P ‖ Q) ≤ c` iff
`∑_y P{y} ^ α Q{y} ^ (1 - α) ≤ e^{(α - 1) c}`. -/
lemma renyiDiv_le_ofReal_iff_tsum [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hac : P ≪ Q)
    (hα : 1 < α) (hc : 0 ≤ c) :
    renyiDiv α P Q ≤ ENNReal.ofReal c ↔
      ∑' y, P {y} ^ α * Q {y} ^ (1 - α) ≤ ENNReal.ofReal (exp ((α - 1) * c)) := by
  rw [RenyiDP.renyiDiv_le_ofReal_iff_lintegral hα hc,
    lintegral_rnDeriv_rpow_eq_tsum hac (by linarith)]
  exact and_iff_right hac

omit [Countable Y] [MeasurableSingletonClass Y] in
/-- A measure is absolutely continuous with respect to a measure that charges every point. -/
lemma absolutelyContinuous_of_forall_ne_zero (h : ∀ y, Q {y} ≠ 0) : P ≪ Q := fun s hs ↦ by
  have : s = ∅ := Set.eq_empty_of_forall_notMem fun y hy ↦
    h y (measure_mono_null (Set.singleton_subset_iff.2 hy) hs)
  simp [this]

/-- On a countable alphabet, the density `∂P/∂Q` at a point charged by `Q` is `P{y} / Q{y}`. -/
lemma toReal_rnDeriv_eq [IsFiniteMeasure Q] (hac : P ≪ Q) {y : Y}
    (hQ : Q {y} ≠ 0) : ((∂P/∂Q) y).toReal = P.real {y} / Q.real {y} := by
  have hy : P {y} = (∂P/∂Q) y * Q {y} := by
    rw [← Measure.setLIntegral_rnDeriv hac, lintegral_singleton]
  have hQr : 0 < Q.real {y} := ENNReal.toReal_pos hQ (measure_ne_top _ _)
  rw [measureReal_def P, hy, ENNReal.toReal_mul, ← measureReal_def, mul_div_assoc,
    div_self hQr.ne', mul_one]

end Countable

/-! ### The Hellinger series of two discrete Gaussians -/


/-- Completing the square: for integer locations `μ, ν` and `m = α μ + (1 - α) ν`,
`p_μ(x) ^ α p_ν(x) ^ (1 - α) = e^{α (α - 1) (μ - ν)² / 2v} e^{-(x - m)² / 2v} / Θ`, where `Θ` is the
theta sum `∑_{y ∈ ℤ} e^{-y² / 2v}`. -/
lemma pmf_rpow_mul_pmf_rpow (hv : v ≠ 0) (μ ν : ℤ) (α : ℝ) (x : ℤ) :
    discreteGaussianPMFReal μ v x ^ α * discreteGaussianPMFReal ν v x ^ (1 - α)
      = rexp (α * (α - 1) * (μ - ν) ^ 2 / (2 * v)) *
        (rexp (-(x - (α * μ + (1 - α) * ν)) ^ 2 / (2 * v)) /
          ∑' y : ℤ, rexp (-y ^ 2 / (2 * v))) := by
  have hT := tsum_exp_neg_sq_sub_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)) 0
  simp only [sub_zero] at hT
  rw [discreteGaussianPMFReal_intCast, discreteGaussianPMFReal_intCast,
    Real.div_rpow (exp_pos _).le hT.le, Real.div_rpow (exp_pos _).le hT.le, ← Real.exp_mul,
    ← Real.exp_mul, div_mul_div_comm, ← Real.exp_add, ← Real.rpow_add hT, add_sub_cancel,
    Real.rpow_one, mul_div_assoc', ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The Hellinger series of `N_ℤ(μ, v)` and `N_ℤ(ν, v)` for integer locations `μ, ν`:
`∑_x p_μ(x) ^ α p_ν(x) ^ (1 - α) = e^{α (α - 1) (μ - ν)² / 2v} Θ(m) / Θ(0)`, where
`Θ(m) = ∑_{x ∈ ℤ} e^{-(x - m)² / 2v}` and `m = α μ + (1 - α) ν`. -/
lemma tsum_rpow_mul_rpow (hv : v ≠ 0) (μ ν : ℤ) {α : ℝ} (hα : 1 < α) :
    ∑' x, discreteGaussian μ v {x} ^ α * discreteGaussian ν v {x} ^ (1 - α)
      = ENNReal.ofReal (rexp (α * (α - 1) * (μ - ν) ^ 2 / (2 * v)) *
        ((∑' x : ℤ, rexp (-(x - (α * μ + (1 - α) * ν)) ^ 2 / (2 * v))) /
          ∑' y : ℤ, rexp (-y ^ 2 / (2 * v)))) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hterm : ∀ x : ℤ, discreteGaussian μ v {x} ^ α * discreteGaussian ν v {x} ^ (1 - α)
      = ENNReal.ofReal
        (discreteGaussianPMFReal μ v x ^ α * discreteGaussianPMFReal ν v x ^ (1 - α)) := by
    intro x
    rw [discreteGaussian_singleton, discreteGaussian_singleton,
      ENNReal.ofReal_rpow_of_nonneg (discreteGaussianPMFReal_nonneg _ _ _) (by linarith),
      ENNReal.ofReal_rpow_of_pos (discreteGaussianPMFReal_pos hv _ _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (discreteGaussianPMFReal_nonneg _ _ _) _)]
  simp_rw [hterm, pmf_rpow_mul_pmf_rpow hv]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
    (((summable_exp_neg_sq_sub hv' _).div_const _).mul_left _), tsum_mul_left, tsum_div_const]

/-- **Proposition 5** of Canonne–Kamath–Steinke for orders `α > 1`. -/
private lemma renyiDiv_le_of_one_lt (hv : v ≠ 0) (μ ν : ℤ) {α : ℝ} (hα : 1 < α) :
    renyiDiv α (discreteGaussian μ v) (discreteGaussian ν v)
      ≤ ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v) * α) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have := isProbabilityMeasure_discreteGaussian (μ : ℝ) hv
  have := isProbabilityMeasure_discreteGaussian (ν : ℝ) hv
  have hT := tsum_exp_neg_sq_sub_pos hv' 0
  simp only [sub_zero] at hT
  rw [renyiDiv_le_ofReal_iff_tsum
    (absolutelyContinuous_of_forall_ne_zero (discreteGaussian_singleton_ne_zero hv ν)) hα
    (by positivity), tsum_rpow_mul_rpow hv μ ν hα]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show (α - 1) * ((μ - ν) ^ 2 / (2 * v) * α) = α * (α - 1) * (μ - ν) ^ 2 / (2 * v) by ring]
  refine mul_le_of_le_one_right (exp_pos _).le ?_
  exact div_le_one_of_le₀ (tsum_exp_neg_sq_sub_le hv' _) hT.le

end DiscreteGaussian


/-- **Proposition 5** of Canonne–Kamath–Steinke (inequality (2)): for `v = σ² ≠ 0`, integer
locations `μ, ν` and every order `α ≥ 1`,
`D_α(N_ℤ(μ, σ²) ‖ N_ℤ(ν, σ²)) ≤ (μ - ν)² / (2σ²) · α`. At `α = 1` the divergence is the
Kullback-Leibler divergence (Statlib's `renyiDiv 1`). -/
theorem renyiDiv_discreteGaussian_le (hv : v ≠ 0) (μ ν : ℤ) {α : ℝ} (hα : 1 ≤ α) :
    renyiDiv α (discreteGaussian μ v) (discreteGaussian ν v)
      ≤ ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v) * α) := by
  rcases hα.eq_or_lt with rfl | hα
  · -- order `1`: monotonicity in the order, and the bound at orders `a > 1`, as `a → 1`
    have := isProbabilityMeasure_discreteGaussian (μ : ℝ) hv
    have := isProbabilityMeasure_discreteGaussian (ν : ℝ) hv
    have hlim : Tendsto (fun a : ℝ ↦ ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v) * a)) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v) * 1))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)).tendsto 1).mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (renyiDiv_le_renyiDiv_of_le zero_le_one (le_of_lt ha)).trans
      (renyiDiv_le_of_one_lt hv μ ν ha)
  · exact renyiDiv_le_of_one_lt hv μ ν hα

/-- The equality case of Proposition 5 for orders `α > 1`. -/
private theorem renyiDiv_discreteGaussian_eq_of_one_lt (hv : v ≠ 0) (μ ν : ℤ) {α : ℝ} (hα : 1 < α)
    (hint : ∃ k : ℤ, α * (μ - ν) = k) :
    renyiDiv α (discreteGaussian μ v) (discreteGaussian ν v)
      = ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v) * α) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have := isProbabilityMeasure_discreteGaussian (μ : ℝ) hv
  have := isProbabilityMeasure_discreteGaussian (ν : ℝ) hv
  obtain ⟨k, hk⟩ := hint
  set c : ℝ := (μ - ν) ^ 2 / (2 * v) * α with hc_def
  have hc : 0 ≤ c := by positivity
  -- the Hellinger series equals `e^{(α - 1) c}` since `α μ + (1 - α) ν = ν + k` is an integer
  have hm : α * μ + (1 - α) * ν = ((ν + k : ℤ) : ℝ) := by push_cast; linarith
  have hH : ∑' x, discreteGaussian μ v {x} ^ α * discreteGaussian ν v {x} ^ (1 - α)
      = ENNReal.ofReal (rexp ((α - 1) * c)) := by
    have hT := tsum_exp_neg_sq_sub_pos hv' 0
    simp only [sub_zero] at hT
    rw [tsum_rpow_mul_rpow hv μ ν hα, hm, tsum_exp_neg_sq_sub_intCast, div_self hT.ne', mul_one,
      hc_def]
    congr 2
    ring
  have hac := absolutelyContinuous_of_forall_ne_zero (P := discreteGaussian μ v)
    (discreteGaussian_singleton_ne_zero hv ν)
  refine le_antisymm (renyiDiv_discreteGaussian_le hv μ ν hα.le) ?_
  by_contra! hlt
  have hR : renyiDiv α (discreteGaussian μ v) (discreteGaussian ν v) ≠ ∞ := hlt.ne_top
  set r := (renyiDiv α (discreteGaussian μ v) (discreteGaussian ν v)).toReal with hr_def
  have hr : r < c := by
    rwa [← ENNReal.ofReal_toReal hR, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
      at hlt
  have hle := (renyiDiv_le_ofReal_iff_tsum hac hα ENNReal.toReal_nonneg).1
    (ENNReal.ofReal_toReal hR).ge
  rw [hH, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le, exp_le_exp] at hle
  nlinarith

/-- The log-likelihood ratio of `N_ℤ(μ, σ²)` against `N_ℤ(ν, σ²)` for integer locations is the
affine function `x ↦ (μ - ν) x / σ² + (ν² - μ²) / 2σ²`. -/
lemma DiscreteGaussian.llr_discreteGaussian (hv : v ≠ 0) (μ ν : ℤ) (x : ℤ) :
    llr (discreteGaussian μ v) (discreteGaussian ν v) x
      = ((μ : ℝ) - ν) / v * x + ((ν : ℝ) ^ 2 - μ ^ 2) / (2 * v) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  have hT := tsum_exp_neg_sq_sub_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)) 0
  simp only [sub_zero] at hT
  have hac := absolutelyContinuous_of_forall_ne_zero (P := discreteGaussian μ v)
    (discreteGaussian_singleton_ne_zero hv ν)
  rw [llr, toReal_rnDeriv_eq hac (discreteGaussian_singleton_ne_zero hv ν x),
    discreteGaussian_real_singleton, discreteGaussian_real_singleton,
    discreteGaussianPMFReal_intCast, discreteGaussianPMFReal_intCast,
    div_div_div_cancel_right₀ hT.ne', ← Real.exp_sub, Real.log_exp]
  field_simp
  ring

/-- **Proposition 5** of Canonne–Kamath–Steinke at `α = 1`, with equality: for `v = σ² ≠ 0` and
integer locations `μ, ν`, `KL(N_ℤ(μ, σ²) ‖ N_ℤ(ν, σ²)) = (μ - ν)² / (2σ²)` (here `α (μ - ν)` is
always an integer). The paper's proof treats `α > 1` only; this uses `E[N_ℤ(μ, σ²)] = μ`. -/
theorem renyiDiv_one_discreteGaussian (hv : v ≠ 0) (μ ν : ℤ) :
    renyiDiv 1 (discreteGaussian μ v) (discreteGaussian ν v)
      = ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v)) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  have := isProbabilityMeasure_discreteGaussian (μ : ℝ) hv
  have := isProbabilityMeasure_discreteGaussian (ν : ℝ) hv
  have hac := absolutelyContinuous_of_forall_ne_zero (P := discreteGaussian μ v)
    (discreteGaussian_singleton_ne_zero hv ν)
  obtain ⟨hint, hmean⟩ := integral_discreteGaussian_intCast hv μ
  have hllr : llr (discreteGaussian μ v) (discreteGaussian ν v)
      = fun x : ℤ ↦ ((μ : ℝ) - ν) / v * x + ((ν : ℝ) ^ 2 - μ ^ 2) / (2 * v) :=
    funext (DiscreteGaussian.llr_discreteGaussian hv μ ν)
  have hint' : Integrable (llr (discreteGaussian μ v) (discreteGaussian ν v))
      (discreteGaussian μ v) := by
    rw [hllr]
    exact (hint.const_mul _).add (integrable_const _)
  rw [renyiDiv_one_of_isProbabilityMeasure, klDiv_of_ac_of_integrable hac hint', hllr,
    integral_add (hint.const_mul _) (integrable_const _), integral_const_mul, hmean,
    integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, add_sub_cancel_right]
  congr 1
  field_simp
  ring

/-- **Proposition 5** of Canonne–Kamath–Steinke, equality case: for `v = σ² ≠ 0`, integer
locations `μ, ν` and an order `α ≥ 1` such that `α (μ - ν)` is an integer,
`D_α(N_ℤ(μ, σ²) ‖ N_ℤ(ν, σ²)) = (μ - ν)² / (2σ²) · α`. -/
theorem renyiDiv_discreteGaussian_eq (hv : v ≠ 0) (μ ν : ℤ) {α : ℝ} (hα : 1 ≤ α)
    (hint : ∃ k : ℤ, α * (μ - ν) = k) :
    renyiDiv α (discreteGaussian μ v) (discreteGaussian ν v)
      = ENNReal.ofReal ((μ - ν) ^ 2 / (2 * v) * α) := by
  rcases hα.eq_or_lt with rfl | hα
  · rw [renyiDiv_one_discreteGaussian hv, mul_one]
  · exact renyiDiv_discreteGaussian_eq_of_one_lt hv μ ν hα hint

/-! ### The discrete Gaussian mechanism -/

section Mechanism

variable {𝒟 : Type*} {m𝒟 : MeasurableSpace 𝒟} {Adj : 𝒟 → 𝒟 → Prop}

/-- **The discrete Gaussian mechanism** `M(S) = q(S) + Y` with `Y ∼ N_ℤ(0, v)` (Theorem 4 of
Canonne–Kamath–Steinke), for a measurable integer-valued query `q`: the kernel
`S ↦ N_ℤ(q S, v)`, which is the law of `q(S) + Y` by `discreteGaussian_intCast_eq_map`. -/
noncomputable def discreteGaussianMechanism (q : 𝒟 → ℤ) (hq : Measurable q) (v : ℝ≥0) :
    Kernel 𝒟 ℤ :=
  (Kernel.ofFunOfCountable fun μ : ℤ ↦ discreteGaussian μ v).comap q hq

lemma discreteGaussianMechanism_apply (q : 𝒟 → ℤ) (hq : Measurable q) (v : ℝ≥0) (S : 𝒟) :
    discreteGaussianMechanism q hq v S = discreteGaussian (q S) v :=
  rfl

/-- The discrete Gaussian mechanism is a Markov kernel for `v ≠ 0`. -/
lemma isMarkovKernel_discreteGaussianMechanism (q : 𝒟 → ℤ) (hq : Measurable q) (hv : v ≠ 0) :
    IsMarkovKernel (discreteGaussianMechanism q hq v) :=
  ⟨fun _ ↦ isProbabilityMeasure_discreteGaussian _ hv⟩

/-- **Theorem 4** of Canonne–Kamath–Steinke, for a general scale: if the integer-valued query
`q` has sensitivity `Δ` (`|q S - q S'| ≤ Δ` for neighbours) and `M S = N_ℤ(q S, σ²)` with
`v = σ² ≠ 0`, then `M` is `(Δ² / (2σ²))`-zCDP. The paper's statement is the case `σ = Δ / ε`
(`isZCDP_discreteGaussianMechanism`); this form is the one the paper's proof gives (it follows
from Proposition 5 and Definition 3). -/
theorem isZCDP_of_discreteGaussian {q : 𝒟 → ℤ} {Δ : ℝ}
    (hq : ∀ ⦃S S'⦄, Adj S S' → |(q S : ℝ) - q S'| ≤ Δ) (hv : v ≠ 0) {M : Kernel 𝒟 ℤ}
    (hM : ∀ S, M S = discreteGaussian (q S) v) : IsZCDP M Adj 0 (Δ ^ 2 / (2 * v)) := by
  refine (isZCDP_iff_le_ofReal le_rfl (by positivity)).2 fun S S' hS α hα ↦ ?_
  rw [hM, hM, zero_add]
  refine (renyiDiv_discreteGaussian_le hv _ _ hα.le).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := abs_le.1 (hq hS)
  have h2 : ((q S : ℝ) - q S') ^ 2 ≤ Δ ^ 2 := sq_le_sq' h.1 h.2
  gcongr

/-- **Theorem 4** of Canonne–Kamath–Steinke (discrete Gaussian satisfies concentrated
differential privacy): for `Δ, ε > 0` and a measurable query `q : 𝒟 → ℤ` with
`|q S - q S'| ≤ Δ` for neighbours, the mechanism `M(S) = q(S) + Y` with `Y ∼ N_ℤ(0, Δ² / ε²)`
is `(ε² / 2)`-zCDP.

The hypothesis `Measurable q` is only needed to build the kernel and costs nothing: the paper's
datasets carry no σ-algebra, so the dataset space may be given the discrete σ-algebra `⊤`, for
which every `q` is measurable; moreover `isZCDP_of_discreteGaussian` assumes no measurability,
since zCDP only involves the laws `M S`. -/
theorem isZCDP_discreteGaussianMechanism {q : 𝒟 → ℤ} (hq_meas : Measurable q) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hq : ∀ ⦃S S'⦄, Adj S S' → |(q S : ℝ) - q S'| ≤ Δ) :
    IsZCDP (discreteGaussianMechanism q hq_meas (Δ ^ 2 / ε ^ 2).toNNReal) Adj 0 (ε ^ 2 / 2) := by
  have hv : (Δ ^ 2 / ε ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  convert isZCDP_of_discreteGaussian hq hv (discreteGaussianMechanism_apply q hq_meas _) using 1
  rw [Real.coe_toNNReal _ (by positivity)]
  field_simp

/-- **Approximate differential privacy of the discrete Gaussian via zCDP**: under the
hypotheses of Theorem 4 of Canonne–Kamath–Steinke, the mechanism `M(S) = q(S) + Y` with
`Y ∼ N_ℤ(0, Δ² / ε²)` is `(ε² / 2 + ε √(2 log (1 / δ)), δ)`-differentially private for every
`δ > 0`. This is the conversion stated after Definition 3 of the paper (from Bun–Steinke,
`IsZCDP.isEpsDeltaDP'`), applied to Theorem 4. It is weaker than the paper's Theorem 7 (not
formalized), whose `δ` is optimal in the worst case over queries of sensitivity `Δ` but which, as
printed, needs an integer `Δ` (see the notes on the paper); this theorem needs no such
restriction. -/
theorem isEpsDeltaDP_discreteGaussianMechanism {q : 𝒟 → ℤ} (hq_meas : Measurable q) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hq : ∀ ⦃S S'⦄, Adj S S' → |(q S : ℝ) - q S'| ≤ Δ) {δ : ℝ}
    (hδ : 0 < δ) :
    IsEpsDeltaDP (discreteGaussianMechanism q hq_meas (Δ ^ 2 / ε ^ 2).toNNReal) Adj
      (ε ^ 2 / 2 + ε * √(2 * log (1 / δ))) δ := by
  have hv : (Δ ^ 2 / ε ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have := isMarkovKernel_discreteGaussianMechanism q hq_meas hv
  convert (isZCDP_discreteGaussianMechanism hq_meas hΔ hε hq).isEpsDeltaDP' hδ using 2
  rw [show ε ^ 2 / 2 * log (1 / δ) = (ε / 2) ^ 2 * (2 * log (1 / δ)) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

/-- **Theorem 14** of Canonne–Kamath–Steinke (multivariate discrete Gaussian satisfies
concentrated differential privacy): for variances `v j = σ_j² ≠ 0` (`j ∈ ι`, a finite index
set) and a query `q : 𝒟 → (ι → ℤ)` with `∑_j (q_j(S) - q_j(S'))² / σ_j² ≤ ε²` for neighbours, a
mechanism with `M S = ∏_j N_ℤ(q_j(S), σ_j²)` (the product measure `Measure.pi`, which is the law
of `q(S) + Y` for `Y` with independent coordinates `Y_j ∼ N_ℤ(0, σ_j²)` by
`discreteGaussian_pi_eq_map`) is `(ε² / 2)`-zCDP. For the kernel
`discreteGaussianPiMechanism` this is `isZCDP_discreteGaussianPiMechanism`. -/
theorem isZCDP_of_discreteGaussian_pi {ι : Type*} [Fintype ι] {q : 𝒟 → ι → ℤ} {v : ι → ℝ≥0}
    (hv : ∀ j, v j ≠ 0) {ε : ℝ}
    (hq : ∀ ⦃S S'⦄, Adj S S' → ∑ j, ((q S j : ℝ) - q S' j) ^ 2 / v j ≤ ε ^ 2)
    {M : Kernel 𝒟 (ι → ℤ)} (hM : ∀ S, M S = Measure.pi fun j ↦ discreteGaussian (q S j) (v j)) :
    IsZCDP M Adj 0 (ε ^ 2 / 2) := by
  refine (isZCDP_iff_le_ofReal le_rfl (by positivity)).2 fun S S' hS α hα ↦ ?_
  have : ∀ j, NeZero (discreteGaussian (q S j) (v j)) := fun j ↦ by
    have := isProbabilityMeasure_discreteGaussian (q S j : ℝ) (hv j)
    infer_instance
  rw [hM, hM, renyiDiv_pi (by linarith), zero_add]
  calc ∑ j, renyiDiv α (discreteGaussian (q S j) (v j)) (discreteGaussian (q S' j) (v j))
      ≤ ∑ j, ENNReal.ofReal (((q S j : ℝ) - q S' j) ^ 2 / (2 * v j) * α) :=
        Finset.sum_le_sum fun j _ ↦ renyiDiv_discreteGaussian_le (hv j) _ _ hα.le
    _ = ENNReal.ofReal (α / 2 * ∑ j, ((q S j : ℝ) - q S' j) ^ 2 / v j) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ by positivity, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ ≤ ENNReal.ofReal (ε ^ 2 / 2 * α) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hq hS]

/-- The product `∏_j N_ℤ(m_j, σ_j²)` of discrete Gaussians with integer locations `m` is the law
of `m + Y`, where `Y` has independent coordinates `Y_j ∼ N_ℤ(0, σ_j²)` (law `∏_j N_ℤ(0, σ_j²)`). -/
theorem discreteGaussian_pi_eq_map {ι : Type*} [Fintype ι] (m : ι → ℤ) (v : ι → ℝ≥0) :
    (Measure.pi fun j ↦ discreteGaussian (m j) (v j))
      = (Measure.pi fun j ↦ discreteGaussian 0 (v j)).map (· + m) := by
  have h := Measure.pi_map_pi (μ := fun j ↦ discreteGaussian 0 (v j)) (f := fun j y ↦ y + m j)
    fun _ ↦ (measurable_of_countable _).aemeasurable
  simp_rw [← discreteGaussian_intCast_eq_map] at h
  rw [← h]
  rfl

/-- **The multivariate discrete Gaussian mechanism** of Theorem 14 of Canonne–Kamath–Steinke:
for a measurable query `q : 𝒟 → (ι → ℤ)` and variances `v j = σ_j²`, the kernel
`S ↦ ∏_j N_ℤ(q_j(S), σ_j²)`, i.e. `M(S) = q(S) + Y` with independent `Y_j ∼ N_ℤ(0, σ_j²)`
(`discreteGaussian_pi_eq_map`). -/
noncomputable def discreteGaussianPiMechanism {ι : Type*} [Fintype ι] (q : 𝒟 → ι → ℤ)
    (hq : Measurable q) (v : ι → ℝ≥0) : Kernel 𝒟 (ι → ℤ) :=
  (Kernel.ofFunOfCountable fun m : ι → ℤ ↦ Measure.pi fun j ↦ discreteGaussian (m j) (v j)).comap
    q hq

lemma discreteGaussianPiMechanism_apply {ι : Type*} [Fintype ι] (q : 𝒟 → ι → ℤ)
    (hq : Measurable q) (v : ι → ℝ≥0) (S : 𝒟) :
    discreteGaussianPiMechanism q hq v S = Measure.pi fun j ↦ discreteGaussian (q S j) (v j) :=
  rfl

/-- The multivariate discrete Gaussian mechanism is a Markov kernel when every `v j ≠ 0`. -/
lemma isMarkovKernel_discreteGaussianPiMechanism {ι : Type*} [Fintype ι] (q : 𝒟 → ι → ℤ)
    (hq : Measurable q) {v : ι → ℝ≥0} (hv : ∀ j, v j ≠ 0) :
    IsMarkovKernel (discreteGaussianPiMechanism q hq v) :=
  ⟨fun S ↦ by
    have := fun j ↦ isProbabilityMeasure_discreteGaussian (q S j : ℝ) (hv j)
    rw [discreteGaussianPiMechanism_apply]
    infer_instance⟩

/-- **Theorem 14** of Canonne–Kamath–Steinke for the kernel `discreteGaussianPiMechanism`: if
every `v j = σ_j² ≠ 0` and `∑_j (q_j(S) - q_j(S'))² / σ_j² ≤ ε²` for neighbours, then
`M(S) = q(S) + Y` with independent `Y_j ∼ N_ℤ(0, σ_j²)` is `(ε² / 2)`-zCDP. -/
theorem isZCDP_discreteGaussianPiMechanism {ι : Type*} [Fintype ι] {q : 𝒟 → ι → ℤ}
    (hq_meas : Measurable q) {v : ι → ℝ≥0} (hv : ∀ j, v j ≠ 0) {ε : ℝ}
    (hq : ∀ ⦃S S'⦄, Adj S S' → ∑ j, ((q S j : ℝ) - q S' j) ^ 2 / v j ≤ ε ^ 2) :
    IsZCDP (discreteGaussianPiMechanism q hq_meas v) Adj 0 (ε ^ 2 / 2) :=
  isZCDP_of_discreteGaussian_pi hv hq (discreteGaussianPiMechanism_apply q hq_meas v)

end Mechanism

end InformationTheory
