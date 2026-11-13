/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.Amplification.HockeyStick
public import InfoLeakage.ZCDP.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Probability.CDF

/-!
# The analytic Gaussian mechanism

This file formalizes the exact `(ε, δ)` characterization of the Gaussian mechanism from
B. Balle and Y.-X. Wang, *Improving the Gaussian mechanism for differential privacy: analytical
calibration and optimal denoising*, ICML 2018 ([arXiv:1805.06530](https://arxiv.org/abs/1805.06530);
result numbers follow arXiv v2), together with its restatement in J. Dong, A. Roth and W. J. Su,
*Gaussian differential privacy* ([arXiv:1905.02383](https://arxiv.org/abs/1905.02383), v3,
Corollary 2.13) and the classical calibration of C. Dwork and A. Roth, *The Algorithmic
Foundations of Differential Privacy*, 2014 (Theorem A.1 = Theorem 3.22).

With `Φ = cdf (gaussianReal 0 1)` the standard normal CDF, the central quantity is
`gaussianDelta μ ε = Φ(μ / 2 - ε / μ) - e^ε Φ(-μ / 2 - ε / μ)`, used for `μ > 0`. For
`M S = N(q S, σ²)` and a query `q` of positive global sensitivity `Δ > 0`, the privacy profile of
`M` is exactly
`gaussianDelta (Δ / σ) ε = Φ(Δ / (2σ) - ε σ / Δ) - e^ε Φ(-Δ / (2σ) - ε σ / Δ)` (equation (6)), so
`M` is `(ε, δ)`-DP iff this is at most `δ` (Theorem 8).

**Scope.** Mechanisms are kernels `M : Kernel 𝒟 ℝ` with `M S = gaussianReal (q S) v`, `v = σ² ≠ 0`,
for an arbitrary neighbouring relation `Adj`; `(ε, δ)`-DP is the library's `IsEpsDeltaDP`, the
hockey-stick divergence and privacy profile are `hockeyStickDiv` and `privacyProfile` from
`InfoLeakage.Amplification.HockeyStick`. Only **scalar** queries (`d = 1`) are treated: the
paper's `ℝ^d`-valued mechanism with `ℓ₂` sensitivity is not formalized. The global sensitivity
`Δ = sup_{S ≃ S'} |q S - q S'|` is expressed as `IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ`
(it need not be attained); sufficiency results only need `Δ` to be an upper bound. All results
assume `Δ > 0`; zero sensitivity is excluded, since at `μ = 0` Lean's convention `x / 0 = 0`
makes `gaussianDelta 0 ε = (1 - e^ε) / 2`, whereas the profile of a constant query is
`max 0 (1 - e^ε)`. Unless stated otherwise results hold for all real `ε` and `δ` (the papers
take `ε ≥ 0`, `δ ∈ [0, 1]`).

## Main definitions

* `gaussianDelta μ ε`: `Φ(μ / 2 - ε / μ) - e^ε Φ(-μ / 2 - ε / μ)`, for `μ > 0` the privacy
  profile of the Gaussian mechanism with `μ = Δ / σ`, `Δ > 0` (left-hand side of equation (6) of
  Balle–Wang, `δ(ε)` of Corollary 2.13 of Dong–Roth–Su).

## Main statements (paper result → Lean name)

Balle–Wang:
* Theorem 1 (classical Gaussian mechanism, `σ ≥ Δ √(2 log (1.25 / δ)) / ε`, `ε, δ ∈ (0, 1)`):
  `isEpsDeltaDP_gaussianReal_classical'`.
* Theorem 2 (`σ ≥ Δ / (2δ)` gives `(0, δ)`-DP): `isEpsDeltaDP_zero_of_gaussianReal`.
* Lemma 3 (the privacy loss is `N(η, 2η)`, `η = D² / (2σ²)`): `map_log_gaussianPDFReal_div`.
* Theorem 4 (low-privacy lower bound `σ ≥ Δ / √(2ε)`): exact form
  `div_sqrt_le_of_isEpsDeltaDP_gaussianReal` (`δ < δ₀(ε) = Φ(0) - e^ε Φ(-√(2ε))`), and a corrected
  explicit form `div_sqrt_le_of_isEpsDeltaDP_gaussianReal'` (`δ < 1 / 2 - 1 / √(4πε)`); the
  statement as printed is refuted by `not_forall_div_sqrt_le_of_isEpsDeltaDP_gaussianReal` (see
  the notes below).
* Theorem 5 (characterization through the likelihood-ratio event `E* = {p ≥ e^ε p'}`), in the
  density form (10) of its proof, for densities w.r.t. any common measure:
  `hockeyStickDiv_withDensity`; the underlying Neyman–Pearson argument:
  `hockeyStickDiv_eq_of_forall_subset`.
* Lemma 6 (privacy-loss probabilities through `Φ`), as stated in the paper for the mechanism's
  privacy loss: `measureReal_privacyLoss_ge` (equation (4)), `measureReal_privacyLoss_le`
  (equation (5)); in terms of the law `N(η, 2η)` of Lemma 3:
  `measureReal_gaussianReal_Ici_privacyLoss`, `measureReal_gaussianReal_Iic_privacyLoss`;
  combined with Theorem 5: `hockeyStickDiv_gaussianReal`, and the target form
  `D_{e^ε}(N(0, σ²) ‖ N(Δ, σ²)) = Φ(Δ / (2σ) - εσ / Δ) - e^ε Φ(-Δ / (2σ) - εσ / Δ)`:
  `hockeyStickDiv_gaussianReal_zero`.
* Lemma 7 (monotonicity in the distance): `monotoneOn_gaussianDelta` (in `μ = √(2η)`).
* Theorem 8 (analytic Gaussian mechanism): `isEpsDeltaDP_gaussianReal_iff`; in privacy-profile
  form `privacyProfile_gaussianReal`; its two halves for a sensitivity bound / a single pair:
  `isEpsDeltaDP_of_gaussianReal`, `gaussianDelta_le_of_isEpsDeltaDP`; for the library's
  `ZCDP.gaussianKernel`: `isEpsDeltaDP_gaussianKernel_iff`, `privacyProfile_gaussianKernel`.

Dong–Roth–Su:
* Theorem 8 of Balle–Wang in DRS notation (`μ = Δ / σ`), i.e. the `⇒` direction of Corollary 2.13
  applied to the Gaussian mechanism (which is `μ`-GDP by Theorem 2.7); no GDP statement is
  formalized: `isEpsDeltaDP_gaussianReal_drs` (the mechanism is `(ε, δ(ε))`-DP for every `ε`) and
  `privacyProfile_gaussianReal_eq_drs` (`δ(ε)` is its exact privacy profile);
  `gaussianDelta_eq_hockeyStickDiv` identifies `δ(ε)` with `D_{e^ε}(N(μ, 1) ‖ N(0, 1))`, the
  profile of the pair defining `G_μ`.

Dwork–Roth:
* Theorem A.1 / 3.22 (classical calibration `σ ≥ c Δ / ε`, `c² > 2 log (1.25 / δ)`,
  `ε ∈ (0, 1)`): `isEpsDeltaDP_gaussianReal_classical`.

## Auxiliary results

`AnalyticGaussian.cdf_gaussianReal` (`cdf N(m, σ²) x = Φ((x - m) / σ)`), `AnalyticGaussian.cdf_neg`
(`Φ(-x) = 1 - Φ(x)`), `AnalyticGaussian.continuous_cdf_gaussianReal`,
`AnalyticGaussian.cdf_sub_cdf_le` (`Φ(b) - Φ(a) ≤ (b - a) / √(2π)`), Gordon's inequality
`AnalyticGaussian.cdf_neg_le`, the tail bound `AnalyticGaussian.cdf_neg_le_half_exp`
(`Φ(-t) ≤ e^{-t² / 2} / 2`), and invariance of the hockey-stick divergence under measurable
equivalences `hockeyStickDiv_map_measurableEquiv`.

## Implementation notes

* Theorem 8 is derived as in the paper from Theorem 5 (via `hockeyStickDiv_withDensity`) and the
  computation of the likelihood-ratio event `E* = [t, ∞)`; the reduction to the extreme pair uses
  monotonicity (Lemma 7) and, because the supremum defining `Δ` need not be attained, continuity
  of `gaussianDelta` in `μ`. Lemma 7 is proved from the stochastic ordering of `N(μ, 1)` in `μ`
  rather than by differentiation.
* Theorem 2 is proved through the exact formula (`Φ(δ) - Φ(-δ) ≤ 2δ / √(2π)`) rather than by
  Pinsker's inequality; Theorem 1 and Dwork–Roth Theorem A.1 are proved through the exact formula
  and the Gaussian tail bounds above rather than through the privacy-loss tail bound.

## Notes on the paper

* Balle–Wang, Theorem 4 (arXiv v2, p. 4, with its proof in Appendix A.1, p. 16) assumes
  `0 < δ < 1 / 2 - e^{-3ε} / √(4πε)`. The faulty step of the proof is the equality
  `e^ε Φ(-√(2ε)) = e^ε Φᶜ(√(2ε)) = e^{-3ε} / √(2π) · r(√(2ε))`, with `r` the Mills ratio: since
  `Φᶜ(t) = e^{-t² / 2} r(t) / √(2π)` and `e^ε e^{-(√(2ε))² / 2} = e^0`, the factor `e^{-3ε}` should
  be `1`. Gordon's inequality `r(t) < 1 / t` is used correctly and then gives
  `e^ε Φ(-√(2ε)) < 1 / √(4πε)`. The stated result is false, and its negation is formalized as
  `not_forall_div_sqrt_le_of_isEpsDeltaDP_gaussianReal`: for `ε = 1`, `δ = 0.47`
  (`< 0.4859… = 1 / 2 - e^{-3} / √(4π)`) and `σ = 2Δ / 3 < Δ / √2`, the mechanism is
  `(1, 0.47)`-DP because `δ(3 / 2, 1) ≈ 0.320` (certified there as `≤ 0.47`). (Numerically also
  `σ = 0.65 Δ` and `δ = 0.4` work, with `δ(1 / 0.65, 1) ≈ 0.336`.) With the bound
  `δ < 1 / 2 - 1 / √(4πε)` the theorem holds and is formalized as
  `div_sqrt_le_of_isEpsDeltaDP_gaussianReal'`; the paper's remark that the admissible range of `δ`
  tends to `1 / 2` as `ε → ∞` remains true for the corrected bound.

## Not formalized

The `ℝ^d`-valued mechanism with `ℓ₂` sensitivity; the privacy-loss random-variable form of
Theorem 5 for general mechanisms; Algorithm 1 and Theorem 9 (numerical calibration); Section 4
(optimal denoising); Gaussian differential privacy itself (trade-off functions on `ℝ`, Definition
2.6 and the `μ`-GDP side of Corollary 2.13 of Dong–Roth–Su).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real Filter Topology
open scoped NNReal ENNReal

namespace InformationTheory

variable {Z : Type*} {mZ : MeasurableSpace Z}

namespace AnalyticGaussian

/-! ### The standard normal CDF -/

/-- Standardizing a Gaussian: if `X ∼ N(m, v)` with `v ≠ 0` then `(X - m) / √v ∼ N(0, 1)`. -/
lemma map_gaussianReal_standardize (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m v).map (fun x ↦ (x - m) / √(v : ℝ)) = gaussianReal 0 1 := by
  have h : (fun x : ℝ ↦ (x - m) / √(v : ℝ)) = (· / √(v : ℝ)) ∘ (· - m) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_div_const, sub_self, zero_div]
  congr 1
  ext
  have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  simp [Real.sq_sqrt v.coe_nonneg, this]

/-- The CDF of `N(m, v)` is `Φ((x - m) / √v)`, where `Φ = cdf (gaussianReal 0 1)`. -/
lemma cdf_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal m v) x = cdf (gaussianReal 0 1) ((x - m) / √(v : ℝ)) := by
  have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (by positivity)
  rw [cdf_eq_real, cdf_eq_real, ← map_gaussianReal_standardize m hv,
    map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext y
  simp only [mem_preimage, mem_Iic, div_le_div_iff_of_pos_right hσ, sub_le_sub_iff_right]

/-- Symmetry of the standard normal CDF: `Φ(-x) = 1 - Φ(x)`. -/
lemma cdf_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h : (gaussianReal 0 1).map (fun x ↦ -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Iic (-x) = Ici x := by ext; simp
  rw [cdf_eq_real, cdf_eq_real, ← h, map_measureReal_apply measurable_neg measurableSet_Iic, hpre,
    h, ← compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic]

/-- The upper tail of `N(m, v)`: `N(m, v)(x, ∞) = Φ((m - x) / √v)`. -/
lemma measureReal_gaussianReal_Ioi (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal m v).real (Ioi x) = cdf (gaussianReal 0 1) ((m - x) / √(v : ℝ)) := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_gaussianReal m hv, ← cdf_neg, ← neg_div, neg_sub]

/-- The standard normal CDF is continuous. -/
lemma continuous_cdf_gaussianReal : Continuous (cdf (gaussianReal 0 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rw [(monotone_cdf _).continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h := (cdf (gaussianReal 0 1)).measure_singleton x
  rw [measure_cdf, measure_singleton] at h
  have h₁ := ENNReal.ofReal_eq_zero.1 h.symm
  have h₂ := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl x)
  linarith

end AnalyticGaussian

/-! ### The Neyman–Pearson form of the hockey-stick divergence -/

section NeymanPearson

variable {γ : ℝ} {μ ν : Measure Z}

/-- **Neyman–Pearson form of the hockey-stick divergence.** If `T` is a measurable set such that
`γ ν(A) ≤ μ(A)` for the measurable subsets `A` of `T` and `μ(A) ≤ γ ν(A)` for those of its
complement, then `T` attains the supremum: `D_γ(μ ‖ ν) = μ(T) - γ ν(T)`. -/
theorem hockeyStickDiv_eq_of_forall_subset [IsFiniteMeasure μ] [IsFiniteMeasure ν] {T : Set Z}
    (hT : MeasurableSet T) (h₁ : ∀ A ⊆ T, MeasurableSet A → γ * ν.real A ≤ μ.real A)
    (h₂ : ∀ A ⊆ Tᶜ, MeasurableSet A → μ.real A ≤ γ * ν.real A) :
    hockeyStickDiv γ μ ν = μ.real T - γ * ν.real T := by
  refine le_antisymm (hockeyStickDiv_le_of_forall fun E hE ↦ ?_) (sub_le_hockeyStickDiv hT)
  have e₁ := measureReal_inter_add_sdiff (μ := μ) (s := E) hT
  have e₂ : γ * ν.real E = γ * ν.real (E ∩ T) + γ * ν.real (E \ T) := by
    rw [← mul_add, measureReal_inter_add_sdiff hT]
  have e₃ := measureReal_inter_add_sdiff (μ := μ) (s := T) hE
  have e₄ : γ * ν.real T = γ * ν.real (T ∩ E) + γ * ν.real (T \ E) := by
    rw [← mul_add, measureReal_inter_add_sdiff hE]
  have k₁ := h₂ (E \ T) (fun _ hx ↦ hx.2) (hE.diff hT)
  have k₂ := h₁ (T \ E) sdiff_subset (hT.diff hE)
  rw [inter_comm] at e₃ e₄
  linarith

namespace AnalyticGaussian

lemma mul_measureReal_le_of_le [IsFiniteMeasure μ] (hγ : 0 ≤ γ) {A : Set Z}
    (h : ENNReal.ofReal γ * ν A ≤ μ A) : γ * ν.real A ≤ μ.real A := by
  have := ENNReal.toReal_mono (measure_ne_top μ A) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ] at this

lemma measureReal_le_mul_of_le [IsFiniteMeasure ν] (hγ : 0 ≤ γ) {A : Set Z}
    (h : μ A ≤ ENNReal.ofReal γ * ν A) : μ.real A ≤ γ * ν.real A := by
  have := ENNReal.toReal_mono (by finiteness) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ] at this

end AnalyticGaussian

open AnalyticGaussian in
/-- **Theorem 5** of Balle–Wang, in the density form (10) of its proof: if `μ = p · ρ` and
`ν = q · ρ` are finite measures with densities `p, q` with respect to a common measure `ρ`, the
hockey-stick divergence is attained at the likelihood-ratio event `E* = {γ q ≤ p}`:
`D_γ(μ ‖ ν) = μ(E*) - γ ν(E*)`. With Theorem 1 of Balle–Barthe–Gaboardi this characterizes
`(ε, δ)`-differential privacy. (Informal remark, not formalized here: with `γ = e^ε` and
`p, q > 0`, `μ(E*)` and `ν(E*)` are the paper's privacy-loss probabilities `P[L_{M,x,x'} ≥ ε]` and
`P[L_{M,x',x} ≤ -ε]`; for the Gaussian mechanism see `measureReal_privacyLoss_ge`.) -/
theorem hockeyStickDiv_withDensity {ρ : Measure Z} {p q : Z → ℝ≥0∞} (hp : Measurable p)
    (hq : Measurable q) [IsFiniteMeasure (ρ.withDensity p)] [IsFiniteMeasure (ρ.withDensity q)]
    (hγ : 0 ≤ γ) :
    hockeyStickDiv γ (ρ.withDensity p) (ρ.withDensity q) =
      (ρ.withDensity p).real {z | ENNReal.ofReal γ * q z ≤ p z} -
        γ * (ρ.withDensity q).real {z | ENNReal.ofReal γ * q z ≤ p z} := by
  refine hockeyStickDiv_eq_of_forall_subset (measurableSet_le (hq.const_mul _) hp)
    (fun A hA hAm ↦ mul_measureReal_le_of_le hγ ?_) (fun A hA hAm ↦ measureReal_le_mul_of_le hγ ?_)
  · rw [withDensity_apply _ hAm, withDensity_apply _ hAm, ← lintegral_const_mul _ hq]
    exact setLIntegral_mono hp fun z hz ↦ hA hz
  · rw [withDensity_apply _ hAm, withDensity_apply _ hAm, ← lintegral_const_mul _ hq]
    exact setLIntegral_mono (hq.const_mul _) fun z hz ↦ (not_le.1 (hA hz)).le

/-- The hockey-stick divergence is invariant under a measurable equivalence. -/
lemma hockeyStickDiv_map_measurableEquiv {Z' : Type*} [MeasurableSpace Z'] (e : Z ≃ᵐ Z')
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hockeyStickDiv γ (μ.map e) (ν.map e) = hockeyStickDiv γ μ ν := by
  refine le_antisymm (hockeyStickDiv_le_of_forall fun E hE ↦ ?_)
    (hockeyStickDiv_le_of_forall fun E hE ↦ ?_)
  · rw [map_measureReal_apply e.measurable hE, map_measureReal_apply e.measurable hE]
    exact sub_le_hockeyStickDiv (e.measurable hE)
  · have hE' := e.symm.measurable hE
    have : E = e ⁻¹' (e.symm ⁻¹' E) := by ext; simp
    rw [this, ← map_measureReal_apply e.measurable hE', ← map_measureReal_apply e.measurable hE']
    exact sub_le_hockeyStickDiv hE'

end NeymanPearson

/-! ### The hockey-stick divergence between two Gaussians -/

/-- The **privacy profile of the Gaussian mechanism**,
`δ(μ, ε) = Φ(μ / 2 - ε / μ) - e^ε Φ(-μ / 2 - ε / μ)`, where `Φ = cdf (gaussianReal 0 1)` is the
standard normal CDF. With `μ = Δ / σ` this is the left-hand side of equation (6) of Balle–Wang
(`gaussianDelta_div`), and it is the `δ(ε)` appearing in Corollary 2.13 of Dong–Roth–Su
(`gaussianDelta_eq_drs`). It is meaningful for `μ > 0`. -/
noncomputable def gaussianDelta (μ ε : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (μ / 2 - ε / μ) - exp ε * cdf (gaussianReal 0 1) (-(μ / 2) - ε / μ)

/-- `gaussianDelta (Δ / σ) ε` is the left-hand side of equation (6) of Balle–Wang. -/
lemma gaussianDelta_div (Δ σ ε : ℝ) :
    gaussianDelta (Δ / σ) ε = cdf (gaussianReal 0 1) (Δ / (2 * σ) - ε * σ / Δ) -
      exp ε * cdf (gaussianReal 0 1) (-(Δ / (2 * σ)) - ε * σ / Δ) := by
  rw [gaussianDelta, div_div, mul_comm σ 2, div_div_eq_mul_div]

/-- `gaussianDelta μ ε` is the `δ(ε) = Φ(-ε / μ + μ / 2) - e^ε Φ(-ε / μ - μ / 2)` of Corollary 2.13
of Dong–Roth–Su. -/
lemma gaussianDelta_eq_drs (μ ε : ℝ) :
    gaussianDelta μ ε = cdf (gaussianReal 0 1) (-ε / μ + μ / 2) -
      exp ε * cdf (gaussianReal 0 1) (-ε / μ - μ / 2) := by
  rw [gaussianDelta, show μ / 2 - ε / μ = -ε / μ + μ / 2 by ring,
    show -(μ / 2) - ε / μ = -ε / μ - μ / 2 by ring]

namespace AnalyticGaussian

lemma gaussianPDFReal_eq_exp_mul (m₁ m₂ : ℝ) (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal m₁ v y =
      exp ((m₁ - m₂) * (2 * y - m₁ - m₂) / (2 * v)) * gaussianPDFReal m₂ v y := by
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← exp_add]
  congr 2
  ring

/-- For `m₂ < m₁`, the likelihood-ratio event `{e^ε p₂ ≤ p₁}` of `N(m₁, v)` against `N(m₂, v)`
is the half-line `[(m₁ + m₂) / 2 + v ε / (m₁ - m₂), ∞)`. -/
lemma setOf_le_gaussianPDF {m₁ m₂ : ℝ} (h : m₂ < m₁) {v : ℝ≥0} (hv : v ≠ 0) (ε : ℝ) :
    {y | ENNReal.ofReal (exp ε) * gaussianPDF m₂ v y ≤ gaussianPDF m₁ v y} =
      Ici ((m₁ + m₂) / 2 + v * ε / (m₁ - m₂)) := by
  ext y
  have hd : 0 < m₁ - m₂ := sub_pos.2 h
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  simp only [mem_ofPred_eq, mem_Ici, gaussianPDF, ← ENNReal.ofReal_mul (exp_pos ε).le]
  rw [ENNReal.ofReal_le_ofReal_iff (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_eq_exp_mul m₁ m₂ v y, mul_le_mul_iff_left₀ (gaussianPDFReal_pos _ _ _ hv),
    exp_le_exp, le_div_iff₀ (by positivity), ← le_sub_iff_add_le', div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- The hockey-stick divergence between `N(m₁, v)` and `N(m₂, v)` for `m₂ < m₁`. -/
lemma hockeyStickDiv_gaussianReal_of_lt {m₁ m₂ : ℝ} (h : m₂ < m₁) {v : ℝ≥0} (hv : v ≠ 0)
    (ε : ℝ) : hockeyStickDiv (exp ε) (gaussianReal m₁ v) (gaussianReal m₂ v) =
      gaussianDelta ((m₁ - m₂) / √(v : ℝ)) ε := by
  have := nullSingletonClass_gaussianReal (μ := m₁) hv
  have := nullSingletonClass_gaussianReal (μ := m₂) hv
  have : IsFiniteMeasure (volume.withDensity (gaussianPDF m₁ v)) := by
    rw [← gaussianReal_of_var_ne_zero _ hv]; infer_instance
  have : IsFiniteMeasure (volume.withDensity (gaussianPDF m₂ v)) := by
    rw [← gaussianReal_of_var_ne_zero _ hv]; infer_instance
  have key := hockeyStickDiv_withDensity (ρ := volume) (measurable_gaussianPDF m₁ v)
    (measurable_gaussianPDF m₂ v) (exp_pos ε).le
  rw [← gaussianReal_of_var_ne_zero _ hv, ← gaussianReal_of_var_ne_zero _ hv,
    setOf_le_gaussianPDF h hv] at key
  rw [key, measureReal_congr Ioi_ae_eq_Ici.symm, measureReal_congr Ioi_ae_eq_Ici.symm,
    measureReal_gaussianReal_Ioi _ hv, measureReal_gaussianReal_Ioi _ hv, gaussianDelta]
  have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hd : m₁ - m₂ ≠ 0 := (sub_pos.2 h).ne'
  have hv' : (v : ℝ) = √(v : ℝ) ^ 2 := (sq_sqrt v.coe_nonneg).symm
  set σ := √(v : ℝ)
  rw [hv']
  congr 3
  · field_simp
    ring
  · field_simp
    ring

end AnalyticGaussian

open AnalyticGaussian in
/-- **The hockey-stick divergence between two Gaussians** with the same variance `v = σ² ≠ 0`
(Lemma 6 of Balle–Wang combined with Theorem 5): for distinct means and every real `ε`,
`D_{e^ε}(N(m₁, σ²) ‖ N(m₂, σ²)) = Φ(D / (2σ) - ε σ / D) - e^ε Φ(-D / (2σ) - ε σ / D)` with
`D = |m₁ - m₂|`. -/
theorem hockeyStickDiv_gaussianReal {m₁ m₂ : ℝ} (h : m₁ ≠ m₂) {v : ℝ≥0} (hv : v ≠ 0) (ε : ℝ) :
    hockeyStickDiv (exp ε) (gaussianReal m₁ v) (gaussianReal m₂ v) =
      gaussianDelta (|m₁ - m₂| / √(v : ℝ)) ε := by
  rcases h.lt_or_gt with h | h
  · have hn (m : ℝ) : (gaussianReal (-m) v).map (MeasurableEquiv.neg ℝ) = gaussianReal m v := by
      rw [show ⇑(MeasurableEquiv.neg ℝ) = fun x ↦ -x from rfl, gaussianReal_map_neg, neg_neg]
    have e := hockeyStickDiv_map_measurableEquiv (γ := exp ε) (MeasurableEquiv.neg ℝ)
      (μ := gaussianReal (-m₁) v) (ν := gaussianReal (-m₂) v)
    rw [hn, hn] at e
    rw [e, hockeyStickDiv_gaussianReal_of_lt (neg_lt_neg h) hv, abs_of_neg (sub_neg.2 h),
      neg_sub, neg_sub_neg]
  · rw [hockeyStickDiv_gaussianReal_of_lt h hv, abs_of_pos (sub_pos.2 h)]

/-- **Target form of Balle–Wang, Lemma 6 / equation (6)**: for `Δ > 0` and variance `v = σ² ≠ 0`,
`D_{e^ε}(N(0, σ²) ‖ N(Δ, σ²)) = Φ(Δ / (2σ) - ε σ / Δ) - e^ε Φ(-Δ / (2σ) - ε σ / Δ)`. -/
theorem hockeyStickDiv_gaussianReal_zero {Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) (ε : ℝ) :
    hockeyStickDiv (exp ε) (gaussianReal 0 v) (gaussianReal Δ v) =
      cdf (gaussianReal 0 1) (Δ / (2 * √(v : ℝ)) - ε * √(v : ℝ) / Δ) -
        exp ε * cdf (gaussianReal 0 1) (-(Δ / (2 * √(v : ℝ))) - ε * √(v : ℝ) / Δ) := by
  rw [hockeyStickDiv_gaussianReal hΔ.ne hv, zero_sub, abs_neg, abs_of_pos hΔ, gaussianDelta_div]

/-! ### Properties of `gaussianDelta` -/

section GaussianDelta

variable {μ μ' ε : ℝ}

/-- `δ(μ, ε)` is the hockey-stick divergence `D_{e^ε}(N(μ, 1) ‖ N(0, 1))` of the pair of unit
Gaussians defining `μ`-GDP in Dong–Roth–Su. -/
lemma gaussianDelta_eq_hockeyStickDiv (hμ : 0 < μ) (ε : ℝ) :
    gaussianDelta μ ε = hockeyStickDiv (exp ε) (gaussianReal μ 1) (gaussianReal 0 1) := by
  rw [hockeyStickDiv_gaussianReal hμ.ne' one_ne_zero, sub_zero, abs_of_pos hμ, NNReal.coe_one,
    sqrt_one, div_one]

lemma gaussianDelta_nonneg (hμ : 0 < μ) : 0 ≤ gaussianDelta μ ε := by
  rw [gaussianDelta_eq_hockeyStickDiv hμ]
  exact hockeyStickDiv_nonneg

lemma gaussianDelta_le_one (hμ : 0 < μ) : gaussianDelta μ ε ≤ 1 := by
  rw [gaussianDelta_eq_hockeyStickDiv hμ]
  exact hockeyStickDiv_le_one (exp_pos ε).le

/-- The event `E = ℝ` gives `1 - e^ε ≤ δ(μ, ε)`. -/
lemma one_sub_exp_le_gaussianDelta (hμ : 0 < μ) : 1 - exp ε ≤ gaussianDelta μ ε := by
  rw [gaussianDelta_eq_hockeyStickDiv hμ]
  simpa using sub_le_hockeyStickDiv (γ := exp ε) (μ := gaussianReal μ 1) (ν := gaussianReal 0 1)
    MeasurableSet.univ

/-- The upper-tail test `(s, ∞)` gives the lower bound `Φ(μ - s) - e^ε Φ(-s) ≤ δ(μ, ε)`; the
bound is attained at `s = μ / 2 + ε / μ`. -/
lemma cdf_sub_le_gaussianDelta (hμ : 0 < μ) (s : ℝ) :
    cdf (gaussianReal 0 1) (μ - s) - exp ε * cdf (gaussianReal 0 1) (-s) ≤ gaussianDelta μ ε := by
  rw [gaussianDelta_eq_hockeyStickDiv hμ]
  have h := sub_le_hockeyStickDiv (γ := exp ε) (μ := gaussianReal μ 1) (ν := gaussianReal 0 1)
    (measurableSet_Ioi (a := s))
  rwa [AnalyticGaussian.measureReal_gaussianReal_Ioi _ one_ne_zero,
    AnalyticGaussian.measureReal_gaussianReal_Ioi _ one_ne_zero, NNReal.coe_one, sqrt_one,
    div_one, div_one, zero_sub] at h

/-- **Lemma 7** of Balle–Wang: `δ(μ, ε)` is monotone in `μ > 0`. (The paper states it for
`h(η) = δ(√(2η), ε)` with `η = μ² / 2` the mean of the privacy loss, and proves it by
differentiating; here it follows from the stochastic ordering of `N(μ, 1)` in `μ`.) The endpoint
`η = 0` of the paper's domain `[0, ∞)` is omitted, as `δ(μ, ε)` is not defined by the formula at
`μ = 0`. -/
lemma monotoneOn_gaussianDelta (ε : ℝ) : MonotoneOn (fun μ ↦ gaussianDelta μ ε) (Ioi 0) := by
  intro μ hμ μ' hμ' h
  have hμ : 0 < μ := hμ
  have hμ' : 0 < μ' := hμ'
  calc gaussianDelta μ ε
      = cdf (gaussianReal 0 1) (μ - (μ / 2 + ε / μ)) -
          exp ε * cdf (gaussianReal 0 1) (-(μ / 2 + ε / μ)) := by
        rw [gaussianDelta, neg_add', show μ - (μ / 2 + ε / μ) = μ / 2 - ε / μ by ring]
    _ ≤ cdf (gaussianReal 0 1) (μ' - (μ / 2 + ε / μ)) -
          exp ε * cdf (gaussianReal 0 1) (-(μ / 2 + ε / μ)) := by
        gcongr
    _ ≤ gaussianDelta μ' ε := cdf_sub_le_gaussianDelta hμ' _

/-- `δ(μ, ε)` is continuous in `μ ≠ 0`. -/
lemma continuousAt_gaussianDelta (hμ : μ ≠ 0) (ε : ℝ) :
    ContinuousAt (fun μ ↦ gaussianDelta μ ε) μ := by
  have hΦ := AnalyticGaussian.continuous_cdf_gaussianReal
  unfold gaussianDelta
  refine ContinuousAt.sub (hΦ.continuousAt.comp ?_) (continuousAt_const.mul
    (hΦ.continuousAt.comp ?_)) <;> fun_prop (disch := exact hμ)

end GaussianDelta

/-! ### The Gaussian mechanism -/

section Mechanism

variable {𝒟 : Type*} {m𝒟 : MeasurableSpace 𝒟} {Adj : 𝒟 → 𝒟 → Prop} {q : 𝒟 → ℝ} {v : ℝ≥0}
  {M : Kernel 𝒟 ℝ} {ε δ Δ : ℝ}

namespace AnalyticGaussian

lemma hockeyStickDiv_self_le {γ : ℝ} (P : Measure ℝ) [IsProbabilityMeasure P] :
    hockeyStickDiv γ P P ≤ max 0 (1 - γ) :=
  hockeyStickDiv_le_of_forall fun E _ ↦ by
    have h₀ := measureReal_nonneg (μ := P) (s := E)
    have h₁ := measureReal_le_one (μ := P) (s := E)
    rcases le_total 0 (1 - γ) with h | h <;>
      nlinarith [le_max_left 0 (1 - γ), le_max_right 0 (1 - γ)]

/-- Two Gaussians whose means are at distance at most `Δ` have hockey-stick divergence at most
`δ(Δ / σ, ε)`. -/
lemma hockeyStickDiv_gaussianReal_le {m₁ m₂ : ℝ} (hΔ : 0 < Δ) (hd : |m₁ - m₂| ≤ Δ)
    (hv : v ≠ 0) (ε : ℝ) : hockeyStickDiv (exp ε) (gaussianReal m₁ v) (gaussianReal m₂ v) ≤
      gaussianDelta (Δ / √(v : ℝ)) ε := by
  have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  rcases eq_or_ne m₁ m₂ with rfl | h
  · exact (hockeyStickDiv_self_le _).trans (max_le (gaussianDelta_nonneg (by positivity))
      (one_sub_exp_le_gaussianDelta (by positivity)))
  · rw [hockeyStickDiv_gaussianReal h hv]
    exact monotoneOn_gaussianDelta ε (show (0 : ℝ) < _ from by
      have := abs_pos.2 (sub_ne_zero.2 h); positivity) (show (0 : ℝ) < _ from by positivity)
      (div_le_div_of_nonneg_right hd hσ.le)

lemma isMarkovKernel_of_gaussianReal (hM : ∀ S, M S = gaussianReal (q S) v) :
    IsMarkovKernel M :=
  ⟨fun S ↦ by rw [hM]; infer_instance⟩

end AnalyticGaussian

open AnalyticGaussian

/-- **Theorem 8** of Balle–Wang, sufficiency (scalar case): if the query `q` has sensitivity at
most `Δ > 0` (`|q S - q S'| ≤ Δ` for neighbours) and `M S = N(q S, σ²)` with `v = σ² ≠ 0`, then
`M` is `(ε, δ)`-DP as soon as `Φ(Δ / (2σ) - ε σ / Δ) - e^ε Φ(-Δ / (2σ) - ε σ / Δ) ≤ δ` (this is
`gaussianDelta (Δ / σ) ε ≤ δ`, see `gaussianDelta_div`). Valid for every real `ε`. -/
theorem isEpsDeltaDP_of_gaussianReal (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ) (hΔ : 0 < Δ)
    (hv : v ≠ 0) (hM : ∀ S, M S = gaussianReal (q S) v)
    (hδ : gaussianDelta (Δ / √(v : ℝ)) ε ≤ δ) : IsEpsDeltaDP M Adj ε δ := by
  have := isMarkovKernel_of_gaussianReal hM
  refine isEpsDeltaDP_iff_forall_hockeyStickDiv_le.2 fun S S' hS ↦ ?_
  rw [hM, hM]
  exact (hockeyStickDiv_gaussianReal_le hΔ (hq hS) hv ε).trans hδ

/-- **Theorem 8** of Balle–Wang, necessity at a single pair: if the Gaussian mechanism
`M S = N(q S, σ²)` is `(ε, δ)`-DP and `S, S'` are neighbours with `q S ≠ q S'`, then
`δ(|q S - q S'| / σ, ε) ≤ δ`. -/
theorem gaussianDelta_le_of_isEpsDeltaDP (h : IsEpsDeltaDP M Adj ε δ) (hv : v ≠ 0)
    (hM : ∀ S, M S = gaussianReal (q S) v) {S S' : 𝒟} (hS : Adj S S') (hd : q S ≠ q S') :
    gaussianDelta (|q S - q S'| / √(v : ℝ)) ε ≤ δ := by
  have := isMarkovKernel_of_gaussianReal hM
  have := isEpsDeltaDP_iff_forall_hockeyStickDiv_le.1 h hS
  rwa [hM, hM, hockeyStickDiv_gaussianReal hd hv] at this

/-- **The exact privacy profile of the Gaussian mechanism** (Balle–Wang, Theorem 8 in profile
form, scalar case, `d = 1`): if `Δ > 0` is the global sensitivity of `q` (the least upper
bound of `|q S - q S'|` over neighbours) and `M S = N(q S, σ²)` with `v = σ² ≠ 0`, then for
every real `ε`, `δ_M(ε) = Φ(Δ / (2σ) - ε σ / Δ) - e^ε Φ(-Δ / (2σ) - ε σ / Δ)`. The supremum
need not be attained. -/
theorem privacyProfile_gaussianReal
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0)
    (hM : ∀ S, M S = gaussianReal (q S) v) (ε : ℝ) :
    privacyProfile M Adj ε = gaussianDelta (Δ / √(v : ℝ)) ε := by
  have := isMarkovKernel_of_gaussianReal hM
  have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  refine le_antisymm (Real.iSup_le (fun p ↦ ?_) (gaussianDelta_nonneg (by positivity)))
    (le_of_forall_lt fun c hc ↦ ?_)
  · rw [hM, hM]
    exact hockeyStickDiv_gaussianReal_le hΔ₀ (hΔ.1 ⟨_, _, p.2, rfl⟩) hv ε
  · have hcont : ContinuousAt (fun d ↦ gaussianDelta (d / √(v : ℝ)) ε) Δ :=
      (continuousAt_gaussianDelta (by positivity) ε).comp (continuousAt_id.div_const _)
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hc))
    obtain ⟨d, ⟨S, S', hS, rfl⟩, hlt, hle⟩ := hΔ.exists_between
      (show max (Δ - η) 0 < Δ from max_lt (by linarith) hΔ₀)
    have hd : q S ≠ q S' := fun h ↦ by simp [h] at hlt
    have hdist : dist |q S - q S'| Δ < η := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith [le_max_left (Δ - η) 0]
    calc c < gaussianDelta (|q S - q S'| / √(v : ℝ)) ε := hball hdist
      _ = hockeyStickDiv (exp ε) (M S) (M S') := by rw [hM, hM, hockeyStickDiv_gaussianReal hd hv]
      _ ≤ privacyProfile M Adj ε := hockeyStickDiv_le_privacyProfile hS

/-- **Theorem 8** of Balle–Wang (analytic Gaussian mechanism), scalar case: if `Δ > 0` is the
global sensitivity of `q` (the least upper bound of `|q S - q S'|` over neighbours, attained or
not) and `M S = N(q S, σ²)` with `v = σ² ≠ 0`, then `M` is `(ε, δ)`-differentially private iff
`Φ(Δ / (2σ) - ε σ / Δ) - e^ε Φ(-Δ / (2σ) - ε σ / Δ) ≤ δ`, i.e. `gaussianDelta (Δ / σ) ε ≤ δ`.
The paper assumes `ε ≥ 0` and `δ ∈ [0, 1]`; the statement holds for all real `ε` and `δ`. -/
theorem isEpsDeltaDP_gaussianReal_iff
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0)
    (hM : ∀ S, M S = gaussianReal (q S) v) :
    IsEpsDeltaDP M Adj ε δ ↔ gaussianDelta (Δ / √(v : ℝ)) ε ≤ δ := by
  have := isMarkovKernel_of_gaussianReal hM
  rcases le_or_gt 0 δ with hδ | hδ
  · rw [isEpsDeltaDP_iff_privacyProfile_le hδ, privacyProfile_gaussianReal hΔ hΔ₀ hv hM]
  · obtain ⟨_, ⟨S, S', hS, rfl⟩, -⟩ := hΔ.exists_between (sub_one_lt Δ)
    have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
    exact ⟨fun h ↦ absurd (by simpa using h hS ∅) hδ.not_ge,
      fun h ↦ absurd ((gaussianDelta_nonneg (by positivity)).trans h) hδ.not_ge⟩

/-- Theorem 8 of Balle–Wang in the notation of Dong–Roth–Su (scalar case, `d = 1`): the Gaussian
mechanism `M S = N(q S, σ²)` for a query of global sensitivity `Δ > 0`, with `μ = Δ / σ`, has
privacy profile exactly `δ(ε) = Φ(-ε / μ + μ / 2) - e^ε Φ(-ε / μ - μ / 2)` for every real `ε`;
hence it is `(ε, δ(ε))`-DP for all `ε` and for no smaller `δ`. This is what the `⇒` direction of
Corollary 2.13 of Dong–Roth–Su gives for the Gaussian mechanism, which is `μ`-GDP by their
Theorem 2.7; `μ`-GDP itself is not formalized. -/
theorem privacyProfile_gaussianReal_eq_drs
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0)
    (hM : ∀ S, M S = gaussianReal (q S) v) {μ : ℝ} (hμ : Δ / √(v : ℝ) = μ) (ε : ℝ) :
    privacyProfile M Adj ε = cdf (gaussianReal 0 1) (-ε / μ + μ / 2) -
      exp ε * cdf (gaussianReal 0 1) (-ε / μ - μ / 2) := by
  rw [privacyProfile_gaussianReal hΔ hΔ₀ hv hM, hμ, gaussianDelta_eq_drs]

/-- Theorem 8 of Balle–Wang (sufficiency) in the notation of Dong–Roth–Su (scalar case, `d = 1`):
with `μ = Δ / σ`, the Gaussian mechanism is `(ε, Φ(-ε / μ + μ / 2) - e^ε Φ(-ε / μ - μ / 2))`-DP for
every `ε`, i.e. the `⇒` direction of Corollary 2.13 of Dong–Roth–Su applied to the Gaussian
mechanism (`μ`-GDP by their Theorem 2.7; GDP itself is not formalized). Here `Δ > 0` need only
bound the sensitivity. -/
theorem isEpsDeltaDP_gaussianReal_drs (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ)
    (hΔ₀ : 0 < Δ) (hv : v ≠ 0) (hM : ∀ S, M S = gaussianReal (q S) v) {μ : ℝ}
    (hμ : Δ / √(v : ℝ) = μ) (ε : ℝ) :
    IsEpsDeltaDP M Adj ε (cdf (gaussianReal 0 1) (-ε / μ + μ / 2) -
      exp ε * cdf (gaussianReal 0 1) (-ε / μ - μ / 2)) :=
  isEpsDeltaDP_of_gaussianReal hq hΔ₀ hv hM (by rw [hμ, gaussianDelta_eq_drs])

/-- **Theorem 8** of Balle–Wang for the library's Gaussian mechanism `ZCDP.gaussianKernel`. -/
theorem isEpsDeltaDP_gaussianKernel_iff (hq : Measurable q)
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0) :
    IsEpsDeltaDP (ZCDP.gaussianKernel q hq v) Adj ε δ ↔ gaussianDelta (Δ / √(v : ℝ)) ε ≤ δ :=
  isEpsDeltaDP_gaussianReal_iff hΔ hΔ₀ hv fun _ ↦ rfl

/-- The privacy profile of the library's Gaussian mechanism `ZCDP.gaussianKernel`. -/
theorem privacyProfile_gaussianKernel (hq : Measurable q)
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0)
    (ε : ℝ) : privacyProfile (ZCDP.gaussianKernel q hq v) Adj ε = gaussianDelta (Δ / √(v : ℝ)) ε :=
  privacyProfile_gaussianReal hΔ hΔ₀ hv (fun _ ↦ rfl) ε

end Mechanism

/-! ### Bounds on the standard normal CDF -/

namespace AnalyticGaussian

/-- `Φ(0) = 1 / 2`. -/
lemma cdf_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have := cdf_neg 0
  rw [neg_zero] at this
  linarith

/-- The standard normal density is at most `1 / √(2π)`, so `Φ(b) - Φ(a) ≤ (b - a) / √(2π)`. -/
lemma cdf_sub_cdf_le {a b : ℝ} (hab : a ≤ b) :
    cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ (b - a) / √(2 * π) := by
  have hc : 0 ≤ (√(2 * π))⁻¹ := inv_nonneg.2 (sqrt_nonneg _)
  have h : (gaussianReal 0 1) (Ioc a b) ≤ ENNReal.ofReal ((√(2 * π))⁻¹ * (b - a)) := by
    rw [gaussianReal_apply _ one_ne_zero, ENNReal.ofReal_mul hc, ← volume_Ioc,
      ← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun y _ ↦ ENNReal.ofReal_le_ofReal ?_
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one]
    exact mul_le_of_le_one_right hc (exp_le_one_iff.2 (by nlinarith [sq_nonneg (y - 0)]))
  rw [← measure_cdf (μ := gaussianReal 0 1), StieltjesFunction.measure_Ioc,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith [show (√(2 * π))⁻¹ * (b - a) = (b - a) / √(2 * π) by ring]

/-- A lower bound on the mass of a negative interval: for `0 ≤ a ≤ b`,
`Φ(-a) - Φ(-b) ≥ (b - a) e^{-b² / 2} / √(2π)`. -/
lemma mul_exp_div_le_cdf_neg_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * exp (-b ^ 2 / 2) / √(2 * π) ≤
      cdf (gaussianReal 0 1) (-a) - cdf (gaussianReal 0 1) (-b) := by
  have hk : 0 ≤ exp (-b ^ 2 / 2) / √(2 * π) := by positivity
  have h : ENNReal.ofReal (exp (-b ^ 2 / 2) / √(2 * π) * (-a - -b)) ≤
      (gaussianReal 0 1) (Ioc (-b) (-a)) := by
    rw [gaussianReal_apply _ one_ne_zero, ENNReal.ofReal_mul hk, ← volume_Ioc,
      ← setLIntegral_const]
    refine setLIntegral_mono (measurable_gaussianPDF _ _) fun y hy ↦ ENNReal.ofReal_le_ofReal ?_
    have hy2 : y ^ 2 ≤ b ^ 2 := by nlinarith [hy.1, hy.2]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [div_eq_inv_mul]
    gcongr
  rw [← measure_cdf (μ := gaussianReal 0 1), StieltjesFunction.measure_Ioc,
    ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 (monotone_cdf _ (by linarith)))] at h
  linarith [show exp (-b ^ 2 / 2) / √(2 * π) * (-a - -b) = (b - a) * exp (-b ^ 2 / 2) / √(2 * π)
    by ring]

/-- `δ(μ, 0) = Φ(μ / 2) - Φ(-μ / 2) ≤ μ / 2`. -/
lemma gaussianDelta_zero_le {μ : ℝ} (hμ : 0 ≤ μ) : gaussianDelta μ 0 ≤ μ / 2 := by
  have h2π : 2 ≤ √(2 * π) := le_sqrt_of_sq_le (by nlinarith [two_le_pi])
  have h := cdf_sub_cdf_le (show -(μ / 2) ≤ μ / 2 by linarith)
  rw [gaussianDelta, zero_div, sub_zero, sub_zero, exp_zero, one_mul]
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Gordon's inequality** (the Mills-ratio bound used in the proof of Theorem 4 of Balle–Wang):
for `t > 0`, `Φ(-t) = P[N(0, 1) > t] ≤ e^{-t² / 2} / (t √(2π))`. -/
lemma cdf_neg_le (t : ℝ) (ht : 0 < t) :
    cdf (gaussianReal 0 1) (-t) ≤ exp (-t ^ 2 / 2) / (t * √(2 * π)) := by
  set c := (√(2 * π))⁻¹
  set φ : ℝ → ℝ := fun y ↦ c * exp (-y ^ 2 / 2)
  have hφ (y : ℝ) : gaussianPDFReal 0 1 y = φ y := by simp [gaussianPDFReal, φ, c]
  set g : ℝ → ℝ := fun y ↦ -φ y
  have hderiv (y : ℝ) : HasDerivAt g (y * φ y) y := by
    have h := (((hasDerivAt_pow 2 y).neg.div_const 2).exp.const_mul c).neg
    convert h using 1
    simp only [φ, Nat.cast_ofNat, Pi.neg_apply, neg_div]
    ring
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h : Tendsto (fun y : ℝ ↦ y ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
    have := ((tendsto_exp_neg_atTop_nhds_zero.comp h).const_mul c).neg
    simpa [g, φ, neg_div, Function.comp_def] using this
  have hpos : ∀ y ∈ Ioi t, 0 ≤ y * φ y := fun y hy ↦
    mul_nonneg (ht.trans hy).le (by positivity)
  have hint := integrableOn_Ioi_deriv_of_nonneg' (fun y _ ↦ hderiv y) hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (fun y _ ↦ hderiv y) hpos hlim
  have hΦ : cdf (gaussianReal 0 1) (-t) = ∫ y in Ioi t, φ y := by
    have h := measureReal_gaussianReal_Ioi 0 one_ne_zero t
    rw [NNReal.coe_one, sqrt_one, div_one, zero_sub, measureReal_def,
      gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
        (setIntegral_nonneg measurableSet_Ioi fun y _ ↦ gaussianPDFReal_nonneg _ _ _)] at h
    simp_rw [← h, hφ]
  have hφint : IntegrableOn φ (Ioi t) := by
    rw [← funext hφ]
    exact (integrable_gaussianPDFReal 0 1).integrableOn
  rw [hΦ]
  calc ∫ y in Ioi t, φ y ≤ ∫ y in Ioi t, t⁻¹ * (y * φ y) :=
        setIntegral_mono_on hφint (hint.const_mul _) measurableSet_Ioi fun y hy ↦ by
          rw [← mul_assoc, le_mul_iff_one_le_left (by positivity), le_inv_mul_iff₀ ht, mul_one]
          exact (mem_Ioi.1 hy).le
    _ = exp (-t ^ 2 / 2) / (t * √(2 * π)) := by
        rw [integral_const_mul, hval]
        simp only [g, φ, c, zero_sub, neg_neg]
        field_simp

/-- A Chernoff-type tail bound: for `t ≥ 0`, `Φ(-t) = P[N(0, 1) > t] ≤ e^{-t² / 2} / 2`. -/
lemma cdf_neg_le_half_exp {t : ℝ} (ht : 0 ≤ t) :
    cdf (gaussianReal 0 1) (-t) ≤ exp (-t ^ 2 / 2) / 2 := by
  have h₁ := measureReal_gaussianReal_Ioi (-t) one_ne_zero 0
  have h₀ := measureReal_gaussianReal_Ioi 0 one_ne_zero 0
  simp only [NNReal.coe_one, sqrt_one, div_one, sub_zero, cdf_zero] at h₁ h₀
  have key : (gaussianReal (-t) 1).real (Ioi 0) ≤
      exp (-t ^ 2 / 2) * (gaussianReal 0 1).real (Ioi 0) := by
    refine measureReal_le_mul_of_le (exp_pos _).le ?_
    rw [gaussianReal_apply _ one_ne_zero, gaussianReal_apply _ one_ne_zero,
      ← lintegral_const_mul _ (measurable_gaussianPDF _ _)]
    refine setLIntegral_mono ((measurable_gaussianPDF _ _).const_mul _) fun u hu ↦ ?_
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (exp_pos _).le,
      gaussianPDFReal_eq_exp_mul (-t) 0 1 u]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (exp_le_exp.2 ?_)
      (gaussianPDFReal_nonneg _ _ _))
    have : 0 < u := hu
    simp only [NNReal.coe_one]
    nlinarith
  rw [← h₁]
  rw [h₀] at key
  linarith

end AnalyticGaussian

/-! ### Consequences: the high- and low-privacy regimes -/

section Regimes

variable {𝒟 : Type*} {m𝒟 : MeasurableSpace 𝒟} {Adj : 𝒟 → 𝒟 → Prop} {q : 𝒟 → ℝ} {v : ℝ≥0}
  {M : Kernel 𝒟 ℝ} {ε δ Δ : ℝ}

open AnalyticGaussian

/-- **Theorem 2** of Balle–Wang (scalar case, `d = 1`): Gaussian noise with `σ ≥ Δ / (2δ)` gives
`(0, δ)`-DP (the paper states `σ = Δ / (2δ)`). Here `Δ > 0` bounds the sensitivity of `q`. The
proof goes through the exact formula, `δ(Δ / σ, 0) = Φ(Δ / (2σ)) - Φ(-Δ / (2σ)) ≤ Δ / (σ √(2π))`,
instead of Pinsker's inequality. -/
theorem isEpsDeltaDP_zero_of_gaussianReal (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ)
    (hΔ : 0 < Δ) (hδ : 0 < δ) (hv : v ≠ 0) (hM : ∀ S, M S = gaussianReal (q S) v)
    (hσ : Δ / (2 * δ) ≤ √(v : ℝ)) : IsEpsDeltaDP M Adj 0 δ := by
  have hσ₀ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  refine isEpsDeltaDP_of_gaussianReal hq hΔ hv hM ((gaussianDelta_zero_le (by positivity)).trans ?_)
  rw [div_le_iff₀ (by positivity)] at hσ
  rw [div_div, div_le_iff₀ (by positivity)]
  linarith

/-- `δ(√(2ε), ε) = Φ(0) - e^ε Φ(-√(2ε)) = 1 / 2 - e^ε Φ(-√(2ε))`, the `δ₀(ε)` of Balle–Wang's
Algorithm 1, the privacy level of the noise scale `σ = Δ / √(2ε)`. -/
lemma gaussianDelta_sqrt_two_mul (hε : 0 < ε) :
    gaussianDelta √(2 * ε) ε = 1 / 2 - exp ε * cdf (gaussianReal 0 1) (-√(2 * ε)) := by
  have hs : 0 < √(2 * ε) := sqrt_pos.2 (by positivity)
  have hsq : √(2 * ε) ^ 2 = 2 * ε := sq_sqrt (by positivity)
  have h₁ : √(2 * ε) / 2 - ε / √(2 * ε) = 0 := by
    field_simp
    linarith
  have h₂ : -(√(2 * ε) / 2) - ε / √(2 * ε) = -√(2 * ε) := by
    field_simp
    linarith
  rw [gaussianDelta, h₁, h₂, cdf_zero]

/-- **Theorem 4** of Balle–Wang, exact form (scalar case, `d = 1`): let `Δ > 0` be the global
sensitivity of `q` and `ε > 0`. If the Gaussian mechanism is `(ε, δ)`-DP with
`δ < δ₀(ε) = Φ(0) - e^ε Φ(-√(2ε))`, then `σ ≥ Δ / √(2ε)`. (This is the argument of the paper's
proof, which reduces Theorem 4 to the bound `δ < δ₀(ε)`.) -/
theorem div_sqrt_le_of_isEpsDeltaDP_gaussianReal (h : IsEpsDeltaDP M Adj ε δ)
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0)
    (hM : ∀ S, M S = gaussianReal (q S) v) (hε : 0 < ε)
    (hδ : δ < 1 / 2 - exp ε * cdf (gaussianReal 0 1) (-√(2 * ε))) :
    Δ / √(2 * ε) ≤ √(v : ℝ) := by
  have hσ₀ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hs : 0 < √(2 * ε) := sqrt_pos.2 (by positivity)
  by_contra hlt
  rw [not_le, lt_div_iff₀ hs, ← lt_div_iff₀' hσ₀] at hlt
  have := (monotoneOn_gaussianDelta ε hs (show (0 : ℝ) < Δ / √(v : ℝ) by positivity)
    hlt.le).trans ((isEpsDeltaDP_gaussianReal_iff hΔ hΔ₀ hv hM).1 h)
  simp only at this
  rw [gaussianDelta_sqrt_two_mul hε] at this
  linarith

/-- The explicit lower bound on `δ₀(ε)` from Gordon's inequality:
`1 / 2 - 1 / √(4πε) ≤ Φ(0) - e^ε Φ(-√(2ε))` for `ε > 0`. -/
lemma AnalyticGaussian.one_half_sub_inv_sqrt_le (hε : 0 < ε) :
    1 / 2 - 1 / √(4 * π * ε) ≤ 1 / 2 - exp ε * cdf (gaussianReal 0 1) (-√(2 * ε)) := by
  have hs : 0 < √(2 * ε) := sqrt_pos.2 (by positivity)
  have h := cdf_neg_le _ hs
  rw [sq_sqrt (by positivity), show -(2 * ε) / 2 = -ε by ring, ← sqrt_mul (by positivity),
    show 2 * ε * (2 * π) = 4 * π * ε by ring] at h
  have h' := mul_le_mul_of_nonneg_left h (exp_pos ε).le
  rw [mul_div_assoc', ← exp_add, add_neg_cancel, exp_zero] at h'
  linarith

/-- **Theorem 4** of Balle–Wang, corrected (scalar case, `d = 1`; see *Notes on the paper*): let
`Δ > 0` be the global sensitivity of `q` and `ε > 0`. If the Gaussian mechanism
`M S = N(q S, σ²)` is `(ε, δ)`-DP with `δ < 1 / 2 - 1 / √(4πε)`, then `σ ≥ Δ / √(2ε)`. With the
paper's bound `δ < 1 / 2 - e^{-3ε} / √(4πε)` the conclusion fails
(`not_forall_div_sqrt_le_of_isEpsDeltaDP_gaussianReal`). -/
theorem div_sqrt_le_of_isEpsDeltaDP_gaussianReal' (h : IsEpsDeltaDP M Adj ε δ)
    (hΔ : IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ) (hΔ₀ : 0 < Δ) (hv : v ≠ 0)
    (hM : ∀ S, M S = gaussianReal (q S) v) (hε : 0 < ε) (hδ : δ < 1 / 2 - 1 / √(4 * π * ε)) :
    Δ / √(2 * ε) ≤ √(v : ℝ) :=
  div_sqrt_le_of_isEpsDeltaDP_gaussianReal h hΔ hΔ₀ hv hM hε
    (hδ.trans_le (one_half_sub_inv_sqrt_le hε))

/-- The classical calibration bound in terms of `δ(μ, ε)`: if `0 < ε < 1`, `0 < δ < 1`,
`c > 0` with `c² ≥ 2 log (1.25 / δ)` and `0 < μ ≤ ε / c`, then `δ(μ, ε) ≤ δ`. -/
lemma gaussianDelta_le_of_classical {μ c : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) (hδ₀ : 0 < δ)
    (hδ₁ : δ < 1) (hc : 0 < c) (hc2 : 2 * log (1.25 / δ) ≤ c ^ 2) (hμ : 0 < μ)
    (hμc : μ ≤ ε / c) : gaussianDelta μ ε ≤ δ := by
  set t := c - ε / (2 * c)
  -- `δ ≥ 1.25 e^{-c² / 2}`
  have hδc : 1.25 * exp (-c ^ 2 / 2) ≤ δ := by
    have h := (log_le_iff_le_exp (by positivity)).1 (show log (1.25 / δ) ≤ c ^ 2 / 2 by linarith)
    rw [div_le_iff₀ hδ₀] at h
    have h' : exp (c ^ 2 / 2) * exp (-c ^ 2 / 2) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
    nlinarith [exp_pos (-c ^ 2 / 2)]
  -- `δ(μ, ε) ≤ Φ(-t)`
  have hle : gaussianDelta μ ε ≤ cdf (gaussianReal 0 1) (-t) := by
    have h₁ : ε / (ε / c) = c := by field_simp
    have h₂ : c ≤ ε / μ := h₁ ▸ div_le_div_of_nonneg_left hε₀.le hμ hμc
    have h₃ : μ / 2 - ε / μ ≤ -t := by
      have : μ / 2 ≤ ε / (2 * c) := by
        rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hc] at hμc; linarith
      simp only [t]; linarith
    rw [gaussianDelta]
    have := mul_nonneg (exp_pos ε).le (cdf_nonneg (gaussianReal 0 1) (-(μ / 2) - ε / μ))
    linarith [monotone_cdf (gaussianReal 0 1) h₃]
  refine hle.trans ?_
  rcases le_or_gt 0 t with ht | ht
  · -- Chernoff-type tail bound: `Φ(-t) ≤ e^{-t² / 2} / 2 ≤ e^{-c² / 2} e^{1 / 2} / 2 ≤ e^{-c² / 2}`
    have ht2 : c ^ 2 - 1 ≤ t ^ 2 := by
      have : t ^ 2 = c ^ 2 - ε + (ε / (2 * c)) ^ 2 := by simp only [t]; field_simp; ring
      nlinarith [sq_nonneg (ε / (2 * c))]
    have he : exp (1 / 2) ≤ 2 := by
      have h := add_one_le_exp (-(1 / 2))
      have h' : exp (1 / 2) * exp (-(1 / 2)) = 1 := by rw [← exp_add]; norm_num
      nlinarith [exp_pos (1 / 2)]
    have hexp : exp (-t ^ 2 / 2) ≤ exp (-c ^ 2 / 2) * exp (1 / 2) := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith)
    have := cdf_neg_le_half_exp ht
    nlinarith [exp_pos (-c ^ 2 / 2)]
  · -- `t < 0` forces `c² < 1 / 2`, hence `δ > 15 / 16`, while `Φ(-t) ≤ 1 / 2 - t / √(2π)`
    have hc2' : 2 * c ^ 2 < ε := by
      simp only [t] at ht
      rw [sub_neg, lt_div_iff₀ (by positivity)] at ht
      linarith
    have hlog : 2 / 5 < c ^ 2 := by
      have h₁ := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.25 / δ by positivity)
      have h₂ : (1.25 / δ)⁻¹ < 4 / 5 := by
        rw [inv_div, div_lt_iff₀ (by norm_num)]; linarith
      linarith
    have hc6 : 3 / 5 < c := by nlinarith
    have hδ' : 15 / 16 < δ := by
      have := add_one_le_exp (-c ^ 2 / 2)
      nlinarith
    have h2π : 2 ≤ √(2 * π) := le_sqrt_of_sq_le (by nlinarith [two_le_pi])
    have h := cdf_sub_cdf_le (show (0 : ℝ) ≤ -t by linarith)
    rw [cdf_zero, sub_zero] at h
    have h' : -t / √(2 * π) ≤ -t / 2 := div_le_div_of_nonneg_left (by linarith) two_pos h2π
    have h'' : ε / (2 * c) ≤ 5 / 6 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    simp only [t] at h h' ⊢
    linarith

/-- A certified numerical bound: `δ(3 / 2, 1) ≤ 0.47` (the true value is `≈ 0.320`). -/
lemma AnalyticGaussian.gaussianDelta_three_halves_one_le : gaussianDelta (3 / 2) 1 ≤ 47 / 100 := by
  have h2π : 2 ≤ √(2 * π) := le_sqrt_of_sq_le (by nlinarith [two_le_pi])
  have h2π' : √(2 * π) ≤ 2.51 := (sqrt_le_left (by norm_num)).2 (by nlinarith [pi_lt_d2])
  -- `Φ(1 / 12) ≤ 1 / 2 + 1 / 24`
  have hup : cdf (gaussianReal 0 1) (1 / 12) ≤ 1 / 2 + 1 / 24 := by
    have h := cdf_sub_cdf_le (show (0 : ℝ) ≤ 1 / 12 by norm_num)
    rw [cdf_zero, sub_zero] at h
    have : 1 / 12 / √(2 * π) ≤ 1 / 24 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  -- `e Φ(-17 / 12) ≥ e^{-241 / 288} / (4 √(2π)) ≥ 0.085`
  have hlow : 0.085 ≤ exp 1 * cdf (gaussianReal 0 1) (-(17 / 12)) := by
    have h := mul_exp_div_le_cdf_neg_sub (a := 17 / 12) (b := 23 / 12) (by norm_num) (by norm_num)
    have h0 := cdf_nonneg (gaussianReal 0 1) (-(23 / 12))
    have he : exp 1 * exp (-(23 / 12) ^ 2 / 2) = exp (-1) * exp (47 / 288) := by
      rw [← exp_add, ← exp_add]; norm_num
    have he' : 0.36787944116 * (47 / 288 + 1) ≤ exp (-1) * exp (47 / 288) :=
      mul_le_mul exp_neg_one_gt_d9.le (add_one_le_exp _) (by norm_num) (exp_pos _).le
    have hk : 0.085 * √(2 * π) ≤ (23 / 12 - 17 / 12) * (exp 1 * exp (-(23 / 12) ^ 2 / 2)) := by
      rw [he]; nlinarith
    have hk' : 0.085 ≤ exp 1 * ((23 / 12 - 17 / 12) * exp (-(23 / 12) ^ 2 / 2) / √(2 * π)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; linarith
    nlinarith [exp_pos 1]
  rw [gaussianDelta, show (3 / 2 : ℝ) / 2 - 1 / (3 / 2) = 1 / 12 by norm_num,
    show -((3 / 2 : ℝ) / 2) - 1 / (3 / 2) = -(17 / 12) by norm_num]
  linarith

/-- **Theorem 4 of Balle–Wang, as printed (arXiv v2), is false.** Its hypotheses are `ε > 0` and
`0 < δ < 1 / 2 - e^{-3ε} / √(4πε)`, and its conclusion for an `(ε, δ)`-DP Gaussian mechanism is
`σ ≥ Δ / √(2ε)`; the paper assumes a symmetric neighbouring relation, and so does the negated
statement (`Std.Symm Adj`). Counterexample (datasets `ℝ`, `q = id`, the symmetric neighbouring
relation `{(1, 0), (0, 1)}`, so `Δ = 1`): `ε = 1`, `δ = 0.47 < 1 / 2 - e^{-3} / √(4π) ≈ 0.486`
and `σ = 2 / 3 < 1 / √2`; the mechanism is `(1, 0.47)`-DP since `δ(3 / 2, 1) ≈ 0.320 ≤ 0.47`
(`AnalyticGaussian.gaussianDelta_three_halves_one_le`, a certified bound). -/
theorem not_forall_div_sqrt_le_of_isEpsDeltaDP_gaussianReal :
    ¬ ∀ (q : ℝ → ℝ) (Adj : ℝ → ℝ → Prop) (v : ℝ≥0) (M : Kernel ℝ ℝ) (ε δ Δ : ℝ),
      Std.Symm Adj → IsLUB {d | ∃ S S', Adj S S' ∧ |q S - q S'| = d} Δ → 0 < Δ → v ≠ 0 →
      (∀ S, M S = gaussianReal (q S) v) → 0 < ε → 0 < δ →
      δ < 1 / 2 - exp (-3 * ε) / √(4 * π * ε) → IsEpsDeltaDP M Adj ε δ →
      Δ / √(2 * ε) ≤ √(v : ℝ) := by
  intro H
  have hσ : √(((4 / 9 : ℝ≥0) : ℝ)) = 2 / 3 := by
    rw [NNReal.coe_div, show (((4 : ℝ≥0) : ℝ) / ((9 : ℝ≥0) : ℝ)) = (2 / 3) ^ 2 by norm_num,
      sqrt_sq (by norm_num)]
  have hv : (4 / 9 : ℝ≥0) ≠ 0 := by positivity
  set Adj : ℝ → ℝ → Prop := fun S S' ↦ (S = 1 ∧ S' = 0) ∨ (S = 0 ∧ S' = 1)
  have hsymm : Std.Symm Adj := ⟨fun _ _ h ↦ h.symm.imp (fun h ↦ h.symm) fun h ↦ h.symm⟩
  have hset : {d | ∃ S S' : ℝ, Adj S S' ∧ |id S - id S'| = d} = {1} := by
    ext d
    constructor
    · rintro ⟨S, S', h, rfl⟩
      rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂]
    · rintro rfl; exact ⟨1, 0, Or.inl ⟨rfl, rfl⟩, by norm_num⟩
  have hpaper : (47 / 100 : ℝ) < 1 / 2 - exp (-3 * 1) / √(4 * π * 1) := by
    rw [mul_one, mul_one]
    have h3 : 20 ≤ exp 3 := by
      have := exp_one_gt_d9
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, exp_add, exp_add]
      nlinarith [exp_pos 1]
    have h4π : 2 ≤ √(4 * π) := le_sqrt_of_sq_le (by nlinarith [two_le_pi])
    have e3 : exp (-3) * 20 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left h3 (exp_pos (-3)).le
      rwa [← exp_add, neg_add_cancel, exp_zero] at h
    have : exp (-3) / √(4 * π) ≤ 1 / 40 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hDP : IsEpsDeltaDP (ZCDP.gaussianKernel id measurable_id (4 / 9)) Adj 1 (47 / 100) := by
    refine isEpsDeltaDP_of_gaussianReal (Δ := 1) ?_ one_pos hv (fun _ ↦ rfl) ?_
    · rintro S S' (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> simp [h₁, h₂]
    · rw [hσ, show (1 : ℝ) / (2 / 3) = 3 / 2 by norm_num]
      exact AnalyticGaussian.gaussianDelta_three_halves_one_le
  have key := H id Adj (4 / 9) _ 1 (47 / 100) 1 hsymm (hset ▸ isLUB_singleton) one_pos hv
    (fun _ ↦ rfl) one_pos (by norm_num) hpaper hDP
  rw [hσ, mul_one, div_le_iff₀ (by positivity)] at key
  have : √2 < 3 / 2 := (sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

/-- **Theorem A.1** of Dwork–Roth (the classical Gaussian mechanism, Theorem 1 of Balle–Wang),
scalar case, `d = 1`: let `0 < ε < 1`, `δ > 0` and `c > 0` with `c² > 2 log (1.25 / δ)`. If
`Δ > 0` bounds the sensitivity of `q` and `σ ≥ c Δ / ε`, the Gaussian mechanism
`M S = N(q S, σ²)` is `(ε, δ)`-DP. Proved from the exact characterization (Theorem 8 of
Balle–Wang) and Gaussian tail bounds rather than through the privacy-loss tail bound of
Dwork–Roth. -/
theorem isEpsDeltaDP_gaussianReal_classical (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ)
    (hΔ : 0 < Δ) (hv : v ≠ 0) (hM : ∀ S, M S = gaussianReal (q S) v) (hε₀ : 0 < ε)
    (hε₁ : ε < 1) (hδ : 0 < δ) {c : ℝ} (hc : 0 < c) (hc2 : 2 * log (1.25 / δ) < c ^ 2)
    (hσ : c * Δ / ε ≤ √(v : ℝ)) : IsEpsDeltaDP M Adj ε δ := by
  have hσ₀ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  refine isEpsDeltaDP_of_gaussianReal hq hΔ hv hM ?_
  rcases lt_or_ge δ 1 with hδ₁ | hδ₁
  · refine gaussianDelta_le_of_classical hε₀ hε₁ hδ hδ₁ hc hc2.le (by positivity) ?_
    rw [div_le_iff₀ hε₀] at hσ
    rw [div_le_div_iff₀ hσ₀ hc]
    linarith
  · exact (gaussianDelta_le_one (by positivity)).trans hδ₁

/-- **Theorem 1** of Balle–Wang (the classical Gaussian mechanism in their formulation), scalar
case, `d = 1`: for
`ε, δ ∈ (0, 1)` and a query of sensitivity at most `Δ > 0`, the Gaussian mechanism with
`σ ≥ Δ √(2 log (1.25 / δ)) / ε` is `(ε, δ)`-DP (the paper takes `σ` equal to this value). -/
theorem isEpsDeltaDP_gaussianReal_classical' (hq : ∀ ⦃S S'⦄, Adj S S' → |q S - q S'| ≤ Δ)
    (hΔ : 0 < Δ) (hv : v ≠ 0) (hM : ∀ S, M S = gaussianReal (q S) v) (hε₀ : 0 < ε)
    (hε₁ : ε < 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hσ : Δ * √(2 * log (1.25 / δ)) / ε ≤ √(v : ℝ)) : IsEpsDeltaDP M Adj ε δ := by
  have hσ₀ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hlog : 0 < log (1.25 / δ) := log_pos (by rw [lt_div_iff₀ hδ₀]; linarith)
  have hc : 0 < √(2 * log (1.25 / δ)) := sqrt_pos.2 (by positivity)
  refine isEpsDeltaDP_of_gaussianReal hq hΔ hv hM (gaussianDelta_le_of_classical hε₀ hε₁ hδ₀ hδ₁ hc
    (sq_sqrt (by positivity)).ge (by positivity) ?_)
  rw [div_le_iff₀ hε₀] at hσ
  rw [div_le_div_iff₀ hσ₀ hc]
  linarith

end Regimes

/-! ### The privacy loss random variable -/

section PrivacyLoss

open AnalyticGaussian

/-- **Lemma 3** of Balle–Wang (scalar case): the privacy loss `L = log (p₁(Y) / p₂(Y))` of
`N(m₁, σ²)` against `N(m₂, σ²)`, with `Y ∼ N(m₁, σ²)`, is distributed as `N(η, 2η)` with
`η = μ² / 2` and `μ = (m₁ - m₂) / σ` (i.e. `η = D² / (2σ²)` with `D = |m₁ - m₂|`). -/
theorem map_log_gaussianPDFReal_div (m₁ m₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m₁ v).map (fun y ↦ log (gaussianPDFReal m₁ v y / gaussianPDFReal m₂ v y)) =
      gaussianReal (((m₁ - m₂) / √(v : ℝ)) ^ 2 / 2) (((m₁ - m₂) / √(v : ℝ)) ^ 2).toNNReal := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  set a := (m₁ - m₂) / (v : ℝ)
  set b := -((m₁ - m₂) * (m₁ + m₂) / (2 * v))
  have hf : (fun y ↦ log (gaussianPDFReal m₁ v y / gaussianPDFReal m₂ v y)) =
      (· + b) ∘ (a * ·) := by
    ext y
    rw [gaussianPDFReal_eq_exp_mul m₁ m₂ v y,
      mul_div_cancel_right₀ _ (gaussianPDFReal_pos _ _ _ hv).ne', log_exp]
    simp only [Function.comp_apply, a, b]
    field_simp
    ring
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  have hsq : √(v : ℝ) ^ 2 = v := sq_sqrt v.coe_nonneg
  congr 1
  · simp only [a, b, div_pow, hsq]
    field_simp
    ring
  · ext
    rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg _)]
    simp only [a, div_pow, hsq]
    field_simp

/-- **Lemma 6** of Balle–Wang, equation (4): for `μ > 0` and `L ∼ N(μ² / 2, μ²)`,
`P[L ≥ ε] = Φ(μ / 2 - ε / μ)` (with `μ = D / σ`, this is `Φ(D / (2σ) - ε σ / D)`). -/
theorem measureReal_gaussianReal_Ici_privacyLoss {μ : ℝ} (hμ : 0 < μ) (ε : ℝ) :
    (gaussianReal (μ ^ 2 / 2) (μ ^ 2).toNNReal).real (Ici ε) =
      cdf (gaussianReal 0 1) (μ / 2 - ε / μ) := by
  have hv : (μ ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have := nullSingletonClass_gaussianReal (μ := μ ^ 2 / 2) hv
  rw [measureReal_congr Ioi_ae_eq_Ici.symm, measureReal_gaussianReal_Ioi _ hv,
    Real.coe_toNNReal _ (sq_nonneg _), sqrt_sq hμ.le]
  congr 1
  field_simp

/-- **Lemma 6** of Balle–Wang, equation (5): for `μ > 0` and `L' ∼ N(μ² / 2, μ²)`,
`P[L' ≤ -ε] = Φ(-μ / 2 - ε / μ)` (with `μ = D / σ`, this is `Φ(-D / (2σ) - ε σ / D)`). -/
theorem measureReal_gaussianReal_Iic_privacyLoss {μ : ℝ} (hμ : 0 < μ) (ε : ℝ) :
    (gaussianReal (μ ^ 2 / 2) (μ ^ 2).toNNReal).real (Iic (-ε)) =
      cdf (gaussianReal 0 1) (-(μ / 2) - ε / μ) := by
  have hv : (μ ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  rw [← cdf_eq_real, cdf_gaussianReal _ hv,
    Real.coe_toNNReal _ (sq_nonneg _), sqrt_sq hμ.le]
  congr 1
  field_simp
  ring

/-- **Lemma 6** of Balle–Wang, equation (4), for the mechanism's privacy loss: if
`M(x) = N(m₁, σ²)`, `M(x') = N(m₂, σ²)` with `D = |m₁ - m₂| > 0` and
`L_{M,x,x'}(y) = log (p₁(y) / p₂(y))`, then
`P_{Y ∼ M(x)}[L_{M,x,x'}(Y) ≥ ε] = Φ(D / (2σ) - ε σ / D)`. -/
theorem measureReal_privacyLoss_ge {m₁ m₂ : ℝ} (h : m₁ ≠ m₂) {v : ℝ≥0} (hv : v ≠ 0) (ε : ℝ) :
    (gaussianReal m₁ v).real {y | ε ≤ log (gaussianPDFReal m₁ v y / gaussianPDFReal m₂ v y)} =
      cdf (gaussianReal 0 1)
        (|m₁ - m₂| / (2 * √(v : ℝ)) - ε * √(v : ℝ) / |m₁ - m₂|) := by
  have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hμ : 0 < |m₁ - m₂| / √(v : ℝ) := div_pos (abs_pos.2 (sub_ne_zero.2 h)) hσ
  have hpre : {y | ε ≤ log (gaussianPDFReal m₁ v y / gaussianPDFReal m₂ v y)} =
      (fun y ↦ log (gaussianPDFReal m₁ v y / gaussianPDFReal m₂ v y)) ⁻¹' Ici ε := rfl
  rw [hpre, ← map_measureReal_apply (by fun_prop) measurableSet_Ici,
    map_log_gaussianPDFReal_div m₁ m₂ hv, div_pow, ← sq_abs, ← div_pow,
    measureReal_gaussianReal_Ici_privacyLoss hμ, div_div, mul_comm (√(v : ℝ)) 2,
    div_div_eq_mul_div]

/-- **Lemma 6** of Balle–Wang, equation (5), for the mechanism's privacy loss: if
`M(x) = N(m₁, σ²)`, `M(x') = N(m₂, σ²)` with `D = |m₁ - m₂| > 0` and
`L_{M,x',x}(y) = log (p₂(y) / p₁(y))`, then
`P_{Y' ∼ M(x')}[L_{M,x',x}(Y') ≤ -ε] = Φ(-D / (2σ) - ε σ / D)`. -/
theorem measureReal_privacyLoss_le {m₁ m₂ : ℝ} (h : m₁ ≠ m₂) {v : ℝ≥0} (hv : v ≠ 0) (ε : ℝ) :
    (gaussianReal m₂ v).real {y | log (gaussianPDFReal m₂ v y / gaussianPDFReal m₁ v y) ≤ -ε} =
      cdf (gaussianReal 0 1)
        (-(|m₁ - m₂| / (2 * √(v : ℝ))) - ε * √(v : ℝ) / |m₁ - m₂|) := by
  have hσ : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hμ : 0 < |m₂ - m₁| / √(v : ℝ) := div_pos (abs_pos.2 (sub_ne_zero.2 h.symm)) hσ
  have hpre : {y | log (gaussianPDFReal m₂ v y / gaussianPDFReal m₁ v y) ≤ -ε} =
      (fun y ↦ log (gaussianPDFReal m₂ v y / gaussianPDFReal m₁ v y)) ⁻¹' Iic (-ε) := rfl
  rw [hpre, ← map_measureReal_apply (by fun_prop) measurableSet_Iic,
    map_log_gaussianPDFReal_div m₂ m₁ hv, div_pow, ← sq_abs, ← div_pow,
    measureReal_gaussianReal_Iic_privacyLoss hμ, abs_sub_comm, div_div, mul_comm (√(v : ℝ)) 2,
    div_div_eq_mul_div]

end PrivacyLoss

end InformationTheory
