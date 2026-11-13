/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.RenyiDP.Basic

/-!
# An improved conversion from Rényi to `(ε, δ)`-differential privacy

This file formalizes the conversion law of B. Balle, G. Barthe, M. Gaboardi, J. Hsu and T. Sato,
*Hypothesis testing interpretations and Rényi differential privacy*, AISTATS 2020
([arXiv:1905.09982](https://arxiv.org/abs/1905.09982)); result numbers follow arXiv v2
(Section 5.1.1).

Mironov's conversion (Lemma 20 of the paper, Proposition 3 of Mironov, formalized as
`IsRenyiDP.isEpsDeltaDP`) turns an `(α, ρ)`-RDP mechanism into an
`(ρ + log (1 / δ) / (α - 1), δ)`-DP one. Balle et al. observe that its proof first establishes
`P(E) ≤ (e^ρ Q(E)) ^ ((α - 1) / α)` (the step `(†)` of the paper, which is Mironov's
Proposition 10, `RenyiDP.measure_le_rpow_of_renyiDiv_le`) and then bounds the concave function
`z ↦ z ^ ((α - 1) / α)` crudely; bounding it instead by a tangent line gives the better law
(Theorem 21) `(α, ρ)`-RDP `⇒ (ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1), δ)`-DP.
The same bound is Proposition 12 of C. Canonne, G. Kamath and T. Steinke, *The discrete Gaussian
for differential privacy* ([arXiv:2004.00010](https://arxiv.org/abs/2004.00010), v6), and the
first term of Lemma 1 of S. Asoodeh, J. Liao, F. Calmon, O. Kosut and L. Sankar, *Three variants
of differential privacy: lossless conversion and applications*
([arXiv:2008.06529](https://arxiv.org/abs/2008.06529)), who write it as
`ρ - log (δ / ζ_α) / (α - 1)` with `ζ_α = α⁻¹ (1 - α⁻¹) ^ (α - 1)`. The further conversions of
Asoodeh et al. are in `InfoLeakage.RDPConversion.Lossless`.

**Scope.** Mechanisms are Markov kernels `M : Kernel 𝒟 Y` into an arbitrary measurable space,
the Rényi divergence is Statlib's `renyiDiv`, `(α, ρ)`-RDP is `IsRenyiDP` and `(ε, δ)`-DP is
`IsEpsDeltaDP`; the neighbouring relation is arbitrary.

## Main definitions

* `RDPConversion.zeta α`: the constant `ζ_α = α⁻¹ (1 - α⁻¹) ^ (α - 1)` of Asoodeh et al.

## Main statements (paper result → Lean name)

* Theorem 21 (improved conversion law) → `IsRenyiDP.isEpsDeltaDP_improved`; for probability
  measures, `RDPConversion.measureReal_le_of_renyiDiv_le`.
* The tangent-line step of the proof of Theorem 21 → `RDPConversion.rpow_le_mul_add`.
* The privacy region `R_{D_α}(ρ)` of the Rényi divergence (Section 5.1.1), in the direction
  "`D_α(P ‖ Q) ≤ ρ` implies that every deterministic test lands in `R_{D_α}(ρ)`" (one half of the
  unnumbered reformulation of Theorem 18 for quasi-convex divergences, stated just before
  Corollary 19, applied to `D_α`) → `RDPConversion.sum_rpow_mul_rpow_le_of_renyiDiv_le`.
  Deterministic tests only; randomized tests (Theorem 18) and the converse are not formalized.
* Lemma 20 (Mironov's Proposition 3) is `IsRenyiDP.isEpsDeltaDP`. Theorem 21 gives a strictly
  smaller `ε` for every `α > 1` (meaningful for `0 < δ < 1`;
  `RDPConversion.improvedEps_lt_mironovEps`, by the margin
  `log (α / (α - 1)) + log α / (α - 1)`), and recovers it
  (`IsRenyiDP.isEpsDeltaDP_of_isEpsDeltaDP_improved`).
* Theorem 21 in the form `ρ - log (δ / ζ_α) / (α - 1)` quoted by Asoodeh et al. (Lemma 1, first
  term of (25)) → `RDPConversion.log_div_zeta_div` and `IsRenyiDP.isEpsDeltaDP_zeta`; at a fixed
  `ε`, `δ = ζ_α e^{(α - 1)(ρ - ε)}` (Proposition 12 of Canonne et al., and the lower bound `g` of
  Theorem 4 of Asoodeh et al.) → `IsRenyiDP.isEpsDeltaDP_zeta_mul_exp`, which improves the
  fixed-`ε` form `δ = e^{(α - 1)(ρ - ε)}` of Mironov's conversion (Theorem 1 of Asoodeh et al.,
  `IsRenyiDP.isEpsDeltaDP_exp_mul`) by the factor `ζ_α < 1` (`RDPConversion.zeta_lt_one`).

## Implementation notes

* The RDP parameter is `ρ : ℝ≥0`, as in `IsRenyiDP`; `δ` is a real number and the statements
  assume `δ > 0` (the paper states Theorem 21 for `0 < δ < 1`; the proof does not use `δ < 1`).
* The paper finds the tangent of the curve `1 - x = (e^ρ y) ^ ((α - 1) / α)` that meets the
  line `1 - x = e^ε y + δ`; here the tangent-line inequality is the weighted
  arithmetic-geometric mean inequality `z ^ p t ^ (1 - p) ≤ p z + (1 - p) t` with
  `p = (α - 1) / α` and `t = (α δ) ^ (α / (α - 1))`.
* The paper's conjecture that the tangents of the boundary of `R_{D_α}(ρ)` give the optimal
  conversion law is not formalized; the optimal law in the regime `α δ ≥ 1` is in
  `InfoLeakage.RDPConversion.Lossless`.

## Notes on the paper

* Section 5.1.1, the chain of implications after the privacy region (arXiv v2, p. 12): the
  exponent is printed `ρ - log d / (α - 1)` (twice); `d` is a misprint for `δ`, as in the
  statement of Lemma 20. The derivation and Theorem 21 are correct.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {𝒟 Y : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}

namespace RDPConversion

/-- The tangent-line inequality behind Theorem 21 of Balle et al.: for `α > 1`, `δ > 0` and
`z ≥ 0`, `z ^ ((α - 1) / α) ≤ e^{log ((α - 1) / α) - (log δ + log α) / (α - 1)} z + δ`. The right
side is the tangent line of the concave function `z ↦ z ^ ((α - 1) / α)` with intercept `δ`. -/
lemma rpow_le_mul_add {α δ z : ℝ} (hα : 1 < α) (hδ : 0 < δ) (hz : 0 ≤ z) :
    z ^ ((α - 1) / α) ≤ exp (log ((α - 1) / α) - (log δ + log α) / (α - 1)) * z + δ := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  set p := (α - 1) / α with hp
  set a := (log δ + log α) / (α - 1) with ha
  have hp0 : 0 < p := by positivity
  have hq : 0 ≤ 1 - p := by
    rw [hp, sub_nonneg, div_le_one hα0]
    linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hp0.le hq hz (exp_pos (α * a)).le
    (add_sub_cancel p 1)
  have h1 : exp (α * a) ^ (1 - p) = exp a := by
    rw [← Real.exp_mul]
    congr 1
    rw [hp]
    field_simp
    ring
  have h2 : exp ((α - 1) * a) = α * δ := by
    rw [ha, mul_div_cancel₀ _ hα1.ne', exp_add, exp_log hδ, exp_log hα0, mul_comm]
  have h3 : (1 - p) * exp (α * a) = exp a * δ := by
    have : exp (α * a) = exp a * exp ((α - 1) * a) := by
      rw [← exp_add]
      ring_nf
    rw [this, h2, hp]
    field_simp
    ring
  rw [h1, h3] at hamgm
  have h4 : exp (log p - a) = p * exp (-a) := by
    rw [sub_eq_add_neg, exp_add, exp_log hp0]
  rw [h4]
  calc z ^ p = z ^ p * exp a * exp (-a) := by
        rw [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
    _ ≤ (p * z + exp a * δ) * exp (-a) := by gcongr
    _ = p * exp (-a) * z + δ := by
        rw [exp_neg]
        field_simp

/-- **Theorem 21** of Balle et al. for probability measures: if `D_α(P ‖ Q) ≤ ρ` with `α > 1`,
then for every `δ > 0` and every set `E`,
`P(E) ≤ e^ε Q(E) + δ` with `ε = ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1)`. -/
theorem measureReal_le_of_renyiDiv_le {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α ρ δ : ℝ} (hα : 1 < α) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (h : renyiDiv α P Q ≤ ENNReal.ofReal ρ) (E : Set Y) :
    P.real E ≤ exp (ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1)) * Q.real E + δ := by
  have h1 := ENNReal.toReal_mono (by finiteness)
    (RenyiDP.measure_le_rpow_of_renyiDiv_le hα hρ h E)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at h1
  refine h1.trans ((rpow_le_mul_add hα hδ (by positivity)).trans_eq ?_)
  rw [← mul_assoc, ← exp_add, measureReal_def]
  ring_nf

/-- The **privacy region** of the Rényi divergence (Section 5.1.1 of Balle et al.): if
`D_α(P ‖ Q) ≤ ρ` with `α > 1`, then for every measurable set `E` the pair
`(x, y) = (P(Eᶜ), Q(E))` (the deterministic test `S = Eᶜ` in the unnumbered reformulation of
Theorem 18 stated just before Corollary 19) lies in
`R_{D_α}(ρ) = {(x, y) | x ^ α (1 - y) ^ (1 - α) + (1 - x) ^ α y ^ (1 - α) ≤ e^{ρ (α - 1)}}`.
As in the paper, `0 ^ (1 - α) = 0` (this is also Mathlib's convention). With this convention the
displayed set is only an outer approximation of the set of attainable pairs: for instance
`(x, y) = (0, 0)` satisfies the inequality, but `Q(E) = 0 < 1 = P(E)` forces
`D_α(P ‖ Q) = ∞`. Attainable pairs also satisfy `y = 0 → x = 1` and `y = 1 → x = 0` (absolute
continuity); the theorem proves only the displayed inequality. The step `(†)` of the proof of
Theorem 21 drops the first term. Deterministic tests only; randomized tests (Theorem 18) and the
converse are not formalized. -/
theorem sum_rpow_mul_rpow_le_of_renyiDiv_le {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α ρ : ℝ} (hα : 1 < α) (hρ : 0 ≤ ρ)
    (h : renyiDiv α P Q ≤ ENNReal.ofReal ρ) {E : Set Y} (hE : MeasurableSet E) :
    P.real Eᶜ ^ α * Q.real Eᶜ ^ (1 - α) + P.real E ^ α * Q.real E ^ (1 - α) ≤
      exp (ρ * (α - 1)) := by
  classical
  have hα1 : 0 < α - 1 := by linarith
  set f : Y → Bool := fun y ↦ decide (y ∈ E) with hfdef
  have hpre (b : Bool) : f ⁻¹' {b} = if b then E else Eᶜ := by
    ext y
    cases b <;> simp [hfdef]
  have hf : Measurable f := measurable_to_countable' fun b ↦ by
    rw [hpre]
    cases b
    · exact hE.compl
    · exact hE
  have h' : renyiDiv α (P.map f) (Q.map f) ≤ ENNReal.ofReal ρ :=
    (renyiDiv_map_le (by linarith) P Q hf).trans h
  obtain ⟨hac, -⟩ := (RenyiDP.renyiDiv_le_ofReal_iff_lintegral hα hρ).1 h'
  rw [RenyiDP.renyiDiv_eq_ofReal_log_sum hα hac, ENNReal.ofReal_le_ofReal_iff hρ,
    inv_mul_le_iff₀ hα1, Fintype.sum_bool, map_measureReal_apply hf (measurableSet_singleton _),
    map_measureReal_apply hf (measurableSet_singleton _),
    map_measureReal_apply hf (measurableSet_singleton _),
    map_measureReal_apply hf (measurableSet_singleton _), hpre, hpre] at h'
  simp only [ite_true, Bool.false_eq_true, ite_false] at h'
  have hS : 0 ≤ P.real Eᶜ ^ α * Q.real Eᶜ ^ (1 - α) + P.real E ^ α * Q.real E ^ (1 - α) := by
    positivity
  rcases hS.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact (exp_pos _).le
  · rw [add_comm] at h'
    rw [mul_comm ρ]
    exact (log_le_iff_le_exp hpos).1 h'

/-- The constant `ζ_α = α⁻¹ (1 - α⁻¹) ^ (α - 1)` of Theorem 4 and Lemma 1 of Asoodeh,
Liao, Calmon, Kosut and Sankar, in which Theorem 21 of Balle et al. reads
`ε = ρ - log (δ / ζ_α) / (α - 1)`. -/
noncomputable def zeta (α : ℝ) : ℝ := α⁻¹ * (1 - α⁻¹) ^ (α - 1)

/-- `ζ_α > 0` for `α > 1`. -/
lemma zeta_pos {α : ℝ} (hα : 1 < α) : 0 < zeta α := by
  have : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have : 0 < 1 - α⁻¹ := by linarith
  unfold zeta
  positivity

/-- `ζ_α < 1` for `α > 1`. -/
lemma zeta_lt_one {α : ℝ} (hα : 1 < α) : zeta α < 1 := by
  have hi : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hi0 : 0 < α⁻¹ := inv_pos.2 (by linarith)
  have h1 : (1 - α⁻¹) ^ (α - 1) ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  calc zeta α = α⁻¹ * (1 - α⁻¹) ^ (α - 1) := rfl
    _ ≤ α⁻¹ * 1 := by gcongr
    _ < 1 := by rwa [mul_one]

/-- `log (δ / ζ_α) / (α - 1) = (log δ + log α) / (α - 1) - log ((α - 1) / α)`: the exponent of
Theorem 21 of Balle et al. in the form of Asoodeh et al. -/
lemma log_div_zeta_div {α δ : ℝ} (hα : 1 < α) (hδ : 0 < δ) :
    log (δ / zeta α) / (α - 1) = (log δ + log α) / (α - 1) - log ((α - 1) / α) := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  have h1 : 1 - α⁻¹ = (α - 1) / α := by field_simp
  rw [Real.log_div hδ.ne' (zeta_pos hα).ne', zeta, h1, Real.log_mul (inv_pos.2 hα0).ne'
    (by positivity), Real.log_inv, Real.log_rpow (by positivity)]
  field_simp
  ring

/-- Theorem 21 of Balle et al. gives a strictly smaller `ε` than Mironov's Proposition 3
(Lemma 20 of the paper) for every `α > 1`:
`ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1) < ρ + log (1 / δ) / (α - 1)`. The gap is
`log (α / (α - 1)) + log α / (α - 1)`, independent of `ρ` and `δ`. The comparison is meaningful
for `0 < δ < 1`; it is stated for every real `δ` since both sides contain `log δ` in the same
way (for `δ ≤ 0`, `Real.log` returns junk values). -/
theorem improvedEps_lt_mironovEps {α : ℝ} (hα : 1 < α) (ρ δ : ℝ) :
    ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1) < ρ + log (1 / δ) / (α - 1) := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  have h1 : log ((α - 1) / α) < 0 :=
    Real.log_neg (by positivity) ((div_lt_one hα0).2 (by linarith))
  have h2 : 0 < log α / (α - 1) := div_pos (Real.log_pos hα) hα1
  rw [one_div, Real.log_inv, add_div, neg_div]
  linarith

end RDPConversion

open RDPConversion

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {α : ℝ} {ρ : ℝ≥0}

/-- **Theorem 21** of Balle, Barthe, Gaboardi, Hsu and Sato (improved conversion from RDP to
`(ε, δ)`-DP): an `(α, ρ)`-RDP mechanism with `α > 1` is
`(ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1), δ)`-DP for every `δ > 0`. The paper states
it for `0 < δ < 1`. -/
theorem IsRenyiDP.isEpsDeltaDP_improved [IsMarkovKernel M] (h : IsRenyiDP M Adj α ρ)
    (hα : 1 < α) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (ρ + log ((α - 1) / α) - (log δ + log α) / (α - 1)) δ :=
  fun _ _ hS E ↦ measureReal_le_of_renyiDiv_le hα ρ.coe_nonneg hδ (by simpa using h hS) E

/-- Theorem 21 of Balle et al. recovers Mironov's conversion (Proposition 3 of Mironov, Lemma 20
of the paper, `IsRenyiDP.isEpsDeltaDP`), since its `ε` is smaller
(`RDPConversion.improvedEps_lt_mironovEps`). -/
theorem IsRenyiDP.isEpsDeltaDP_of_isEpsDeltaDP_improved [IsMarkovKernel M]
    (h : IsRenyiDP M Adj α ρ) (hα : 1 < α) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (ρ + log (1 / δ) / (α - 1)) δ :=
  (h.isEpsDeltaDP_improved hα hδ).mono (improvedEps_lt_mironovEps hα _ _).le le_rfl

/-- Theorem 21 of Balle et al. in the form quoted by Asoodeh et al. (Lemma 1, first term of
equation (25)): an `(α, ρ)`-RDP mechanism with `α > 1` is `(ρ - log (δ / ζ_α) / (α - 1), δ)`-DP
for every `δ > 0`. -/
theorem IsRenyiDP.isEpsDeltaDP_zeta [IsMarkovKernel M] (h : IsRenyiDP M Adj α ρ) (hα : 1 < α)
    {δ : ℝ} (hδ : 0 < δ) : IsEpsDeltaDP M Adj (ρ - log (δ / zeta α) / (α - 1)) δ := by
  convert h.isEpsDeltaDP_improved hα hδ using 1
  rw [log_div_zeta_div hα hδ]
  ring

/-- Theorem 21 of Balle et al. at a fixed `ε`, i.e. Proposition 12 of Canonne, Kamath and
Steinke and the bound `γ ≥ g(α, ε, δ)` of Theorem 4 of Asoodeh et al.: an `(α, ρ)`-RDP mechanism
with `α > 1` is `(ε, ζ_α e^{(α - 1)(ρ - ε)})`-DP for every real `ε`. Mironov's conversion gives
`δ = e^{(α - 1)(ρ - ε)}` (Theorem 1 of Asoodeh et al.); here `ζ_α < 1`
(`RDPConversion.zeta_lt_one`). -/
theorem IsRenyiDP.isEpsDeltaDP_zeta_mul_exp [IsMarkovKernel M] (h : IsRenyiDP M Adj α ρ)
    (hα : 1 < α) (ε : ℝ) : IsEpsDeltaDP M Adj ε (zeta α * exp ((α - 1) * (ρ - ε))) := by
  have hα1 : 0 < α - 1 := by linarith
  have hδ : 0 < zeta α * exp ((α - 1) * (ρ - ε)) := mul_pos (zeta_pos hα) (exp_pos _)
  convert h.isEpsDeltaDP_zeta hα hδ using 1
  rw [mul_div_cancel_left₀ _ (zeta_pos hα).ne', log_exp, mul_div_cancel_left₀ _ hα1.ne']
  ring

/-- Mironov's conversion at a fixed `ε` (Theorem 1 of Asoodeh et al., Theorem 2 of Abadi et al.):
an `(α, ρ)`-RDP mechanism with `α > 1` is `(ε, e^{(α - 1)(ρ - ε)})`-DP for every real `ε` (the
paper states it for `ε > ρ`). It follows from `IsRenyiDP.isEpsDeltaDP_zeta_mul_exp`, since
`ζ_α ≤ 1`. -/
theorem IsRenyiDP.isEpsDeltaDP_exp_mul [IsMarkovKernel M] (h : IsRenyiDP M Adj α ρ) (hα : 1 < α)
    (ε : ℝ) : IsEpsDeltaDP M Adj ε (exp ((α - 1) * (ρ - ε))) :=
  (h.isEpsDeltaDP_zeta_mul_exp hα ε).mono le_rfl
    (mul_le_of_le_one_left (exp_pos _).le (zeta_lt_one hα).le)

end InformationTheory
