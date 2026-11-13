/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.Amplification.HockeyStick
public import InfoLeakage.RDPConversion.Basic

/-!
# Conversions from Rényi to `(ε, δ)`-differential privacy (Asoodeh et al.)

This file formalizes conversion results of S. Asoodeh, J. Liao, F. P. Calmon, O. Kosut and
L. Sankar, *Three variants of differential privacy: lossless conversion and applications*, IEEE
J. Sel. Areas Inf. Theory 2 (2021) ([arXiv:2008.06529](https://arxiv.org/abs/2008.06529));
result and equation numbers follow arXiv v2.

The paper expresses `(ε, δ)`-DP through the hockey-stick divergence `E_{e^ε}` (equation (9)) and
`(α, γ)`-RDP through the `χ^α`-divergence, `D_α ≤ γ ⟺ χ^α ≤ χ(γ) = (e^{(α - 1) γ} - 1) / (α - 1)`
(equations (10)–(11)), and studies the optimal conversion `ε^δ_α(γ)`, the smallest `ε` such that
every `(α, γ)`-RDP mechanism is `(ε, δ)`-DP (equation (14)). Its Lemma 1 gives
`ε^δ_α(γ) = (γ + log (1 - δ))_+` when `α δ ≥ 1` (equation (24)) and, when `0 < α δ < 1`, the
upper bound
`ε^δ_α(γ) ≤ (α - 1)⁻¹ (min ((α - 1) γ - log (δ / ζ_α)) (log ((e^{(α - 1) γ} - 1) / (α δ) + 1)))_+`
(equation (25)), whose first term is Theorem 21 of Balle et al. (`InfoLeakage.RDPConversion.Basic`).

**Scope.** Mechanisms are Markov kernels `M : Kernel 𝒟 Y` into an arbitrary measurable space,
`(α, γ)`-RDP is `IsRenyiDP` (with `γ : ℝ≥0`) and `(ε, δ)`-DP is `IsEpsDeltaDP`; the neighbouring
relation is arbitrary. The divergences are Statlib's `renyiDiv` and `hellingerDiv` (the
`χ^α`-divergence of the paper; Statlib uses the generator `(t ^ α - 1 - α (t - 1)) / (α - 1)`,
which gives the same divergence between probability measures) and the library's
`hockeyStickDiv`. Optimality is stated for pairs of distributions on `Bool` and, for mechanisms,
for a one-sided neighbouring relation (see the notes below).

## Main definitions

* `RDPConversion.optimalEps α γ δ`: the optimal conversion `ε^δ_α(γ)` of equation (14), over
  ordered pairs of probability measures.

## Main statements (paper result → Lean name)

* Equation (9) is `isEpsDeltaDP_iff_forall_hockeyStickDiv_le`
  (`InfoLeakage.Amplification.HockeyStick`); equations (10)–(11) →
  `isRenyiDP_iff_forall_hellingerDiv_le` (from `RenyiDP.renyiDiv_le_ofReal_iff_hellingerDiv`).
* A relation between the two divergences:
  `E_λ(P ‖ Q) ≤ (α - 1) χ^α(P ‖ Q) / (α (λ ^ (α - 1) - 1))` for `λ > 1` →
  `RDPConversion.hockeyStickDiv_le_hellingerDiv`, and in Rényi form
  `RDPConversion.measureReal_sub_le_of_renyiDiv_le`. (The paper reaches its bounds through the
  joint range of the two divergences, Theorems 2–4; the inequality used here gives the second
  term of (25) directly.)
* Lemma 1, equation (24), as an equality over ordered pairs:
  `ε^δ_α(γ) = (γ + log (1 - δ))_+` for `α δ ≥ 1` and `δ < 1` → `RDPConversion.optimalEps_eq`.
  The upper bound → `IsRenyiDP.isEpsDeltaDP_add_log_one_sub` (for probability measures,
  `RDPConversion.measureReal_le_of_renyiDiv_le_of_one_le_mul`); the lower bound, for pairs of
  distributions → `RDPConversion.add_log_one_sub_le_of_forall` (with the extremal pair
  `RDPConversion.exists_renyiDiv_le_and_lt`), and for mechanisms →
  `RDPConversion.exists_isRenyiDP_not_isEpsDeltaDP`. The lower bound `γ + log (1 - δ)` never
  exceeds the `ε` of Theorem 21 of Balle et al.
  (`RDPConversion.add_log_one_sub_le_improvedEps`); the upper bound (24) is established only when
  `α δ ≥ 1`.
* Lemma 1, equation (25) → `IsRenyiDP.isEpsDeltaDP_max_min`; its second term (equation (102) of
  Appendix D) → `IsRenyiDP.isEpsDeltaDP_log_one_add`.
* Remark 1 (when RDP gives `(0, δ)`-DP) → `IsRenyiDP.isEpsDeltaDP_zero`.

## Implementation notes

* The hockey-stick parameter `λ = e^ε` of the paper is written `l` (`λ` is a Lean keyword).
* The upper bounds are proved for every `δ > 0`; the paper states the second term of (25) for
  `0 < δ ≤ 1 / α` (Appendix D) and Lemma 1 for `0 < α δ < 1`. The second term of (25) is proved
  from the pointwise inequality `α (λ ^ (α - 1) - 1) (t - λ) ≤ t ^ α - 1 - α (t - 1)`
  (`RDPConversion.mul_sub_le_rpow_sub`) integrated against `Q` at `t = dP/dQ`, instead of the
  paper's convexity argument.
* Equation (24) is proved from `P(E) ≤ min ((e^γ Q(E)) ^ ((α - 1) / α), 1)` (Mironov's
  Proposition 10) and the concavity of `z ↦ z ^ ((α - 1) / α)` (`RDPConversion.le_one_sub_mul_add`).

## Not formalized

* Theorem 2 (the joint range of two `f`-divergences, from Harremoës–Vajda), Theorem 3 (the
  variational formula for the optimal conversion `γ^ε_α(δ)`) and the bound `f(α, ε, δ)` of
  Theorem 4; the sections on composition, the moments accountant, noisy SGD and `f`-DP.

## Notes on the paper

* Section III, equations (13)–(18) (arXiv v2): identifying `δ^ε_α(γ)` with the upper boundary of
  the joint range `R_α` of `(χ^α(M_d ‖ M_d'), E_{e^ε}(M_d ‖ M_d'))` treats each ordered pair
  `(M_d, M_d')` on its own, whereas for the paper's neighbouring relation (Hamming distance one,
  Section II, which is symmetric) an `(α, γ)`-RDP mechanism also satisfies
  `D_α(M_d' ‖ M_d) ≤ γ`. For `γ > 0` the extremal pair used here for (24) has
  `D_α(M_d' ‖ M_d) = ∞`. The upper bounds (Lemma 1, and Theorem 4 as lower bounds on
  `γ^ε_α(δ)`) hold for every neighbouring relation. Optimality is formalized for ordered pairs (a
  one-sided neighbouring relation); whether (24) is attained under the paper's symmetric Hamming
  relation is not addressed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {𝒟 Y : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}

namespace RDPConversion

/-- The pointwise inequality behind the hockey-stick bound: for `α > 1`, `λ > 0` and `t ≥ 0`,
`α (λ ^ (α - 1) - 1) (t - λ) ≤ t ^ α - 1 - α (t - 1)`. The right side `g(t)` is convex and
nonnegative with `g'(λ) = α (λ ^ (α - 1) - 1)`, so it lies above its tangent line at `λ`, hence
above the parallel line through `(λ, 0)`. -/
lemma mul_sub_le_rpow_sub {α l t : ℝ} (hα : 1 < α) (hl : 0 < l) (ht : 0 ≤ t) :
    α * (l ^ (α - 1) - 1) * (t - l) ≤ t ^ α - 1 - α * (t - 1) := by
  have e : l ^ α = l ^ (α - 1) * l := by
    rw [← Real.rpow_add_one hl.ne']
    ring_nf
  have hB1 : l ^ α + α * l ^ (α - 1) * (t - l) ≤ t ^ α := by
    have h := one_add_mul_self_le_rpow_one_add (s := t / l - 1)
      (by have := div_nonneg ht hl.le; linarith) hα.le
    rw [add_sub_cancel, Real.div_rpow ht hl.le, le_div_iff₀ (Real.rpow_pos_of_pos hl α)] at h
    calc l ^ α + α * l ^ (α - 1) * (t - l) = (1 + α * (t / l - 1)) * l ^ α := by
          rw [e]
          field_simp
      _ ≤ t ^ α := h
  have hB2 : 1 + α * (l - 1) ≤ l ^ α := by
    have h := one_add_mul_self_le_rpow_one_add (s := l - 1) (by linarith) hα.le
    rwa [add_sub_cancel] at h
  linarith

/-- Bernoulli's inequality in the form `0 ≤ t ^ α - 1 - α (t - 1)`, for `α ≥ 1` and `t ≥ 0`. -/
lemma rpow_sub_one_sub_mul_nonneg {α t : ℝ} (hα : 1 ≤ α) (ht : 0 ≤ t) :
    0 ≤ t ^ α - 1 - α * (t - 1) := by
  have h := one_add_mul_self_le_rpow_one_add (s := t - 1) (by linarith) hα
  rw [add_sub_cancel] at h
  linarith

/-- The hockey-stick bound by the Hellinger integral: for probability measures with `P ≪ Q`
whose density has an integrable `α`-th power, `α > 1`, `λ > 0` and every set `E`,
`α (λ ^ (α - 1) - 1) (P(E) - λ Q(E)) ≤ ∫ (dP/dQ) ^ α dQ - 1`. -/
theorem mul_sub_le_integral_rpow_sub_one {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α l : ℝ} (hα : 1 < α) (hl : 0 < l) (hac : P ≪ Q)
    (hint : Integrable (fun y ↦ ((∂P/∂Q) y).toReal ^ α) Q) (E : Set Y) :
    α * (l ^ (α - 1) - 1) * (P.real E - l * Q.real E) ≤
      ∫ y, ((∂P/∂Q) y).toReal ^ α ∂Q - 1 := by
  have hL : Integrable (fun y ↦ ((∂P/∂Q) y).toReal) Q := Measure.integrable_toReal_rnDeriv
  have hA : Integrable (fun y ↦ ((∂P/∂Q) y).toReal ^ α - 1) Q := hint.sub (integrable_const _)
  have hB : Integrable (fun y ↦ α * (((∂P/∂Q) y).toReal - 1)) Q :=
    (hL.sub (integrable_const _)).const_mul α
  have hg : Integrable (fun y ↦ ((∂P/∂Q) y).toReal ^ α - 1 - α * (((∂P/∂Q) y).toReal - 1)) Q :=
    hA.sub hB
  have hK : Integrable (fun y ↦ α * (l ^ (α - 1) - 1) * (((∂P/∂Q) y).toReal - l)) Q :=
    (hL.sub (integrable_const _)).const_mul _
  have hE : ∫ y in E, (((∂P/∂Q) y).toReal - l) ∂Q = P.real E - l * Q.real E := by
    rw [integral_sub hL.integrableOn (integrable_const _), Measure.setIntegral_toReal_rnDeriv hac,
      setIntegral_const, smul_eq_mul, mul_comm l]
  have hI : ∫ y, (((∂P/∂Q) y).toReal - 1) ∂Q = 0 := by
    rw [integral_sub hL (integrable_const _), Measure.integral_toReal_rnDeriv hac]
    simp
  calc α * (l ^ (α - 1) - 1) * (P.real E - l * Q.real E)
      = ∫ y in E, α * (l ^ (α - 1) - 1) * (((∂P/∂Q) y).toReal - l) ∂Q := by
        rw [integral_const_mul, hE]
    _ ≤ ∫ y in E, (((∂P/∂Q) y).toReal ^ α - 1 - α * (((∂P/∂Q) y).toReal - 1)) ∂Q :=
        setIntegral_mono hK.integrableOn hg.integrableOn fun y ↦
          mul_sub_le_rpow_sub hα hl ENNReal.toReal_nonneg
    _ ≤ ∫ y, (((∂P/∂Q) y).toReal ^ α - 1 - α * (((∂P/∂Q) y).toReal - 1)) ∂Q :=
        setIntegral_le_integral hg (Filter.Eventually.of_forall fun y ↦
          rpow_sub_one_sub_mul_nonneg hα.le ENNReal.toReal_nonneg)
    _ = ∫ y, (((∂P/∂Q) y).toReal ^ α - 1) ∂Q - ∫ y, α * (((∂P/∂Q) y).toReal - 1) ∂Q :=
        integral_sub hA hB
    _ = ∫ y, ((∂P/∂Q) y).toReal ^ α ∂Q - 1 := by
        rw [integral_const_mul, hI, integral_sub hint (integrable_const _)]
        simp

/-- The hockey-stick divergence is bounded by the Hellinger divergence: for probability measures,
`α > 1` and `λ > 1`, `E_λ(P ‖ Q) ≤ (α - 1) χ^α(P ‖ Q) / (α (λ ^ (α - 1) - 1))`, where `χ^α` is
Statlib's `hellingerDiv α` (the `χ^α`-divergence of Asoodeh et al.). -/
theorem hockeyStickDiv_le_hellingerDiv {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α l : ℝ} (hα : 1 < α) (hl : 1 < l) (h : hellingerDiv α P Q ≠ ∞) :
    hockeyStickDiv l P Q ≤ (α - 1) * (hellingerDiv α P Q).toReal / (α * (l ^ (α - 1) - 1)) := by
  obtain ⟨hint, hac⟩ := (hellingerDiv_ne_top_iff_of_one_lt hα P Q).1 h
  have hI := mul_hellingerDiv_add_meas_eq_integral (μ := P) (ν := Q) (by linarith) hα.ne' h
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at hI
  have hK : 0 < α * (l ^ (α - 1) - 1) :=
    mul_pos (by linarith) (by linarith [Real.one_lt_rpow hl (by linarith : (0 : ℝ) < α - 1)])
  refine hockeyStickDiv_le_of_forall fun E _ ↦ ?_
  rw [le_div_iff₀ hK, mul_comm]
  have := mul_sub_le_integral_rpow_sub_one (l := l) hα (by linarith) hac hint E
  linarith

/-- The hockey-stick bound for a Rényi divergence: for probability measures with
`D_α(P ‖ Q) ≤ γ`, `α > 1` and `λ > 1`, every set `E` satisfies
`P(E) - λ Q(E) ≤ (e^{(α - 1) γ} - 1) / (α (λ ^ (α - 1) - 1))`. -/
theorem measureReal_sub_le_of_renyiDiv_le {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α γ l : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hl : 1 < l)
    (h : renyiDiv α P Q ≤ ENNReal.ofReal γ) (E : Set Y) :
    P.real E - l * Q.real E ≤ (exp ((α - 1) * γ) - 1) / (α * (l ^ (α - 1) - 1)) := by
  obtain ⟨hH, hle⟩ := (RenyiDP.renyiDiv_le_ofReal_iff_integral hα hγ).1 h
  obtain ⟨hint, hac⟩ := (hellingerDiv_ne_top_iff_of_one_lt hα P Q).1 hH
  have hK : 0 < α * (l ^ (α - 1) - 1) :=
    mul_pos (by linarith) (by linarith [Real.one_lt_rpow hl (by linarith : (0 : ℝ) < α - 1)])
  rw [le_div_iff₀ hK, mul_comm]
  have := mul_sub_le_integral_rpow_sub_one (l := l) hα (by linarith) hac hint E
  linarith

/-- If `D_α(P ‖ Q) ≤ 0` for some `α > 1`, then `P(E) ≤ Q(E)` for every set `E`. -/
lemma measureReal_le_of_renyiDiv_le_zero {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α : ℝ} (hα : 1 < α) (h : renyiDiv α P Q ≤ ENNReal.ofReal 0)
    (E : Set Y) : P.real E ≤ Q.real E := by
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have h1 := measureReal_sub_le_of_renyiDiv_le hα le_rfl (l := 1 + η) (by linarith) h E
  have hQ : Q.real E ≤ 1 := measureReal_le_one
  simp only [mul_zero, exp_zero, sub_self, zero_div] at h1
  nlinarith

/-- The real inequality behind equation (24) of Asoodeh et al.: if `α > 1`, `α δ ≥ 1`,
`δ ≤ 1`, `z ≥ 0` and `x ≤ min (z ^ ((α - 1) / α), 1)`, then `x ≤ (1 - δ) z + δ`. -/
lemma le_one_sub_mul_add {α δ x z : ℝ} (hα : 1 < α) (hαδ : 1 ≤ α * δ) (hδ1 : δ ≤ 1)
    (hz : 0 ≤ z) (hxz : x ≤ z ^ ((α - 1) / α)) (hx1 : x ≤ 1) : x ≤ (1 - δ) * z + δ := by
  have hα0 : 0 < α := by linarith
  set p := (α - 1) / α with hpdef
  have hp : 1 - δ ≤ p := by
    rw [hpdef, le_div_iff₀ hα0]
    linarith
  have hp0 : 0 ≤ p := div_nonneg (by linarith) hα0.le
  have hp1 : p ≤ 1 := by
    rw [hpdef, div_le_one hα0]
    linarith
  rcases le_total z 1 with hz1 | hz1
  · have h := rpow_one_add_le_one_add_mul_self (s := z - 1) (by linarith) hp0 hp1
    rw [add_sub_cancel] at h
    nlinarith [mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hz1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hδ1) (sub_nonneg.2 hz1)]

/-- Equation (24) of Asoodeh et al. for probability measures: if `D_α(P ‖ Q) ≤ γ` with
`α > 1`, `α δ ≥ 1` and `δ < 1`, then `P(E) ≤ e^{γ + log (1 - δ)} Q(E) + δ` for every set `E`. -/
theorem measureReal_le_of_renyiDiv_le_of_one_le_mul {P Q : Measure Y} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {α γ δ : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hαδ : 1 ≤ α * δ)
    (hδ1 : δ < 1) (h : renyiDiv α P Q ≤ ENNReal.ofReal γ) (E : Set Y) :
    P.real E ≤ exp (γ + log (1 - δ)) * Q.real E + δ := by
  have h1 := ENNReal.toReal_mono (by finiteness)
    (RenyiDP.measure_le_rpow_of_renyiDiv_le hα hγ h E)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le,
    ← measureReal_def, ← measureReal_def] at h1
  rw [exp_add, exp_log (by linarith)]
  exact (le_one_sub_mul_add hα hαδ hδ1.le (by positivity) h1 measureReal_le_one).trans_eq
    (by ring)

/-- The extremal pair for equation (24) of Asoodeh et al.: for `α > 1`, `γ ≥ 0`, `δ < 1` and
`ε < γ + log (1 - δ)`, the probability measures `P = δ_true` and
`Q = e^{-γ} δ_true + (1 - e^{-γ}) δ_false` on `Bool` satisfy `D_α(P ‖ Q) ≤ γ` and
`P{true} > e^ε Q{true} + δ`. -/
theorem exists_renyiDiv_le_and_lt {α γ δ ε : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hδ1 : δ < 1)
    (hε : ε < γ + log (1 - δ)) :
    ∃ P Q : Measure Bool, IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      renyiDiv α P Q ≤ ENNReal.ofReal γ ∧ exp ε * Q.real {true} + δ < P.real {true} := by
  classical
  set q := exp (-γ) with hqdef
  have hq0 : 0 < q := exp_pos _
  have hq1 : q ≤ 1 := exp_le_one_iff.2 (by linarith)
  set Q : Measure Bool :=
    ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false with hQ
  have hQs (s : Set Bool) : Q s = (if true ∈ s then ENNReal.ofReal q else 0)
      + (if false ∈ s then ENNReal.ofReal (1 - q) else 0) := by
    simp only [hQ, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> simp
  have hQprob : IsProbabilityMeasure Q := ⟨by
    rw [hQs]
    simp only [Set.mem_univ, ite_true]
    rw [← ENNReal.ofReal_add hq0.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]⟩
  have hR : renyiDiv α (Measure.dirac true) Q ≤ ENNReal.ofReal γ := by
    refine RenyiDP.renyiDiv_le_of_forall_le hα hγ fun s ↦ ?_
    by_cases hs : true ∈ s
    · rw [Measure.dirac_apply_of_mem hs]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (exp γ) * ENNReal.ofReal q := by
            rw [← ENNReal.ofReal_mul (exp_pos _).le, hqdef, ← exp_add, add_neg_cancel, exp_zero,
              ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal (exp γ) * Q s := by
            gcongr
            rw [hQs]
            simp only [hs, ↓reduceIte]
            exact le_self_add
    · simp [hs]
  refine ⟨Measure.dirac true, Q, inferInstance, hQprob, hR, ?_⟩
  have hQt : Q.real {true} = q := by
    rw [measureReal_def, hQs]
    simp [hq0.le]
  rw [hQt, measureReal_def, Measure.dirac_apply_of_mem rfl, ENNReal.toReal_one]
  have h2 : exp ε * q < 1 - δ := by
    rw [hqdef, ← exp_add, ← exp_log (by linarith : 0 < 1 - δ)]
    exact exp_lt_exp.2 (by linarith)
  linarith

/-- No conversion from `(α, γ)`-RDP to `(ε, δ)`-DP can beat `ε = γ + log (1 - δ)`: if every pair
of probability measures on `Bool` with `D_α(P ‖ Q) ≤ γ` satisfies `P(E) ≤ e^ε Q(E) + δ` for every
`E`, then `γ + log (1 - δ) ≤ ε`, for every `δ < 1`. This is the lower bound
`ε^δ_α(γ) ≥ γ + log (1 - δ)` behind the equality in equation (24) of Asoodeh et al. (it does not
need `α δ ≥ 1`). -/
theorem add_log_one_sub_le_of_forall {α γ δ ε : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hδ1 : δ < 1)
    (h : ∀ P Q : Measure Bool, IsProbabilityMeasure P → IsProbabilityMeasure Q →
      renyiDiv α P Q ≤ ENNReal.ofReal γ → ∀ E, P.real E ≤ exp ε * Q.real E + δ) :
    γ + log (1 - δ) ≤ ε := by
  by_contra! hε
  obtain ⟨P, Q, hP, hQ, hR, hlt⟩ := exists_renyiDiv_le_and_lt hα hγ hδ1 hε
  linarith [h P Q hP hQ hR {true}]

/-- The lower bound `γ + log (1 - δ)` of equation (24) of Asoodeh et al. never exceeds the `ε` of
Theorem 21 of Balle et al.: for `α > 1`, `γ ≥ 0` and `0 < δ < 1`,
`γ + log (1 - δ) ≤ γ + log ((α - 1) / α) - (log δ + log α) / (α - 1)`. (By
`add_log_one_sub_le_of_forall`, this holds because Theorem 21 is a valid conversion.) The matching
upper bound (24) is established only when `α δ ≥ 1`. -/
theorem add_log_one_sub_le_improvedEps {α γ δ : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    γ + log (1 - δ) ≤ γ + log ((α - 1) / α) - (log δ + log α) / (α - 1) :=
  add_log_one_sub_le_of_forall hα hγ hδ1 fun _ _ _ _ hR E ↦
    measureReal_le_of_renyiDiv_le hα hγ hδ0 hR E

/-- Optimality of equation (24) of Asoodeh et al. for mechanisms: for `α > 1`, `γ ≥ 0`, `δ < 1`
and `ε < γ + log (1 - δ)`, there is a mechanism `M : Kernel Bool Bool` that is `(α, γ)`-RDP but
not `(ε, δ)`-DP, for the neighbouring relation whose only pair is `(true, false)`.
(For a symmetric relation the RDP constraint would also bound `D_α(M false ‖ M true)`, which is
infinite for this extremal mechanism when `γ > 0`; see the notes on the paper.) -/
theorem exists_isRenyiDP_not_isEpsDeltaDP {α γ δ ε : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hδ1 : δ < 1)
    (hε : ε < γ + log (1 - δ)) :
    ∃ M : Kernel Bool Bool, IsMarkovKernel M ∧
      IsRenyiDP M (fun S S' ↦ S = true ∧ S' = false) α γ.toNNReal ∧
      ¬ IsEpsDeltaDP M (fun S S' ↦ S = true ∧ S' = false) ε δ := by
  obtain ⟨P, Q, hP, hQ, hR, hlt⟩ := exists_renyiDiv_le_and_lt hα hγ hδ1 hε
  refine ⟨Kernel.ofFunOfCountable fun b ↦ cond b P Q, ⟨fun b ↦ by cases b <;> assumption⟩, ?_, ?_⟩
  · rintro S S' ⟨rfl, rfl⟩
    exact hR
  · intro hDP
    have h1 : P.real {true} ≤ exp ε * Q.real {true} + δ :=
      hDP (S := true) (S' := false) ⟨rfl, rfl⟩ {true}
    linarith

/-- The optimal conversion `ε^δ_α(γ)` of equation (14) of Asoodeh et al., over ordered pairs of
probability measures: the infimum of the `ε ≥ 0` such that every pair `(P, Q)` of probability
measures on a measurable space (in `Type`) with `D_α(P ‖ Q) ≤ γ` satisfies `P(E) ≤ e^ε Q(E) + δ`
for every set `E`. -/
noncomputable def optimalEps (α γ δ : ℝ) : ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P Q : Measure Ω),
    IsProbabilityMeasure P → IsProbabilityMeasure Q → renyiDiv α P Q ≤ ENNReal.ofReal γ →
      ∀ E, P.real E ≤ exp ε * Q.real E + δ}

/-- **Lemma 1** of Asoodeh et al., equation (24), as an equality over ordered pairs: for
`α > 1`, `γ ≥ 0`, `α δ ≥ 1` and `δ < 1`, `ε^δ_α(γ) = (γ + log (1 - δ))_+`. -/
theorem optimalEps_eq {α γ δ : ℝ} (hα : 1 < α) (hγ : 0 ≤ γ) (hαδ : 1 ≤ α * δ) (hδ1 : δ < 1) :
    optimalEps α γ δ = max (γ + log (1 - δ)) 0 := by
  refine IsLeast.csInf_eq ⟨⟨le_max_right _ _, ?_⟩, fun ε hε ↦ ?_⟩
  · intro Ω _ P Q _ _ hR E
    refine (measureReal_le_of_renyiDiv_le_of_one_le_mul hα hγ hαδ hδ1 hR E).trans ?_
    gcongr
    exact le_max_left _ _
  · exact max_le (add_log_one_sub_le_of_forall hα hγ hδ1 fun P Q hP hQ hR E ↦
      hε.2 Bool P Q hP hQ hR E) hε.1

end RDPConversion

open RDPConversion

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {α : ℝ} {γ : ℝ≥0}

/-- Equations (10)–(11) of Asoodeh et al.: for `α > 1`, a mechanism is `(α, γ)`-RDP iff
`χ^α(M(S) ‖ M(S')) ≤ χ(γ) = (e^{(α - 1) γ} - 1) / (α - 1)` for all neighbouring `S, S'`, where
`χ^α` is Statlib's Hellinger divergence `hellingerDiv α`. -/
theorem isRenyiDP_iff_forall_hellingerDiv_le [IsMarkovKernel M] (hα : 1 < α) :
    IsRenyiDP M Adj α γ ↔ ∀ ⦃S S'⦄, Adj S S' →
      hellingerDiv α (M S) (M S') ≤ ENNReal.ofReal ((exp ((α - 1) * γ) - 1) / (α - 1)) := by
  have key (S S' : 𝒟) : renyiDiv α (M S) (M S') ≤ γ ↔
      hellingerDiv α (M S) (M S') ≤ ENNReal.ofReal ((exp ((α - 1) * γ) - 1) / (α - 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal, RenyiDP.renyiDiv_le_ofReal_iff_hellingerDiv hα γ.coe_nonneg]
  simp only [IsRenyiDP, key]

/-- **Lemma 1** of Asoodeh et al., second term of equation (25) (equation (102)): an
`(α, γ)`-RDP mechanism with `α > 1` is `(ε, δ)`-DP with
`ε = log ((e^{(α - 1) γ} - 1) / (α δ) + 1) / (α - 1)`, for every `δ > 0`. The paper derives it
for `0 < δ ≤ 1 / α` from a linearization of the bound `f` of its Theorem 4; the proof here is
direct (`RDPConversion.measureReal_sub_le_of_renyiDiv_le`) and needs only `δ > 0`. -/
theorem IsRenyiDP.isEpsDeltaDP_log_one_add [IsMarkovKernel M] (h : IsRenyiDP M Adj α γ)
    (hα : 1 < α) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (log ((exp ((α - 1) * γ) - 1) / (α * δ) + 1) / (α - 1)) δ := by
  intro S S' hS E
  have hR : renyiDiv α (M S) (M S') ≤ ENNReal.ofReal γ := by simpa using h hS
  have hα1 : 0 < α - 1 := by linarith
  rcases γ.coe_nonneg.eq_or_lt with hγ | hγ
  · rw [← hγ] at hR ⊢
    have := measureReal_le_of_renyiDiv_le_zero hα hR E
    simp only [mul_zero, exp_zero, sub_self, zero_div, zero_add, log_one, one_mul]
    linarith
  · have he : 0 < exp ((α - 1) * γ) - 1 := sub_pos.2 (one_lt_exp_iff.2 (mul_pos hα1 hγ))
    set c := (exp ((α - 1) * γ) - 1) / (α * δ) + 1 with hc
    have hc1 : 1 < c := by
      have : 0 < (exp ((α - 1) * γ) - 1) / (α * δ) := div_pos he (by positivity)
      linarith
    have hl : 1 < exp (log c / (α - 1)) := one_lt_exp_iff.2 (div_pos (log_pos hc1) hα1)
    have hpow : exp (log c / (α - 1)) ^ (α - 1) = c := by
      rw [← exp_mul, div_mul_cancel₀ _ hα1.ne', exp_log (by linarith)]
    have h1 := measureReal_sub_le_of_renyiDiv_le hα γ.coe_nonneg hl hR E
    have h2 : (exp ((α - 1) * γ) - 1) / (α * (c - 1)) = δ := by
      rw [hc, add_sub_cancel_right]
      field_simp
    rw [hpow, h2] at h1
    linarith

/-- **Lemma 1** of Asoodeh et al., equation (24), upper bound: if `α δ ≥ 1` and `δ < 1`, an
`(α, γ)`-RDP mechanism with `α > 1` is `(γ + log (1 - δ), δ)`-DP. The paper's
`ε^δ_α(γ) = (γ + log (1 - δ))_+` takes the positive part because it optimizes over `ε ≥ 0`; the
matching lower bound is `RDPConversion.add_log_one_sub_le_of_forall`, and the equality is
`RDPConversion.optimalEps_eq`. -/
theorem IsRenyiDP.isEpsDeltaDP_add_log_one_sub [IsMarkovKernel M] (h : IsRenyiDP M Adj α γ)
    (hα : 1 < α) {δ : ℝ} (hαδ : 1 ≤ α * δ) (hδ1 : δ < 1) :
    IsEpsDeltaDP M Adj (γ + log (1 - δ)) δ := fun _ _ hS E ↦
  measureReal_le_of_renyiDiv_le_of_one_le_mul hα γ.coe_nonneg hαδ hδ1 (by simpa using h hS) E

/-- **Lemma 1** of Asoodeh et al., equation (25): an `(α, γ)`-RDP mechanism with `α > 1` is
`(ε, δ)`-DP with
`ε = (α - 1)⁻¹ (min ((α - 1) γ - log (δ / ζ_α)) (log ((e^{(α - 1) γ} - 1) / (α δ) + 1)))_+`,
for every `δ > 0`. The paper states it for `0 < α δ < 1`. The first term is Theorem 21 of Balle et
al. (`IsRenyiDP.isEpsDeltaDP_zeta`), the second is `IsRenyiDP.isEpsDeltaDP_log_one_add`. -/
theorem IsRenyiDP.isEpsDeltaDP_max_min [IsMarkovKernel M] (h : IsRenyiDP M Adj α γ) (hα : 1 < α)
    {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (max (min ((α - 1) * γ - log (δ / zeta α))
      (log ((exp ((α - 1) * γ) - 1) / (α * δ) + 1))) 0 / (α - 1)) δ := by
  have hα1 : 0 < α - 1 := by linarith
  set A := (α - 1) * γ - log (δ / zeta α)
  set B := log ((exp ((α - 1) * γ) - 1) / (α * δ) + 1)
  have hA : IsEpsDeltaDP M Adj (A / (α - 1)) δ := by
    convert h.isEpsDeltaDP_zeta hα hδ using 1
    field_simp
    rfl
  have hB : IsEpsDeltaDP M Adj (B / (α - 1)) δ := h.isEpsDeltaDP_log_one_add hα hδ
  rcases le_total A B with hAB | hAB
  · refine hA.mono (div_le_div_of_nonneg_right ?_ hα1.le) le_rfl
    rw [min_eq_left hAB]
    exact le_max_left _ _
  · refine hB.mono (div_le_div_of_nonneg_right ?_ hα1.le) le_rfl
    rw [min_eq_right hAB]
    exact le_max_left _ _

/-- **Remark 1** of Asoodeh et al.: an `(α, γ)`-RDP mechanism with `α > 1` is `(0, δ)`-DP as soon
as `δ ≥ ζ_α e^{(α - 1) γ}`, or `α δ ≥ 1` and `δ ≥ 1 - e^{-γ}`. The paper states the first case
for `δ ∈ [ζ_α e^{(α - 1) γ}, 1 / α]` with `γ < log (α / (α - 1))` (so that the interval is
nonempty), and the second (Appendix E) for `δ > max (1 - e^{-γ}) (1 / α)`. -/
theorem IsRenyiDP.isEpsDeltaDP_zero [IsMarkovKernel M] (h : IsRenyiDP M Adj α γ) (hα : 1 < α)
    {δ : ℝ} (hδ : zeta α * exp ((α - 1) * γ) ≤ δ ∨ (1 ≤ α * δ ∧ 1 - exp (-γ) ≤ δ)) :
    IsEpsDeltaDP M Adj 0 δ := by
  rcases hδ with hδ | ⟨hαδ, hδ'⟩
  · exact (h.isEpsDeltaDP_zeta_mul_exp hα 0).mono le_rfl (by simpa using hδ)
  rcases lt_or_ge δ 1 with hδ1 | hδ1
  · refine (h.isEpsDeltaDP_add_log_one_sub hα hαδ hδ1).mono ?_ le_rfl
    have : log (1 - δ) ≤ -γ := by
      rw [log_le_iff_le_exp (by linarith)]
      linarith
    linarith
  · intro S S' hS E
    have : (M S).real E ≤ 1 := measureReal_le_one
    have : 0 ≤ (M S').real E := measureReal_nonneg
    rw [exp_zero, one_mul]
    linarith

end InformationTheory
