/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.DP.Exponential
public import InfoLeakage.ZCDP.Basic

/-!
# Bounded-range mechanisms

This file formalizes bounded-range (BR) mechanisms, introduced by D. Durfee and R. Rogers,
*Practical differentially private top-k selection with pay-what-you-get composition*,
NeurIPS 2019 ([arXiv:1905.04273](https://arxiv.org/abs/1905.04273), v2), and their
zero-concentrated privacy following M. Cesar and R. Rogers, *Bounding, concentrating, and
truncating: unifying privacy loss composition for data analytics*, ALT 2021
([arXiv:2004.07223](https://arxiv.org/abs/2004.07223), v3). Result numbers refer to these
versions, abbreviated DR and CR.

A mechanism is a kernel `M : Kernel 𝒟 Y` and `Adj : 𝒟 → 𝒟 → Prop` is an arbitrary neighbouring
relation. The mechanism is `η`-BR if, for all neighbours `x, x'`, the privacy loss
`log (dM(x)/dM(x'))` takes values in an interval of length `η`; pure `ε`-DP only places it in
`[-ε, ε]`, an interval of length `2ε`. Differential privacy is `IsEpsDeltaDP`/`IsEpsDP`
(`InfoLeakage.FDP.Basic`, `InfoLeakage.DP.Basic`), zCDP is `IsZCDP` (`InfoLeakage.ZCDP.Basic`),
and the exponential mechanism is `exponentialMechanism` (`InfoLeakage.DP.Exponential`).

**Scope.** The definition and the general results hold for arbitrary measurable output spaces;
the pointwise forms of the definition assume a countable output space with measurable
singletons, and the exponential mechanism has a finite output set.

## Main definitions

* `IsBoundedRange M Adj η`: `η`-bounded range (DR, Definition 4.2; CR, Definition 2.2).
* `BoundedRange.CrossLe μ ν η`: the bounded-range condition for a pair of measures.

## Main statements (paper result → Lean name)

* DR, Definition 4.2, and CR, Definition 2.2, as stated with ratios of point probabilities:
  `isBoundedRange_iff_forall_singleton_div`; with the denominators cleared:
  `isBoundedRange_iff_forall_singleton`.
* DR, Corollary 4.2, and CR, Lemma 2.1 (`η`-BR implies `η`-DP, and `ε`-DP implies `2ε`-BR):
  `IsBoundedRange.isEpsDP`, `IsEpsDeltaDP.isBoundedRange`.
* CR, Lemma 2.1, last part (the privacy loss lies in `[t - η, t]` for some `t ∈ [0, η]`):
  `IsBoundedRange.exists_log_mem_Icc`; DR, Corollary 4.2, last claim
  (`sup_y ln (P[M(x) = y] / P[M(x') = y]) - inf_{y'} ln (…) ≤ η`, over outputs of positive
  probability): `IsBoundedRange.log_div_sub_log_div_le`; measure form, with its converse:
  `isBoundedRange_iff_exists_sandwich` (via `BoundedRange.CrossLe.exists_sandwich`).
* DR, Lemma 4.3 (the exponential mechanism is BR; the monotonic case):
  `isBoundedRange_exponentialMechanism`, `isBoundedRange_exponentialMechanism_of_monotone`, both
  from the general `isBoundedRange_exponentialMechanism_of_range`. The claim after CR,
  Definition 2.3 (the exponential mechanism calibrated to the range of the score is `ε`-BR):
  `isBoundedRange_exponentialMechanism_range`.
* CR, remark after Lemma 3.4, using Hoeffding's lemma as in CR, Lemma 3.2 (`η`-BR implies
  `(η² / 8)`-zCDP):
  `IsBoundedRange.isZCDP`, via the Rényi bound `BoundedRange.renyiDiv_le_of_sandwich`; with the
  conversion to approximate DP (CR, Lemma 2.3): `IsBoundedRange.isEpsDeltaDP`.
* Composition, by the zCDP composition theorems of Bun–Steinke applied to
  `IsBoundedRange.isZCDP`: non-adaptive, `isZCDP_piKernel_of_isBoundedRange`; adaptive, for two
  mechanisms, `isZCDP_compProd_of_isBoundedRange`; approximate-DP form,
  `isEpsDeltaDP_piKernel_of_isBoundedRange`, which strengthens the third bound of DR, Lemma 4.4,
  in the non-adaptive case, and is the non-adaptive, BR-only case of CR, equation (3), with the
  weaker mean term `η² / 8` and heterogeneous `η i` allowed (CR's (3) holds under set-wise
  adaptive composition with a shared parameter); homogeneous form
  `isEpsDeltaDP_piKernel_of_isBoundedRange_const`.
* The exponential mechanism is `(ε² / 8)`-zCDP (`isZCDP_exponentialMechanism`), and `k`
  exponential mechanisms compose to `(k ε² / 8)`-zCDP and
  `(k ε² / 8 + ε √(k log (1 / δ) / 2), δ)`-DP (`isZCDP_pi_exponentialMechanism`), against
  `k ε² / 2` through pure DP.

## Implementation notes

* The papers' ratio `P[M(x) = y₁] / P[M(x') = y₁] ≤ e^η P[M(x) = y₂] / P[M(x') = y₂]` is stated
  with the denominators cleared, for measurable sets of outputs rather than single outputs (as
  footnote 4 of DR allows for pure DP), in `ℝ≥0∞`. On countable output spaces this is the
  pointwise condition (`isBoundedRange_iff_forall_singleton`), and when all point probabilities
  are positive it is the papers' ratio form (`isBoundedRange_iff_forall_singleton_div`). The
  papers leave the ratio undefined when probabilities vanish; the cleared form forces `M x` and
  `M x'` to have the same null sets, as the finite privacy loss of CR, Lemma 2.1 requires. The
  density form for continuous outputs that DR mention is not formalized.
* `IsBoundedRange.isZCDP` applies Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`) to the
  privacy loss twice: at `-1`, to bound its mean by `η² / 8`, and at `α - 1`, to bound the Rényi
  divergence of order `α`. CR use the sharper mean bound
  `η / (e^η - 1) - 1 - log (η / (e^η - 1))` of Dong, Durfee and Rogers and state
  `(ξ, η² / 8)`-zCDP with `ξ ≤ 0`; only the consequence `ξ = 0` is formalized. The argument
  generalizes `ZCDP.renyiDiv_le_sq_of_le_smul` (Bun–Steinke, Proposition 3.3), which is the case
  of the interval `[-ε, ε]`.
* `IsZCDP` bounds `D_α(M x ‖ M x')` for each ordered pair of neighbours; CR's Definition 2.7
  asks for both directions, which follow because bounded range is symmetric
  (`IsBoundedRange.symm`).
* Normalizations of the exponential mechanism: `exponentialMechanism u ε Δ` outputs `r` with
  probability proportional to `exp (ε u(x, r) / (2Δ))` (Dwork–Roth). DR's `EM_q` with parameter
  `ε` uses `exp (ε q(x, r) / Δ(q))`, which is `exponentialMechanism q (2ε) Δ(q)`, and DR's
  Lemma 4.3 says it is `2ε`-BR (`ε`-BR for monotonic scores); with parameter `ε / 2`, as here, it
  is `ε`-BR (`ε / 2`-BR). CR's mechanism uses `exp (ε u(x, r) / Δ̃)` for a bound `Δ̃` on the range
  of the score, which is `exponentialMechanism u ε (Δ̃ / 2)`
  (`BoundedRange.exponentialMechanismProb_half`).

## Notes on the papers

* DR, discussion after Corollary 4.2 (p. 12, v2): "for any `y ∈ Y` there is some fixed
  `t ∈ [0, ε]` such that `ln (Pr[M(x) = y] / Pr[M(x') = y]) ∈ [-t, ε - t]`" has the quantifiers
  in the wrong order as written. Read literally (for all `y` there is `t`), the claim is
  equivalent to `|ln (Pr[M(x) = y] / Pr[M(x') = y])| ≤ ε`, which is the `ε`-DP guarantee that the
  next sentence contrasts it with, so the contrast collapses. The word "fixed" signals the
  intended order, one `t` for all `y` (for each pair of neighbours), as in CR, Lemma 2.1
  (`t := t(x, x')`), and in DR's own proof of Lemma 4.4 (Appendix B.2). The intended statement
  is true (`IsBoundedRange.exists_log_mem_Icc`, with `t` replaced by `η - t`).

## Not formalized

* CR's sharper mean bound for the privacy loss of BR mechanisms (from Dong–Durfee–Rogers), hence
  the exact form of CR, equation (3), and the value `ξ < 0` in the remark after CR, Lemma 3.4.
* Adaptive composition of more than two BR mechanisms (DR, Lemma 4.4 in full; CR's set-wise
  adaptive composition, Section 3), and the optimal composition bounds (CR, Theorems 1–3,
  Sections 4–5).
* The top-k algorithms, the Gumbel-noise and peeling mechanisms of DR, and the truncated
  Gaussian mechanisms of CR, Section 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {𝒟 Y : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}

/-- **`η`-bounded range** (Durfee–Rogers, Definition 4.2; Cesar–Rogers, Definition 2.2): a
mechanism `M : Kernel 𝒟 Y` is `η`-bounded range (`η`-BR) for the neighbouring relation `Adj` if
for all neighbours `Adj x x'` and all measurable sets of outcomes `S, S'`,
`P[M(x) ∈ S] P[M(x') ∈ S'] ≤ e^η P[M(x') ∈ S] P[M(x) ∈ S']`.

This is the papers' condition
`P[M(x) = y₁] / P[M(x') = y₁] ≤ e^η P[M(x) = y₂] / P[M(x') = y₂]` with the denominators cleared,
stated for sets of outcomes as in footnote 4 of Durfee–Rogers; on a countable output space with
measurable singletons it is equivalent to the pointwise condition
(`isBoundedRange_iff_forall_singleton`). Clearing the denominators also fixes the meaning of the
ratio when probabilities vanish: the condition forces `M x` and `M x'` to have the same null
sets. The definition is meant for probability kernels (mechanisms). -/
def IsBoundedRange (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (η : ℝ) : Prop :=
  ∀ ⦃x x'⦄, Adj x x' → ∀ ⦃S S' : Set Y⦄, MeasurableSet S → MeasurableSet S' →
    M x S * M x' S' ≤ ENNReal.ofReal (exp η) * (M x' S * M x S')

namespace BoundedRange

variable {μ ν : Measure Y} {t η : ℝ}

/-- The bounded-range condition for a pair of measures: `μ(S) ν(S') ≤ e^η ν(S) μ(S')` for all
measurable `S, S'`. -/
def CrossLe (μ ν : Measure Y) (η : ℝ) : Prop :=
  ∀ ⦃S S' : Set Y⦄, MeasurableSet S → MeasurableSet S' →
    μ S * ν S' ≤ ENNReal.ofReal (exp η) * (ν S * μ S')

/-- `ofReal (exp a) * ofReal (exp b) = ofReal (exp (a + b))`. -/
lemma ofReal_exp_mul_ofReal_exp (a b : ℝ) :
    ENNReal.ofReal (exp a) * ENNReal.ofReal (exp b) = ENNReal.ofReal (exp (a + b)) := by
  rw [← ENNReal.ofReal_mul (exp_pos a).le, exp_add]

/-- A sandwich `e^{t - η} ν ≤ μ ≤ e^t ν` gives the bounded-range condition. -/
lemma crossLe_of_sandwich
    (h1 : ∀ E, MeasurableSet E → μ E ≤ ENNReal.ofReal (exp t) * ν E)
    (h2 : ∀ E, MeasurableSet E → ENNReal.ofReal (exp (t - η)) * ν E ≤ μ E) :
    CrossLe μ ν η := by
  intro S S' hS hS'
  calc μ S * ν S' ≤ (ENNReal.ofReal (exp t) * ν S) * ν S' := by gcongr; exact h1 S hS
    _ = ENNReal.ofReal (exp η) * (ν S * (ENNReal.ofReal (exp (t - η)) * ν S')) := by
        rw [show ENNReal.ofReal (exp t) = ENNReal.ofReal (exp η) * ENNReal.ofReal (exp (t - η)) by
          rw [ofReal_exp_mul_ofReal_exp, add_sub_cancel]]
        ring
    _ ≤ ENNReal.ofReal (exp η) * (ν S * μ S') := by gcongr; exact h2 S' hS'

/-- Under the bounded-range condition, `ν`-null sets are `μ`-null. -/
lemma CrossLe.measure_eq_zero [IsProbabilityMeasure ν] (h : CrossLe μ ν η) {S : Set Y}
    (hS : MeasurableSet S) (hνS : ν S = 0) : μ S = 0 := by
  simpa [hνS] using h hS MeasurableSet.univ

/-- **The sandwich form of bounded range** (Cesar–Rogers, Lemma 2.1, last part; Durfee–Rogers,
discussion after Corollary 4.2): if two probability measures satisfy the bounded-range
condition, then there is `t ∈ [0, η]` with `e^{t - η} ν ≤ μ ≤ e^t ν` on measurable sets. Here
`e^t` is the supremum of the ratios `μ(S) / ν(S)`. -/
lemma CrossLe.exists_sandwich [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : CrossLe μ ν η) : ∃ t ∈ Set.Icc 0 η,
      (∀ E, MeasurableSet E → μ E ≤ ENNReal.ofReal (exp t) * ν E) ∧
      (∀ E, MeasurableSet E → ENNReal.ofReal (exp (t - η)) * ν E ≤ μ E) := by
  set c := ENNReal.ofReal (exp η) with hc_def
  have hc0 : c ≠ 0 := by simp [c, exp_pos]
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  set r := ⨆ (S : Set Y) (_ : MeasurableSet S), μ S / ν S with hr_def
  -- each ratio is at most `e^η`
  have hratio : ∀ S, MeasurableSet S → μ S / ν S ≤ c := fun S hS ↦
    ENNReal.div_le_of_le_mul (by simpa using h hS MeasurableSet.univ)
  have hrc : r ≤ c := iSup₂_le hratio
  have hr1 : 1 ≤ r := by
    refine le_trans ?_ (le_iSup₂ (f := fun (S : Set Y) (_ : MeasurableSet S) ↦ μ S / ν S)
      Set.univ MeasurableSet.univ)
    simp
  -- upper bound `μ ≤ r ν`
  have hup : ∀ E, MeasurableSet E → μ E ≤ r * ν E := by
    intro E hE
    by_cases hνE : ν E = 0
    · simp [h.measure_eq_zero hE hνE]
    · calc μ E = μ E / ν E * ν E := (ENNReal.div_mul_cancel hνE (measure_ne_top ν E)).symm
        _ ≤ r * ν E := by
          gcongr
          exact le_iSup₂ (f := fun (S : Set Y) (_ : MeasurableSet S) ↦ μ S / ν S) E hE
  -- lower bound `r ν ≤ e^η μ`
  have hlow : ∀ E, MeasurableSet E → r * ν E ≤ c * μ E := by
    intro E hE
    have hrE : r * ν E = ⨆ (S : Set Y) (_ : MeasurableSet S), μ S / ν S * ν E := by
      simp_rw [hr_def, ENNReal.iSup_mul]
    rw [hrE]
    refine iSup₂_le fun S hS ↦ ?_
    by_cases hνS : ν S = 0
    · simp [h.measure_eq_zero hS hνS]
    · rw [ENNReal.div_eq_inv_mul, mul_assoc]
      refine (ENNReal.inv_mul_le_iff hνS (measure_ne_top ν S)).2 ?_
      calc μ S * ν E ≤ c * (ν S * μ E) := h hS hE
        _ = ν S * (c * μ E) := by ring
  have hrtop : r ≠ ∞ := ne_top_of_le_ne_top hctop hrc
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos (by positivity) hrtop
  have hexp : ENNReal.ofReal (exp (log r.toReal)) = r := by
    rw [exp_log hrpos, ENNReal.ofReal_toReal hrtop]
  refine ⟨log r.toReal, ⟨log_nonneg ?_, ?_⟩, fun E hE ↦ by rw [hexp]; exact hup E hE,
    fun E hE ↦ ?_⟩
  · simpa using ENNReal.toReal_mono hrtop hr1
  · rw [← exp_le_exp, exp_log hrpos]
    have := ENNReal.toReal_mono hctop hrc
    rwa [hc_def, ENNReal.toReal_ofReal (exp_pos η).le] at this
  · rw [← ENNReal.mul_le_mul_iff_right hc0 hctop, ← mul_assoc, hc_def,
      ofReal_exp_mul_ofReal_exp, add_sub_cancel, hexp]
    exact hlow E hE

/-- **Rényi divergence of a bounded-range pair.** If `μ ≤ e^t ν` and `e^{t - η} ν ≤ μ` on
measurable sets, then `D_a(μ ‖ ν) ≤ η² a / 8` for every `a > 1`. This is the computation behind
the remark after Lemma 3.4 of Cesar–Rogers (`η`-BR implies `(η² / 8)`-zCDP), where the privacy
loss `Z = log (dμ/dν)` takes values in an interval `[t - η, t]` of length `η` and is therefore
`η² / 4`-sub-Gaussian by Hoeffding's lemma, as in Cesar–Rogers, Lemma 3.2. Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc`) is applied to `Z` under `μ` twice: at `-1`, where
`E_μ[e^{-Z}] = 1` gives `E_μ[Z] ≤ η² / 8`, and at `a - 1`, where
`E_μ[e^{(a-1)Z}] = exp ((a - 1) D_a(μ ‖ ν))`. -/
lemma renyiDiv_le_of_sandwich [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h1 : ∀ E, MeasurableSet E → μ E ≤ ENNReal.ofReal (exp t) * ν E)
    (h2 : ∀ E, MeasurableSet E → ENNReal.ofReal (exp (t - η)) * ν E ≤ μ E) {a : ℝ}
    (ha : 1 < a) : renyiDiv a μ ν ≠ ∞ ∧ (renyiDiv a μ ν).toReal ≤ η ^ 2 / 8 * a := by
  set c := ENNReal.ofReal (exp t) with hc_def
  set d := ENNReal.ofReal (exp (t - η)) with hd_def
  have hd0 : d ≠ 0 := by simp [d, exp_pos]
  have hac : μ ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs hνs ↦
    le_antisymm ((h1 s hs).trans (by simp [hνs])) zero_le
  have hca : ν ≪ μ := Measure.AbsolutelyContinuous.mk fun s hs hμs ↦ by
    have := h2 s hs
    rw [hμs, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left hd0
  have hup : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ c :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ν)
      fun s hs _ ↦ by
        rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
        exact h1 s hs
  have hlow : ∀ᵐ x ∂ν, d ≤ μ.rnDeriv ν x :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const fun s hs _ ↦ by
      rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
      exact h2 s hs
  set Z : Y → ℝ := fun x ↦ log (μ.rnDeriv ν x).toReal with hZ_def
  have hbd : ∀ᵐ x ∂μ,
      exp (t - η) ≤ (μ.rnDeriv ν x).toReal ∧ (μ.rnDeriv ν x).toReal ≤ exp t := by
    refine hac.ae_le ?_
    filter_upwards [hup, hlow, Measure.rnDeriv_lt_top μ ν] with x hu hl ht
    exact ⟨(ENNReal.ofReal_le_iff_le_toReal ht.ne).1 hl,
      ENNReal.toReal_le_of_le_ofReal (exp_pos t).le hu⟩
  have hZ : ∀ᵐ x ∂μ, Z x ∈ Set.Icc (t - η) t := by
    filter_upwards [hbd] with x ⟨hl, hu⟩
    have hpos : 0 < (μ.rnDeriv ν x).toReal := (exp_pos _).trans_le hl
    exact ⟨(le_log_iff_exp_le hpos).2 hl, (log_le_iff_le_exp hpos).2 hu⟩
  have hmeas : AEMeasurable Z μ :=
    ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.log).aemeasurable
  have hsub := hasSubgaussianMGF_of_mem_Icc hmeas hZ
  set m := ∫ x, Z x ∂μ
  have hc2 : (((‖t - (t - η)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = η ^ 2 / 4 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, sub_sub_cancel]
    rw [div_pow, sq_abs]
    norm_num
  have hmgf : ∀ s, mgf Z μ s ≤ exp (s * m + η ^ 2 * s ^ 2 / 8) := by
    intro s
    have h := hsub.mgf_le s
    rw [hc2] at h
    have : mgf (fun x ↦ Z x - m) μ s = mgf Z μ s * exp (-(s * m)) := by
      simp only [sub_eq_add_neg]
      rw [mgf_add_const, mul_neg]
    rw [this, ← le_div_iff₀ (exp_pos _), ← exp_sub] at h
    convert h using 2
    ring
  -- `s = -1`: the mean of the privacy loss is at most `η ^ 2 / 8`
  have hmgf1 : mgf Z μ (-1) = 1 := by
    have h_ae : (fun x ↦ exp (-1 * Z x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
      filter_upwards [hbd, Measure.inv_rnDeriv hac] with x ⟨hl, _⟩ hinv
      have hpos : 0 < (μ.rnDeriv ν x).toReal := (exp_pos _).trans_le hl
      rw [← hinv, Pi.inv_apply, ENNReal.toReal_inv, neg_one_mul, exp_neg, hZ_def,
        exp_log hpos]
    rw [mgf, integral_congr_ae h_ae, Measure.integral_toReal_rnDeriv hca, probReal_univ]
  have hm : m ≤ η ^ 2 / 8 := by
    have h := hmgf (-1)
    rw [hmgf1] at h
    have h' : exp 0 ≤ exp (-1 * m + η ^ 2 * (-1) ^ 2 / 8) := by rwa [exp_zero]
    rw [exp_le_exp] at h'
    nlinarith
  -- `s = a - 1`
  have ha1 : 0 < a - 1 := by linarith
  have hJ : mgf Z μ (a - 1) ≤ exp ((a - 1) * (η ^ 2 / 8 * a)) := by
    refine (hmgf (a - 1)).trans (exp_le_exp.2 ?_)
    nlinarith [mul_le_mul_of_nonneg_left hm ha1.le]
  have hJpos : 0 < mgf Z μ (a - 1) := mgf_pos (integrable_exp_mul_of_mem_Icc hmeas hZ)
  have hJeq : mgf Z μ (a - 1) = ∫ x, (μ.rnDeriv ν x).toReal ^ (a - 1) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hbd] with x ⟨hl, _⟩
    have hpos : 0 < (μ.rnDeriv ν x).toReal := (exp_pos _).trans_le hl
    rw [rpow_def_of_pos hpos, hZ_def, mul_comm]
  have h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν := by
    refine Integrable.of_bound
      ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.pow_const a).aestronglyMeasurable
      (exp t ^ a) ?_
    filter_upwards [hup] with x hu
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg ENNReal.toReal_nonneg _)]
    exact rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal (exp_pos t).le hu)
      (by linarith)
  rw [renyiDiv_eq_log_integral_of_one_lt' ha h_int hac]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal', ← hJeq]
  simp only [measure_univ, ENNReal.toReal_one, log_one, mul_zero, add_zero, sub_zero]
  refine max_le ?_ (by positivity)
  rw [inv_mul_le_iff₀ ha1]
  exact (log_le_iff_le_exp hJpos).2 hJ

end BoundedRange

open BoundedRange

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {η η' ε : ℝ}

/-! ### Basic properties -/

/-- The bounded-range condition at a pair of neighbours, for the measures `M x` and `M x'`. -/
lemma IsBoundedRange.crossLe (h : IsBoundedRange M Adj η) {x x' : 𝒟} (hx : Adj x x') :
    CrossLe (M x) (M x') η :=
  fun _ _ hS hS' ↦ h hx hS hS'

/-- `η`-bounded range is monotone in `η`. -/
lemma IsBoundedRange.mono (h : IsBoundedRange M Adj η) (hη : η ≤ η') :
    IsBoundedRange M Adj η' :=
  fun _ _ hx _ _ hS hS' ↦ (h hx hS hS').trans (by gcongr)

/-- The parameter of a bounded-range Markov kernel is nonnegative as soon as some pair of
datasets is neighbouring. -/
lemma IsBoundedRange.nonneg [IsMarkovKernel M] (h : IsBoundedRange M Adj η) {x x' : 𝒟}
    (hx : Adj x x') : 0 ≤ η := by
  have := h hx MeasurableSet.univ MeasurableSet.univ
  simp only [measure_univ, mul_one, ENNReal.one_le_ofReal] at this
  exact one_le_exp_iff.1 this

/-- **Bounded range as a sandwich** (Cesar–Rogers, Lemma 2.1, last part, with its converse; the
range interpretation after Corollary 4.2 of Durfee–Rogers): a Markov kernel is `η`-BR iff for all
neighbours `x, x'` there is `t ∈ [0, η]` with `e^{t - η} M(x') ≤ M(x) ≤ e^t M(x')` on
measurable sets, that is, the privacy loss `log (dM(x)/dM(x'))` takes values in `[t - η, t]`. -/
theorem isBoundedRange_iff_exists_sandwich [IsMarkovKernel M] :
    IsBoundedRange M Adj η ↔ ∀ ⦃x x'⦄, Adj x x' → ∃ t ∈ Set.Icc 0 η,
      (∀ E, MeasurableSet E → M x E ≤ ENNReal.ofReal (exp t) * M x' E) ∧
      (∀ E, MeasurableSet E → ENNReal.ofReal (exp (t - η)) * M x' E ≤ M x E) := by
  refine ⟨fun h x x' hx ↦ (h.crossLe hx).exists_sandwich, fun h x x' hx S S' hS hS' ↦ ?_⟩
  obtain ⟨t, -, h1, h2⟩ := h hx
  exact crossLe_of_sandwich h1 h2 hS hS'

/-- **Cesar–Rogers, Lemma 2.1, last part** (pointwise form): if `M` is `η`-BR, then for each pair
of neighbours `x, x'` there is `t ∈ [0, η]` such that
`t - η ≤ log (P[M(x) = y] / P[M(x') = y]) ≤ t` for every outcome `y` with `P[M(x) = y] > 0`
(for the other outcomes the ratio is `0 / 0`). -/
theorem IsBoundedRange.exists_log_mem_Icc [MeasurableSingletonClass Y] [IsMarkovKernel M]
    (h : IsBoundedRange M Adj η) {x x' : 𝒟} (hx : Adj x x') : ∃ t ∈ Set.Icc 0 η, ∀ y : Y,
      0 < (M x).real {y} → log ((M x).real {y} / (M x').real {y}) ∈ Set.Icc (t - η) t := by
  obtain ⟨t, ht, h1, h2⟩ := isBoundedRange_iff_exists_sandwich.1 h hx
  refine ⟨t, ht, fun y hy ↦ ?_⟩
  have h1' : (M x).real {y} ≤ exp t * (M x').real {y} := by
    have := ENNReal.toReal_mono (by finiteness) (h1 {y} (measurableSet_singleton y))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos t).le] at this
  have h2' : exp (t - η) * (M x').real {y} ≤ (M x).real {y} := by
    have := ENNReal.toReal_mono (by finiteness) (h2 {y} (measurableSet_singleton y))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at this
  have hy' : 0 < (M x').real {y} := by
    by_contra hneg
    have h0 : (M x').real {y} = 0 := le_antisymm (not_lt.1 hneg) measureReal_nonneg
    rw [h0, mul_zero] at h1'
    linarith
  have hq : 0 < (M x).real {y} / (M x').real {y} := div_pos hy hy'
  refine ⟨(le_log_iff_exp_le hq).2 ?_, (log_le_iff_le_exp hq).2 ?_⟩
  · rwa [le_div_iff₀ hy']
  · rwa [div_le_iff₀ hy']

/-- **Durfee–Rogers, Corollary 4.2, last claim**: if `M` is `η`-BR, then for neighbours `x, x'`
the log-ratios `ln (P[M(x) = y] / P[M(x') = y])` over outputs of positive probability differ by
at most `η`, that is, their supremum minus their infimum is at most `η`. -/
theorem IsBoundedRange.log_div_sub_log_div_le [MeasurableSingletonClass Y] [IsMarkovKernel M]
    (h : IsBoundedRange M Adj η) {x x' : 𝒟} (hx : Adj x x') {y y' : Y}
    (hy : 0 < (M x).real {y}) (hy' : 0 < (M x).real {y'}) :
    log ((M x).real {y} / (M x').real {y}) - log ((M x).real {y'} / (M x').real {y'}) ≤ η := by
  obtain ⟨t, -, ht⟩ := h.exists_log_mem_Icc hx
  linarith [(ht y hy).2, (ht y' hy').1]

/-- On a countable output space with measurable singletons, `η`-bounded range is the pointwise
condition of Durfee–Rogers, Definition 4.2, and Cesar–Rogers, Definition 2.2, with the
denominators cleared: `P[M(x) = y₁] P[M(x') = y₂] ≤ e^η P[M(x') = y₁] P[M(x) = y₂]`. -/
theorem isBoundedRange_iff_forall_singleton [Countable Y] [MeasurableSingletonClass Y] :
    IsBoundedRange M Adj η ↔ ∀ ⦃x x'⦄, Adj x x' → ∀ y₁ y₂ : Y,
      M x {y₁} * M x' {y₂} ≤ ENNReal.ofReal (exp η) * (M x' {y₁} * M x {y₂}) := by
  refine ⟨fun h x x' hx y₁ y₂ ↦
    h hx (measurableSet_singleton y₁) (measurableSet_singleton y₂), fun h x x' hx S S' hS hS' ↦ ?_⟩
  rw [← (M x).tsum_indicator_apply_singleton S hS, ← (M x').tsum_indicator_apply_singleton S' hS',
    ← (M x').tsum_indicator_apply_singleton S hS, ← (M x).tsum_indicator_apply_singleton S' hS',
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y₁ ↦ ?_
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y₂ ↦ ?_
  by_cases h₁ : y₁ ∈ S <;> by_cases h₂ : y₂ ∈ S' <;> simp [h₁, h₂, h hx y₁ y₂]

/-- **Durfee–Rogers, Definition 4.2, and Cesar–Rogers, Definition 2.2, as stated**: on a countable
output space with measurable singletons, for a finite kernel such that `P[M(x') = y] > 0` for
all neighbours `Adj x x'` and all outputs `y` (so that the ratios in the definition are defined),
`η`-bounded range is the condition
`P[M(x) = y₁] / P[M(x') = y₁] ≤ e^η P[M(x) = y₂] / P[M(x') = y₂]`. -/
theorem isBoundedRange_iff_forall_singleton_div [Countable Y] [MeasurableSingletonClass Y]
    [IsFiniteKernel M] (hpos : ∀ ⦃x x'⦄, Adj x x' → ∀ y : Y, 0 < (M x').real {y}) :
    IsBoundedRange M Adj η ↔ ∀ ⦃x x'⦄, Adj x x' → ∀ y₁ y₂ : Y,
      (M x).real {y₁} / (M x').real {y₁} ≤ exp η * ((M x).real {y₂} / (M x').real {y₂}) := by
  rw [isBoundedRange_iff_forall_singleton]
  refine forall₂_congr fun x x' ↦ forall_congr' fun hx ↦ forall₂_congr fun y₁ y₂ ↦ ?_
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos η).le,
    ← measureReal_def, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    div_le_iff₀ (hpos hx y₁),
    show exp η * ((M x).real {y₂} / (M x').real {y₂}) * (M x').real {y₁}
      = exp η * ((M x').real {y₁} * (M x).real {y₂}) / (M x').real {y₂} by ring,
    le_div_iff₀ (hpos hx y₂)]

/-- The bounded-range condition is symmetric: if `M` is `η`-BR for `Adj`, it is `η`-BR for the
reversed relation. In particular the two-sided Rényi bounds required by Cesar–Rogers,
Definition 2.7, follow from `IsBoundedRange.isZCDP` even for a non-symmetric `Adj`. -/
lemma IsBoundedRange.symm (h : IsBoundedRange M Adj η) :
    IsBoundedRange M (fun x x' ↦ Adj x' x) η := by
  intro x x' hx S S' hS hS'
  calc M x S * M x' S' = M x' S' * M x S := mul_comm _ _
    _ ≤ ENNReal.ofReal (exp η) * (M x S' * M x' S) := h hx hS' hS
    _ = ENNReal.ofReal (exp η) * (M x' S * M x S') := by ring

/-! ### Bounded range and pure differential privacy -/

/-- **Durfee–Rogers, Corollary 4.2; Cesar–Rogers, Lemma 2.1** (first direction): an `η`-BR
Markov kernel is `η`-differentially private. -/
theorem IsBoundedRange.isEpsDP [IsMarkovKernel M] (h : IsBoundedRange M Adj η) :
    IsEpsDP M Adj η := by
  refine isEpsDP_iff_le_smul.2 fun x x' hx ↦ Measure.le_iff.2 fun E hE ↦ ?_
  obtain ⟨t, ht, h1, -⟩ := isBoundedRange_iff_exists_sandwich.1 h hx
  rw [smul_apply, smul_eq_mul]
  exact (h1 E hE).trans (by gcongr; exact ht.2)

/-- **Durfee–Rogers, Corollary 4.2; Cesar–Rogers, Lemma 2.1** (second direction): an `ε`-DP
Markov kernel is `2ε`-BR, for a symmetric neighbouring relation. -/
theorem IsEpsDeltaDP.isBoundedRange [IsMarkovKernel M] [Std.Symm Adj] (h : IsEpsDP M Adj ε) :
    IsBoundedRange M Adj (2 * ε) := by
  have hle := isEpsDP_iff_le_smul.1 h
  intro x x' hx S S' hS hS'
  refine crossLe_of_sandwich (t := ε) (fun E hE ↦ ?_) (fun E hE ↦ ?_) hS hS'
  · simpa using Measure.le_iff'.1 (hle hx) E
  · have h' : M x' E ≤ ENNReal.ofReal (exp ε) * M x E := by
      simpa using Measure.le_iff'.1 (hle (Std.Symm.symm _ _ hx)) E
    calc ENNReal.ofReal (exp (ε - 2 * ε)) * M x' E
        ≤ ENNReal.ofReal (exp (-ε)) * (ENNReal.ofReal (exp ε) * M x E) := by
          rw [show ε - 2 * ε = -ε by ring]
          gcongr
      _ = M x E := by
          rw [← mul_assoc, ofReal_exp_mul_ofReal_exp, neg_add_cancel, exp_zero,
            ENNReal.ofReal_one, one_mul]

/-- An `ε`-DP Markov kernel is `2ε`-BR (`IsEpsDeltaDP.isBoundedRange`). -/
alias IsEpsDP.isBoundedRange := IsEpsDeltaDP.isBoundedRange

/-! ### Bounded range implies zero-concentrated differential privacy -/

/-- **`η`-bounded range implies `(η² / 8)`-zCDP** (Cesar–Rogers, remark after Lemma 3.4,
which states `(ξ, η² / 8)`-zCDP with `ξ ≤ 0`; the form proved here, with `ξ = 0`, follows from it
by monotonicity). For every pair of neighbours, the privacy loss lies in an interval of length
`η`, so it is `η² / 4`-sub-Gaussian by Hoeffding's lemma, as in Cesar–Rogers, Lemma 3.2; see
`BoundedRange.renyiDiv_le_of_sandwich`. No symmetry of `Adj` is needed. For comparison, `ε`-DP
gives `(ε² / 2)`-zCDP (`IsEpsDeltaDP.isZCDP`), so a `2ε`-BR mechanism such as an `ε`-DP one is
also `(ε² / 2)`-zCDP, and an `ε`-BR one is `(ε² / 8)`-zCDP. -/
theorem IsBoundedRange.isZCDP [IsMarkovKernel M] (h : IsBoundedRange M Adj η) :
    IsZCDP M Adj 0 (η ^ 2 / 8) := by
  refine isZCDP_iff_toReal.2 fun x x' hx α hα ↦ ?_
  obtain ⟨t, -, h1, h2⟩ := isBoundedRange_iff_exists_sandwich.1 h hx
  rw [zero_add]
  exact renyiDiv_le_of_sandwich h1 h2 hα

/-- An `η`-BR Markov kernel is `(η² / 8 + η √(log (1 / δ) / 2), δ)`-DP for every `δ > 0` and
`η ≥ 0`: `IsBoundedRange.isZCDP` followed by the conversion of Bun–Steinke (Cesar–Rogers,
Lemma 2.3). -/
theorem IsBoundedRange.isEpsDeltaDP [IsMarkovKernel M] (h : IsBoundedRange M Adj η)
    (hη : 0 ≤ η) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP M Adj (η ^ 2 / 8 + η * √(log (1 / δ) / 2)) δ := by
  have := h.isZCDP.isEpsDeltaDP' hδ
  rwa [show η ^ 2 / 8 * log (1 / δ) = (η / 2) ^ 2 * (log (1 / δ) / 2) by ring,
    sqrt_mul (sq_nonneg _), sqrt_sq (by linarith),
    show 2 * (η / 2 * √(log (1 / δ) / 2)) = η * √(log (1 / δ) / 2) by ring] at this

/-! ### Composition -/

/-- **Composition of bounded-range mechanisms via zCDP** (the zCDP composition theorem of
Bun–Steinke, Lemma 1.7, `IsZCDP.piKernel`, applied to the remark after Lemma 3.4 of Cesar–Rogers,
`IsBoundedRange.isZCDP`; non-adaptive): if each `M i` is `η i`-BR, the product mechanism
`ZCDP.piKernel M`, releasing independent outputs of all of them, is `(∑ η i² / 8)`-zCDP. -/
theorem isZCDP_piKernel_of_isBoundedRange {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    {η : ι → ℝ} (h : ∀ i, IsBoundedRange (M i) Adj (η i)) :
    IsZCDP (ZCDP.piKernel M) Adj 0 (∑ i, η i ^ 2 / 8) := by
  simpa using IsZCDP.piKernel fun i ↦ (h i).isZCDP

/-- **Composition of bounded-range mechanisms, approximate-DP form.** The product mechanism
`ZCDP.piKernel M` of mechanisms `M i` that are `η i`-BR is
`(∑ η i² / 8 + √((∑ η i²) log (1 / δ) / 2), δ)`-DP for every `δ > 0`.

This strengthens, in the non-adaptive case, the third bound in equation (4) of Durfee–Rogers,
Lemma 4.4, `∑ η i² / 2 + √((∑ η i²) log (1 / δ) / 2)`: the deviation term is the same, and the
mean term `η i² / 2` (the expected privacy loss of an `η i`-DP mechanism, used in their proof) is
improved to `η i² / 8` (the bound for `η i`-BR mechanisms from Hoeffding's lemma). It is also
the non-adaptive, BR-only case of equation (3) of Cesar–Rogers, with the weaker mean term
`η² / 8` in place of their `η / (e^η - 1) - 1 - log (η / (e^η - 1))` (not formalized), and with
heterogeneous `η i` allowed; CR's (3) holds more generally, under set-wise adaptive composition
with a shared parameter `η`. -/
theorem isEpsDeltaDP_piKernel_of_isBoundedRange {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    {η : ι → ℝ} (h : ∀ i, IsBoundedRange (M i) Adj (η i)) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP (ZCDP.piKernel M) Adj
      (∑ i, η i ^ 2 / 8 + √((∑ i, η i ^ 2) * log (1 / δ) / 2)) δ := by
  have := (isZCDP_piKernel_of_isBoundedRange h).isEpsDeltaDP' hδ
  have e : 2 * √((∑ i, η i ^ 2 / 8) * log (1 / δ)) = √((∑ i, η i ^ 2) * log (1 / δ) / 2) := by
    rw [show (∑ i, η i ^ 2) * log (1 / δ) / 2 = 2 ^ 2 * ((∑ i, η i ^ 2 / 8) * log (1 / δ)) by
      rw [← Finset.sum_div]; ring, sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num),
      sqrt_sq (by norm_num)]
  rwa [e] at this

/-- **Composition of `k` mechanisms that are `η`-BR, approximate-DP form**: the homogeneous case
of `isEpsDeltaDP_piKernel_of_isBoundedRange`. The product mechanism `ZCDP.piKernel M` of
`k = |ι|` mechanisms, each `η`-BR with `η ≥ 0`, is
`(k η² / 8 + η √(k log (1 / δ) / 2), δ)`-DP for every `δ > 0`. Compare
`isEpsDeltaDP_pi_of_isEpsDeltaDP`, which gives `(k ε² / 2 + ε √(2 k log (1 / δ)), δ)` for `k`
mechanisms that are `ε`-DP. -/
theorem isEpsDeltaDP_piKernel_of_isBoundedRange_const {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    (hη : 0 ≤ η) (h : ∀ i, IsBoundedRange (M i) Adj η) {δ : ℝ} (hδ : 0 < δ) :
    IsEpsDeltaDP (ZCDP.piKernel M) Adj
      (Fintype.card ι * η ^ 2 / 8 + η * √(Fintype.card ι * log (1 / δ) / 2)) δ := by
  have := (isZCDP_piKernel_of_isBoundedRange h).isEpsDeltaDP' hδ
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  rwa [show (Fintype.card ι : ℝ) * (η ^ 2 / 8) * log (1 / δ)
      = (η / 2) ^ 2 * (Fintype.card ι * log (1 / δ) / 2) by ring,
    sqrt_mul (sq_nonneg _), sqrt_sq (by linarith),
    show 2 * (η / 2 * √(Fintype.card ι * log (1 / δ) / 2))
      = η * √(Fintype.card ι * log (1 / δ) / 2) by ring, ← mul_div_assoc] at this

/-- **Adaptive composition of two bounded-range mechanisms via zCDP** (the adaptive zCDP
composition of Bun–Steinke, Lemma 2.3, `IsZCDP.compProd`, applied to the remark after Lemma 3.4
of Cesar–Rogers): if `M` is `η`-BR and, for every first output `y`, the second
mechanism `M' (·, y)` is `η'`-BR, then the mechanism releasing both outputs (`M ⊗ₖ M'`) is
`((η² + η'²) / 8)`-zCDP. It assumes `Y` countable or `Z` countably generated. -/
theorem isZCDP_compProd_of_isBoundedRange {Z : Type*} {mZ : MeasurableSpace Z}
    [IsMarkovKernel M] {M' : Kernel (𝒟 × Y) Z} [IsMarkovKernel M']
    [MeasurableSpace.CountableOrCountablyGenerated Y Z] (h : IsBoundedRange M Adj η)
    (h' : ∀ y, IsBoundedRange (M'.sectL y) Adj η') :
    IsZCDP (M ⊗ₖ M') Adj 0 ((η ^ 2 + η' ^ 2) / 8) := by
  simpa [add_div] using h.isZCDP.compProd fun y ↦ (h' y).isZCDP

/-! ### The exponential mechanism -/

section Exponential

variable {R : Type*} [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
  {u : 𝒟 → R → ℝ} {Δ D : ℝ}

namespace BoundedRange

/-- The probability that the exponential mechanism outputs `r`. -/
lemma exponentialMechanism_singleton (hu : ∀ r, Measurable fun x ↦ u x r) (x : 𝒟) (r : R) :
    exponentialMechanism u ε Δ x {r} = ENNReal.ofReal (exponentialMechanismProb u ε Δ x r) := by
  rw [exponentialMechanism_apply hu, withDensity_apply _ (measurableSet_singleton r)]
  simp

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
/-- With sensitivity parameter `Δ̃ / 2`, the exponential mechanism outputs `r` with probability
proportional to `exp (ε u(x, r) / Δ̃)`, the normalization of Cesar–Rogers, Definition 2.3. -/
lemma exponentialMechanismProb_half (x : 𝒟) (r : R) :
    exponentialMechanismProb u ε (Δ / 2) x r =
      exp (ε * u x r / Δ) / ∑ r', exp (ε * u x r' / Δ) := by
  simp only [exponentialMechanismProb, mul_div_cancel₀ Δ two_ne_zero]

end BoundedRange

open BoundedRange

/-- **The exponential mechanism is bounded range, general form.** If, for all neighbours `x, x'`,
the change of score `u(x, r) - u(x', r)` varies by at most `D` over the outputs `r`, then the
exponential mechanism `exponentialMechanism u ε Δ` (output `r` with probability proportional to
`exp (ε u(x, r) / (2Δ))`) is `(ε D / (2Δ))`-BR. The normalizing constants cancel in the
bounded-range ratio, which is the computation in the proof of Lemma 4.3 of Durfee–Rogers. -/
theorem isBoundedRange_exponentialMechanism_of_range (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 ≤ ε) (hΔ : 0 < Δ)
    (hD : ∀ ⦃x x'⦄, Adj x x' → ∀ r r', (u x r - u x' r) - (u x r' - u x' r') ≤ D) :
    IsBoundedRange (exponentialMechanism u ε Δ) Adj (ε * D / (2 * Δ)) := by
  refine isBoundedRange_iff_forall_singleton.2 fun x x' hx r₁ r₂ ↦ ?_
  have : Nonempty R := ⟨r₁⟩
  simp only [exponentialMechanism_singleton hu]
  rw [← ENNReal.ofReal_mul (exponentialMechanismProb_nonneg ..),
    ← ENNReal.ofReal_mul (exponentialMechanismProb_nonneg ..),
    ← ENNReal.ofReal_mul (exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  set w : 𝒟 → R → ℝ := fun x r ↦ exp (ε * u x r / (2 * Δ)) with hw
  have hZ := ExponentialMechanism.sum_exp_pos u ε Δ x
  have hZ' := ExponentialMechanism.sum_exp_pos u ε Δ x'
  have key : w x r₁ * w x' r₂ ≤ exp (ε * D / (2 * Δ)) * (w x' r₁ * w x r₂) := by
    simp only [hw, ← exp_add]
    rw [exp_le_exp, ← add_div, ← add_div, ← add_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (hD hx r₁ r₂) hε]
  simp only [exponentialMechanismProb]
  rw [div_mul_div_comm, div_mul_div_comm, ← mul_div_assoc,
    mul_comm (∑ r, exp (ε * u x' r / (2 * Δ)))]
  exact div_le_div_of_nonneg_right key (by positivity)

/-- **Durfee–Rogers, Lemma 4.3** (first part), in the normalization of Dwork–Roth: if the score
has sensitivity at most `Δ > 0` (`|u(x, r) - u(x', r)| ≤ Δ` for neighbours `x, x'`), then the
exponential mechanism `exponentialMechanism u ε Δ`, which outputs `r` with probability
proportional to `exp (ε u(x, r) / (2Δ))`, is `ε`-BR. (Durfee–Rogers's mechanism `EM_q` with
parameter `ε` uses `exp (ε u(x, r) / Δ)`, which is the present one with `2ε`, and is `2ε`-BR.) -/
theorem isBoundedRange_exponentialMechanism (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 ≤ ε) (hΔ : 0 < Δ) (hΔu : ∀ ⦃x x'⦄, Adj x x' → ∀ r, |u x r - u x' r| ≤ Δ) :
    IsBoundedRange (exponentialMechanism u ε Δ) Adj ε := by
  have hD : ∀ ⦃x x'⦄, Adj x x' → ∀ r r', (u x r - u x' r) - (u x r' - u x' r') ≤ 2 * Δ := by
    intro x x' hx r r'
    linarith [(abs_le.1 (hΔu hx r)).2, (abs_le.1 (hΔu hx r')).1]
  have h := isBoundedRange_exponentialMechanism_of_range hu hε hΔ hD
  rwa [mul_div_assoc, div_self (by positivity), mul_one] at h

/-- **Durfee–Rogers, Lemma 4.3** (second part, monotonic scores), in the normalization of
Dwork–Roth: if the score has sensitivity at most `Δ > 0` and is monotonic in the dataset (for
neighbours `x, x'`, either `u(x, r) ≤ u(x', r)` for all `r` or `u(x', r) ≤ u(x, r)` for all `r`),
then `exponentialMechanism u ε Δ` is `(ε / 2)`-BR. -/
theorem isBoundedRange_exponentialMechanism_of_monotone (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 ≤ ε) (hΔ : 0 < Δ) (hΔu : ∀ ⦃x x'⦄, Adj x x' → ∀ r, |u x r - u x' r| ≤ Δ)
    (hmono : ∀ ⦃x x'⦄, Adj x x' → (∀ r, u x r ≤ u x' r) ∨ (∀ r, u x' r ≤ u x r)) :
    IsBoundedRange (exponentialMechanism u ε Δ) Adj (ε / 2) := by
  have hD : ∀ ⦃x x'⦄, Adj x x' → ∀ r r', (u x r - u x' r) - (u x r' - u x' r') ≤ Δ := by
    intro x x' hx r r'
    rcases hmono hx with hm | hm
    · linarith [hm r, (abs_le.1 (hΔu hx r')).1]
    · linarith [hm r', (abs_le.1 (hΔu hx r)).2]
  have h := isBoundedRange_exponentialMechanism_of_range hu hε hΔ hD
  rwa [show ε * Δ / (2 * Δ) = ε / 2 by field_simp] at h

/-- **The exponential mechanism of Cesar–Rogers** (Definition 2.3, after Dong–Durfee–Rogers) is
`ε`-BR, as stated after that definition: if `Δ̃ > 0` bounds the range of the score,
`(u(x, r) - u(x', r)) - (u(x, r') - u(x', r')) ≤ Δ̃` for all neighbours `x, x'` and all `r, r'`,
then the mechanism that outputs `r` with probability proportional to `exp (ε u(x, r) / Δ̃)`,
which is `exponentialMechanism u ε (Δ̃ / 2)` (`BoundedRange.exponentialMechanismProb_half`), is
`ε`-BR. -/
theorem isBoundedRange_exponentialMechanism_range (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 ≤ ε) (hΔ : 0 < Δ)
    (hrange : ∀ ⦃x x'⦄, Adj x x' → ∀ r r', (u x r - u x' r) - (u x r' - u x' r') ≤ Δ) :
    IsBoundedRange (exponentialMechanism u ε (Δ / 2)) Adj ε := by
  have h := isBoundedRange_exponentialMechanism_of_range hu hε (half_pos hΔ) hrange
  rwa [show ε * Δ / (2 * (Δ / 2)) = ε by field_simp] at h

/-- **The exponential mechanism is `(ε² / 8)`-zCDP** (Cesar–Rogers: the exponential mechanism
is `ε`-BR, after Definition 2.3, and `ε`-BR implies `(ε² / 8)`-zCDP, remark after Lemma 3.4):
if the score has sensitivity at most `Δ > 0`, then `exponentialMechanism u ε Δ` is
`(ε² / 8)`-zCDP. Going through pure DP instead
(`isEpsDeltaDP_exponentialMechanism` and `IsEpsDeltaDP.isZCDP`) only gives `(ε² / 2)`-zCDP. -/
theorem isZCDP_exponentialMechanism [Nonempty R] (hu : ∀ r, Measurable fun x ↦ u x r)
    (hε : 0 ≤ ε) (hΔ : 0 < Δ) (hΔu : ∀ ⦃x x'⦄, Adj x x' → ∀ r, |u x r - u x' r| ≤ Δ) :
    IsZCDP (exponentialMechanism u ε Δ) Adj 0 (ε ^ 2 / 8) :=
  have := isMarkovKernel_exponentialMechanism (ε := ε) (Δ := Δ) hu
  (isBoundedRange_exponentialMechanism hu hε hΔ hΔu).isZCDP

/-- **Composition of `k` exponential mechanisms** (the improved composition of exponential
mechanisms of Durfee–Rogers, §4.2, through zCDP; this is the non-adaptive, BR-only case of
Cesar–Rogers, equation (3), with the weaker mean term `ε² / 8`, see
`isEpsDeltaDP_piKernel_of_isBoundedRange`). Let
`u i : 𝒟 → R i → ℝ`, `i ∈ ι`, be `k = |ι|` scores, each of sensitivity at most `Δ > 0`, and let
`K` release independent outputs of the exponential mechanisms `exponentialMechanism (u i) ε Δ`
(`K x = ∏ i, exponentialMechanism (u i) ε Δ x`). Then `K` is `(k ε² / 8)`-zCDP, and it is
`(k ε² / 8 + ε √(k log (1 / δ) / 2), δ)`-DP for every `δ > 0`. Through pure DP the same
composition is only `(k ε² / 2)`-zCDP (`isZCDP_pi_of_isEpsDeltaDP`). -/
theorem isZCDP_pi_exponentialMechanism {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] [∀ i, MeasurableSpace (R i)]
    [∀ i, MeasurableSingletonClass (R i)] {u : ∀ i, 𝒟 → R i → ℝ}
    (hu : ∀ i r, Measurable fun x ↦ u i x r) (hε : 0 ≤ ε) (hΔ : 0 < Δ)
    (hΔu : ∀ i ⦃x x'⦄, Adj x x' → ∀ r, |u i x r - u i x' r| ≤ Δ) {K : Kernel 𝒟 (∀ i, R i)}
    (hK : ∀ x, K x = Measure.pi fun i ↦ exponentialMechanism (u i) ε Δ x) :
    IsZCDP K Adj 0 (Fintype.card ι * ε ^ 2 / 8) ∧ ∀ δ : ℝ, 0 < δ →
      IsEpsDeltaDP K Adj (Fintype.card ι * ε ^ 2 / 8 + ε * √(Fintype.card ι * log (1 / δ) / 2))
        δ := by
  have (i : ι) : IsMarkovKernel (exponentialMechanism (u i) ε Δ) :=
    isMarkovKernel_exponentialMechanism (hu i)
  obtain rfl : K = ZCDP.piKernel fun i ↦ exponentialMechanism (u i) ε Δ := Kernel.ext hK
  have h := fun i ↦ isBoundedRange_exponentialMechanism (hu i) hε hΔ (hΔu i)
  refine ⟨?_, fun δ hδ ↦ isEpsDeltaDP_piKernel_of_isBoundedRange_const hε h hδ⟩
  simpa [← mul_div_assoc] using isZCDP_piKernel_of_isBoundedRange h

end Exponential

end InformationTheory
