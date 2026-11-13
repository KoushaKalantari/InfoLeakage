/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Laplace
public import InfoLeakage.SmoothSensitivity.Admissible
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Laplace noise calibrated to smooth sensitivity

This file formalizes the Laplace instance of the smooth sensitivity framework of K. Nissim,
S. Raskhodnikova and A. Smith, *Smooth sensitivity and sampling in private data analysis*,
STOC 2007 (result numbers refer to the full version, Draft Full Version v1.0, May 17, 2011):
the standard Laplace distribution `Lap(1)` is `(ε/2, ε/(2 ln(2/δ)))`-admissible, and releasing
`f(x) + 2 S(x)/ε · η` with `η ∼ Lap(1)` and `S` an `ε/(2 ln(2/δ))`-smooth upper bound on the
local sensitivity of `f` is `(ε, δ)`-differentially private.

The Laplace distribution is `laplaceMeasure 0 1` from `InfoLeakage.DP.Laplace`, with density
`h(z) = e^{-|z|}/2`. **Restriction:** as in the rest of this directory, the database domain `D`
is **finite**, whereas the paper allows any `D`.

## Main statements (paper result → Lean name)

* Lemma 2.9, case `d = 1`: `isAdmissibleNoise_laplace` (for `ε ∈ (0, 1]` and `δ ∈ (0, 1)`).
* Corollary 2.4, item 2: `isEpsDeltaDP_smoothNoiseMechanism_laplace` (for `ε ∈ (0, 1]`,
  `δ ∈ (0, 1)`), in the stronger form `(ε, δ/2)` that the proof gives
  (`isEpsDeltaDP_smoothNoiseMechanism_laplace_half`); with `S = S*_{f,β}` (Lemma 2.3):
  `isEpsDeltaDP_smoothNoiseMechanism_laplace_smoothSensitivity`.
* The sliding property holds with no additive term: `laplace_sliding`.

## Notes on the paper

* Corollary 2.4 assumes only `δ ∈ (0, 1)`, but it rests on Lemma 2.9, which also assumes
  `ε ∈ (0, 1)`; we assume `ε ∈ (0, 1]`. A bound on `ε` is needed, at least for large `ε`
  (numerical check, not formalized): for Corollary 2.4, item 2, take `n = 1`, `D = {0, 1}`,
  `f(x) = 1`, `f(y) = 0`, `S(x) = e^β`, `S(y) = 1` (a `β`-smooth upper bound), `ε = 8`,
  `δ = 0.65`, `β = ε/(2 ln(2/δ)) ≈ 3.559`; the hockey-stick divergence
  `sup_E (P[A(x) ∈ E] - e^ε P[A(y) ∈ E])` is `≈ 0.697 > δ`. Likewise the dilation property of
  Lemma 2.9 fails at `ε = 8`, `δ = 0.1` (additive term `≈ 0.110 > δ/2`).
* Proof of Lemma 2.9 (Section 2.2.2, p. 10, v1.0), dilation by `λ > 0`: the step
  "the median of `‖Z‖₁` is at most `d` and `δ' < 1/2`, so `ρ_{δ'}(‖Z‖₁) > d`" does not follow
  (a quantile above the median need not exceed `d`). For `d = 1`, `ρ_{δ/2}(|Z|) = ln(2/δ)`,
  which is `< 1` when `δ > 2/e`, and then `β = ε/(2 ln(2/δ)) > ε/2`, so the bound "`λd` is at most
  `ε/2`" fails. The statement for `d = 1` is still true: the formal proof handles this regime
  by spending the additive term `δ/2`.
* In the same proof (case `λ < 0`), the event `G = {|z| ≤ ρ_δ}` is said to have probability
  `1 - δ`, but `Pr_h[Ḡ] ≤ δ/2` is used, so `ρ_{δ/2}` is meant. As written, both dilation cases
  bound the ratio `h'/h` of the dilated density `h'(z) = e^λ h(e^λ z)` to `h` from above,
  whereas `Pr_h[S] ≤ e^{ε/2} Pr_{h'}[S] + δ/2` needs an upper bound on `h/h'` off an event of
  `h`-probability at most `δ/2`. The formal proof bounds `h/h'` directly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace InformationTheory

namespace SmoothSensitivity

/-! ### Change of variables for the standard Laplace distribution -/

private lemma laplace_apply {E : Set ℝ} (hE : MeasurableSet E) :
    laplaceMeasure 0 1 E = ∫⁻ w in E, laplacePDF 0 1 w :=
  withDensity_apply _ hE

/-- `P[Z ∈ E + Δ] = ∫_E h(w + Δ) dw` for `Z ∼ Lap(1)`. -/
private lemma laplace_preimage_sub {E : Set ℝ} (hE : MeasurableSet E) (Δ : ℝ) :
    laplaceMeasure 0 1 ((· - Δ) ⁻¹' E) = ∫⁻ w in E, laplacePDF 0 1 (w + Δ) := by
  have hm : Measurable fun z : ℝ ↦ z - Δ := by fun_prop
  rw [laplaceMeasure, withDensity_apply _ (hE.preimage hm), ← lintegral_indicator (hE.preimage hm),
    ← lintegral_indicator hE,
    ← lintegral_sub_right_eq_self (fun w ↦ E.indicator (fun w ↦ laplacePDF 0 1 (w + Δ)) w) Δ]
  congr 1
  ext z
  by_cases hz : z - Δ ∈ E <;> simp [Set.indicator, hz]

/-- `P[Z ∈ c⁻¹ · E] = c⁻¹ ∫_E h(w / c) dw` for `Z ∼ Lap(1)` and `c > 0`. -/
private lemma laplace_preimage_mul {E : Set ℝ} (hE : MeasurableSet E) {c : ℝ} (hc : 0 < c) :
    laplaceMeasure 0 1 ((c * ·) ⁻¹' E) =
      ENNReal.ofReal c⁻¹ * ∫⁻ w in E, laplacePDF 0 1 (w / c) := by
  have hm : Measurable fun z : ℝ ↦ c * z := by fun_prop
  have hG : Measurable (E.indicator fun w ↦ laplacePDF 0 1 (w / c)) :=
    (by fun_prop : Measurable fun w ↦ laplacePDF 0 1 (w / c)).indicator hE
  calc laplaceMeasure 0 1 ((c * ·) ⁻¹' E)
      = ∫⁻ z, (E.indicator fun w ↦ laplacePDF 0 1 (w / c)) (c * z) := by
        rw [laplaceMeasure, withDensity_apply _ (hE.preimage hm),
          ← lintegral_indicator (hE.preimage hm)]
        congr 1
        ext z
        by_cases hz : c * z ∈ E <;> simp [Set.indicator, hz, hc.ne']
    _ = ∫⁻ w, (E.indicator fun w ↦ laplacePDF 0 1 (w / c)) w ∂(Measure.map (c * ·) volume) :=
        (lintegral_map hG hm).symm
    _ = _ := by
        rw [Real.map_volume_mul_left hc.ne', lintegral_smul_measure, abs_of_pos (inv_pos.2 hc),
          lintegral_indicator hE, smul_eq_mul]

/-- Passing from an `ℝ≥0∞` inequality between values of a finite measure to its real form. -/
private lemma measureReal_le_of_le {μ : Measure ℝ} [IsFiniteMeasure μ] {E F : Set ℝ} {k d : ℝ}
    (hk : 0 ≤ k) (hd : 0 ≤ d) (h : μ E ≤ ENNReal.ofReal k * μ F + ENNReal.ofReal d) :
    μ.real E ≤ k * μ.real F + d := by
  have := ENNReal.toReal_mono (by finiteness) h
  rwa [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hk, ENNReal.toReal_ofReal hd, ← measureReal_def,
    ← measureReal_def] at this

/-- The real inequality behind the dilation property for `s > 0`: on `|w| ≤ L`, the log-ratio
`|w| (e^s - 1) - s` of the original to the dilated Laplace density is at most `a`. -/
private lemma abs_mul_exp_sub_one_le {w s a L : ℝ} (hs : 0 ≤ s) (hL : 1 / 2 ≤ L)
    (hsL : s * L ≤ a) (ha : a ≤ 1 / 2) (hw : |w| ≤ L) : |w| * (exp s - 1) ≤ a + s := by
  have hs1 : s ≤ 1 := by nlinarith
  have hexp : exp s - 1 ≤ s + s ^ 2 := by
    have := abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_nonneg hs]; exact hs1)
    linarith [le_abs_self (exp s - 1 - s)]
  have h₀ : 0 ≤ exp s - 1 := by linarith [add_one_le_exp s]
  calc |w| * (exp s - 1) ≤ L * (s + s ^ 2) :=
        mul_le_mul hw hexp h₀ (by linarith)
    _ = s * L + (s * L) * s := by ring
    _ ≤ a + a * s := by gcongr
    _ ≤ a + s := by nlinarith

/-- The real inequality behind the dilation property for `s < 0` (with `t = -s`): from the
pointwise bound `p₀ ≤ e^t p` and `p₀ ≤ 1`, the additive term `e^{-L}` absorbs the excess of
`e^t` over `e^a`. -/
private lemma le_exp_mul_add_exp_neg {p₀ p a t L : ℝ} (hp : 0 ≤ p) (h₁ : p₀ ≤ exp t * p)
    (h₂ : p₀ ≤ 1) (ht : 0 ≤ t) (htL : t * L ≤ a) (hL : 1 / 2 ≤ L) (ha : a ≤ 1 / 2) :
    p₀ ≤ exp a * p + exp (-L) := by
  rcases le_or_gt t a with hta | hta
  · calc p₀ ≤ exp t * p := h₁
      _ ≤ exp a * p := by gcongr
      _ ≤ _ := le_add_of_nonneg_right (exp_pos _).le
  have he : exp a = exp (a - t) * exp t := by rw [← exp_add, sub_add_cancel]
  have hlt : exp (a - t) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have hkey : p₀ ≤ exp a * p + (1 - exp (a - t)) := by
    rcases le_total (exp t * p) 1 with hp1 | hp1
    · calc p₀ ≤ exp t * p := h₁
        _ = exp a * p + (1 - exp (a - t)) * (exp t * p) := by rw [he]; ring
        _ ≤ exp a * p + (1 - exp (a - t)) * 1 := by gcongr
        _ = _ := by ring
    · have := mul_le_mul_of_nonneg_left hp1 (exp_pos (a - t)).le
      calc p₀ ≤ 1 := h₂
        _ ≤ exp (a - t) * (exp t * p) + (1 - exp (a - t)) := by linarith
        _ = _ := by rw [he]; ring
  have h₃ : 1 - exp (a - t) ≤ t - a := by linarith [add_one_le_exp (a - t)]
  have h₄ : t - a ≤ exp (-L) := by
    rcases le_total 1 L with hL1 | hL1
    · nlinarith [exp_pos (-L), mul_le_mul_of_nonneg_left hL1 ht]
    · have ht1 : t ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hL ht]
      nlinarith [mul_le_mul_of_nonneg_right ht1 (sub_nonneg.2 hL1), add_one_le_exp (-L)]
  linarith

/-- The pointwise comparison of the Laplace density with its dilation by `e^s`: if
`|w| (e^s - 1) ≤ k + s`, then `h(w) ≤ e^k · e^s h(e^s w)`. -/
private lemma laplacePDFReal_le_dilate {w s k : ℝ} (h : |w| * (exp s - 1) ≤ k + s) :
    laplacePDFReal 0 1 w ≤ exp k * (exp s * laplacePDFReal 0 1 (w / exp (-s))) := by
  have e : |w / exp (-s)| = |w| * exp s := by
    rw [abs_div, abs_of_pos (exp_pos _), exp_neg, div_inv_eq_mul]
  have e₁ : laplacePDFReal 0 1 w = 2⁻¹ * exp (-|w|) := by simp [laplacePDFReal]
  have e₂ : exp k * (exp s * laplacePDFReal 0 1 (w / exp (-s))) =
      2⁻¹ * exp (k + s + -(|w| * exp s)) := by
    simp only [laplacePDFReal, sub_zero, div_one, e, exp_add]
    ring
  rw [e₁, e₂]
  gcongr
  linarith

end SmoothSensitivity

open SmoothSensitivity

/-- **Sliding property of the Laplace distribution** (Dwork–McSherry–Nissim–Smith, used in
Nissim–Raskhodnikova–Smith, Lemma 2.9): for `Z ∼ Lap(1)`, every shift `Δ` and every measurable
`E`, `P[Z ∈ E] ≤ e^{|Δ|} P[Z ∈ E + Δ]`, with no additive term. -/
theorem laplace_sliding (Δ : ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    (laplaceMeasure 0 1).real E ≤ exp |Δ| * (laplaceMeasure 0 1).real ((· - Δ) ⁻¹' E) := by
  have := isProbabilityMeasure_laplaceMeasure 0 one_pos
  have h : laplaceMeasure 0 1 E ≤
      ENNReal.ofReal (exp |Δ|) * laplaceMeasure 0 1 ((· - Δ) ⁻¹' E) + ENNReal.ofReal 0 := by
    rw [ENNReal.ofReal_zero, add_zero, laplace_apply hE, laplace_preimage_sub hE,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hE fun w _ ↦ ?_
    rw [laplacePDF, laplacePDF, ← ENNReal.ofReal_mul (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : laplacePDFReal 0 1 (w + Δ) = laplacePDFReal (-Δ) 1 w := by
      simp [laplacePDFReal]
    rw [e]
    exact laplacePDFReal_le_exp_mul one_pos (by simp) w
  simpa using measureReal_le_of_le (exp_pos _).le le_rfl h

/-- **Dilation property of the Laplace distribution** (Nissim–Raskhodnikova–Smith, proof of
Lemma 2.9, case `d = 1`): for `Z ∼ Lap(1)`, `ε ≤ 1`, `δ ∈ (0, 1)`, every
`|s| ≤ ε / (2 ln (2/δ))` and every measurable `E`,
`P[Z ∈ E] ≤ e^{ε/2} P[Z ∈ e^s · E] + δ/2`. -/
theorem laplace_dilation {ε δ s : ℝ} (hε : ε ≤ 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hs : |s| ≤ ε / (2 * log (2 / δ))) {E : Set ℝ} (hE : MeasurableSet E) :
    (laplaceMeasure 0 1).real E ≤
      exp (ε / 2) * (laplaceMeasure 0 1).real ((exp (-s) * ·) ⁻¹' E) + δ / 2 := by
  have := isProbabilityMeasure_laplaceMeasure 0 one_pos
  set L := log (2 / δ) with hL_def
  have hL : 1 / 2 ≤ L := by
    have h2 : log 2 < L := log_lt_log two_pos (by rw [lt_div_iff₀ hδ₀]; linarith)
    linarith [log_two_gt_d9]
  have hL₀ : 0 < L := by linarith
  have hsL : |s| * L ≤ ε / 2 := by
    rw [le_div_iff₀ (by positivity)] at hs
    linarith
  have hexpL : exp (-L) = δ / 2 := by rw [hL_def, exp_neg, exp_log (by positivity), inv_div]
  have hpre : laplaceMeasure 0 1 ((exp (-s) * ·) ⁻¹' E) =
      ∫⁻ w in E, ENNReal.ofReal (exp s) * laplacePDF 0 1 (w / exp (-s)) := by
    rw [laplace_preimage_mul hE (exp_pos _), exp_neg, inv_inv,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hpt {k : ℝ} (w : ℝ) (h : |w| * (exp s - 1) ≤ k + s) : laplacePDF 0 1 w ≤
      ENNReal.ofReal (exp k) * (ENNReal.ofReal (exp s) * laplacePDF 0 1 (w / exp (-s))) := by
    rw [laplacePDF, laplacePDF, ← ENNReal.ofReal_mul (exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (laplacePDFReal_le_dilate h)
  rcases le_total s 0 with hs0 | hs0
  · -- the noise is spread out: a bound with factor `e^{-s}`, whose excess `δ/2` absorbs
    have h : laplaceMeasure 0 1 E ≤ ENNReal.ofReal (exp (-s)) *
        laplaceMeasure 0 1 ((exp (-s) * ·) ⁻¹' E) + ENNReal.ofReal 0 := by
      rw [ENNReal.ofReal_zero, add_zero, laplace_apply hE, hpre,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hE fun w _ ↦ hpt w ?_
      have : exp s ≤ 1 := exp_le_one_iff.2 hs0
      nlinarith [abs_nonneg w]
    have h' := measureReal_le_of_le (exp_pos _).le le_rfl h
    rw [add_zero] at h'
    rw [← hexpL]
    exact le_exp_mul_add_exp_neg measureReal_nonneg h' measureReal_le_one (by linarith)
      (by rwa [abs_of_nonpos hs0] at hsL) hL (by linarith)
  · -- the noise is concentrated: the density ratio is at most `e^{ε/2}` on `|w| < L`
    set G := {w : ℝ | L * 1 ≤ |w - 0|} with hG_def
    have hG : MeasurableSet G := measurableSet_le measurable_const (by fun_prop)
    have hνG : laplaceMeasure 0 1 G = ENNReal.ofReal (δ / 2) := by
      rw [← ofReal_measureReal, hG_def, laplaceMeasure_real_le_abs_sub 0 one_pos hL₀.le, hexpL]
    have hm : Measurable fun w : ℝ ↦ ENNReal.ofReal (exp (ε / 2)) *
        (ENNReal.ofReal (exp s) * laplacePDF 0 1 (w / exp (-s))) := by fun_prop
    have h : laplaceMeasure 0 1 E ≤ ENNReal.ofReal (exp (ε / 2)) *
        laplaceMeasure 0 1 ((exp (-s) * ·) ⁻¹' E) + ENNReal.ofReal (δ / 2) := by
      rw [laplace_apply hE, hpre, ← hνG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ∫⁻ w in E, laplacePDF 0 1 w
          ≤ ∫⁻ w in E, (ENNReal.ofReal (exp (ε / 2)) * (ENNReal.ofReal (exp s) *
              laplacePDF 0 1 (w / exp (-s))) + G.indicator (laplacePDF 0 1) w) := by
            refine setLIntegral_mono' hE fun w _ ↦ ?_
            by_cases hw : w ∈ G
            · rw [indicator_of_mem hw]
              exact le_add_self
            · refine le_add_right (hpt w ?_)
              have hwL : |w| ≤ L := by
                rw [hG_def] at hw
                simp only [mem_ofPred_eq, mul_one, sub_zero, not_le] at hw
                exact hw.le
              exact abs_mul_exp_sub_one_le hs0 hL (by rwa [abs_of_nonneg hs0] at hsL)
                (by linarith) hwL
        _ = (∫⁻ w in E, ENNReal.ofReal (exp (ε / 2)) * (ENNReal.ofReal (exp s) *
              laplacePDF 0 1 (w / exp (-s)))) + ∫⁻ w in E, G.indicator (laplacePDF 0 1) w :=
            lintegral_add_left hm _
        _ ≤ _ := by
            refine add_le_add (le_refl _) ?_
            rw [laplace_apply hG, ← lintegral_indicator hG]
            exact setLIntegral_le_lintegral _ _
    exact measureReal_le_of_le (exp_pos _).le (by positivity) h

/-- **Nissim–Raskhodnikova–Smith, Lemma 2.9**, case `d = 1`: for `ε ≤ 1` and `δ ∈ (0, 1)`, the
standard Laplace distribution `Lap(1)` is `(α, β)`-admissible for `(ε, δ)` with `α = ε/2` and
`β = ε / (2 ln (2/δ))`. (The paper assumes `ε, δ ∈ (0, 1)`.) -/
theorem isAdmissibleNoise_laplace {ε δ : ℝ} (hε : ε ≤ 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    IsAdmissibleNoise (laplaceMeasure 0 1) (ε / 2) (ε / (2 * log (2 / δ))) ε δ where
  sliding Δ hΔ E hE :=
    calc _ ≤ exp |Δ| * _ := laplace_sliding Δ hE
      _ ≤ exp (ε / 2) * (laplaceMeasure 0 1).real ((· - Δ) ⁻¹' E) := by gcongr
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  dilation _ hs _ hE := laplace_dilation hε hδ₀ hδ₁ hs hE

section Mechanism

variable {ι D : Type*} [Fintype ι] [DecidableEq D] [Finite D] [MeasurableSpace D]
  [MeasurableSingletonClass D] {f : (ι → D) → ℝ} {S : (ι → D) → ℝ} {ε δ β : ℝ}

/-- **Nissim–Raskhodnikova–Smith, Corollary 2.4, item 2**, in the stronger form given by the
proof: for `ε ∈ (0, 1]`, `δ ∈ (0, 1)` and a `β`-smooth upper bound `S` on the local
sensitivity of `f` with `β ≤ ε / (2 ln (2/δ))`, the algorithm `x ↦ f(x) + 2 S(x)/ε · η` with
`η ∼ Lap(1)` (the mechanism with `α = ε/2`, so that `S(x)/α = 2 S(x)/ε`) is
`(ε, δ/2)`-differentially private. Since the Laplace distribution slides with no additive term,
only the dilation step costs `δ/2`. -/
theorem isEpsDeltaDP_smoothNoiseMechanism_laplace_half (hε₀ : 0 < ε) (hε : ε ≤ 1)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hβ : β ≤ ε / (2 * log (2 / δ)))
    (hS : IsSmoothUpperBound f β S) :
    IsEpsDeltaDP (smoothNoiseMechanism (laplaceMeasure 0 1) f S (ε / 2))
      (fun x y ↦ hammingDist x y = 1) ε (δ / 2) := by
  have := isProbabilityMeasure_laplaceMeasure 0 one_pos
  have h := SmoothSensitivity.isEpsDeltaDP_of_dilation_of_sliding (hS.mono hβ) (half_pos hε₀)
    (half_pos hε₀).le (half_pos hε₀).le le_rfl (half_pos hδ₀).le
    (fun Δ hΔ E hE ↦ by
      rw [add_zero]
      exact (laplace_sliding Δ hE).trans (by gcongr))
    (fun s hs E hE ↦ laplace_dilation hε hδ₀ hδ₁ hs hE)
  rwa [add_halves, mul_zero, zero_add] at h

/-- **Nissim–Raskhodnikova–Smith, Corollary 2.4, item 2**: for `ε ∈ (0, 1]`, `δ ∈ (0, 1)` and a
`β`-smooth upper bound `S` on the local sensitivity of `f` with `β ≤ ε / (2 ln (2/δ))`, the
algorithm `x ↦ f(x) + 2 S(x)/ε · η` with `η ∼ Lap(1)` is `(ε, δ)`-differentially private. The
paper assumes only `δ ∈ (0, 1)`; the bound `ε ≤ 1` comes from Lemma 2.9, and some bound on `ε`
is needed (see the notes for a numerical counterexample at `ε = 8`). -/
theorem isEpsDeltaDP_smoothNoiseMechanism_laplace (hε₀ : 0 < ε) (hε : ε ≤ 1)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hβ : β ≤ ε / (2 * log (2 / δ)))
    (hS : IsSmoothUpperBound f β S) :
    IsEpsDeltaDP (smoothNoiseMechanism (laplaceMeasure 0 1) f S (ε / 2))
      (fun x y ↦ hammingDist x y = 1) ε δ :=
  (isEpsDeltaDP_smoothNoiseMechanism_laplace_half hε₀ hε hδ₀ hδ₁ hβ hS).mono le_rfl
    (by linarith)

/-- The smooth sensitivity instance of Corollary 2.4, item 2 (Nissim–Raskhodnikova–Smith,
Lemma 2.3 and Corollary 2.4): for `ε ∈ (0, 1]` and `δ ∈ (0, 1)`, releasing
`f(x) + 2 S*_{f,β}(x)/ε · η` with `β = ε / (2 ln (2/δ))` and `η ∼ Lap(1)` is
`(ε, δ)`-differentially private. -/
theorem isEpsDeltaDP_smoothNoiseMechanism_laplace_smoothSensitivity (hε₀ : 0 < ε)
    (hε : ε ≤ 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    IsEpsDeltaDP (smoothNoiseMechanism (laplaceMeasure 0 1) f
      (smoothSensitivity f (ε / (2 * log (2 / δ)))) (ε / 2))
      (fun x y ↦ hammingDist x y = 1) ε δ := by
  have hL : 0 < log (2 / δ) := log_pos (by rw [lt_div_iff₀ hδ₀]; linarith)
  exact isEpsDeltaDP_smoothNoiseMechanism_laplace hε₀ hε hδ₀ hδ₁ le_rfl
    (isSmoothUpperBound_smoothSensitivity (by positivity))

end Mechanism

end InformationTheory
