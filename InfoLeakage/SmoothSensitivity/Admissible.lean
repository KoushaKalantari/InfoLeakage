/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.SmoothSensitivity.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Admissible noise and the smooth sensitivity framework

This file formalizes Section 2.2.1 of K. Nissim, S. Raskhodnikova and A. Smith, *Smooth
sensitivity and sampling in private data analysis*, STOC 2007 (result numbers refer to the full
version, Draft Full Version v1.0, May 17, 2011): adding noise `S(x)/α · Z` to a real-valued
query `f`, where `S` is a `β`-smooth upper bound on the local sensitivity of `f` and `Z` has an
`(α, β)`-admissible distribution, is differentially private.

Databases are vectors `x : ι → D` with the Hamming distance, as in
`InfoLeakage.SmoothSensitivity.Basic`, and neighbours are databases at Hamming distance `1`.
**Restriction:** the domain `D` is **finite** (`[Finite D]`), whereas the paper allows any `D`
(its examples use `D = [0, Λ]`). Privacy is `IsEpsDeltaDP` from `InfoLeakage.FDP.Basic`. The
noise is a measure `ν` on `ℝ`, meant to be a probability measure (the case `d = 1` of the paper,
which takes `ν` with a density `h` on `ℝᵈ`; no density is needed here).

## Main definitions

* `IsAdmissibleNoise ν α β ε δ`: `ν` is `(α, β)`-admissible for the privacy parameters
  `(ε, δ)` (Definition 2.5, `d = 1`).
* `smoothNoiseMechanism ν f S α`: the algorithm `A(x) = f(x) + S(x)/α · Z` with `Z ∼ ν`.

## Main statements (paper result → Lean name)

* Lemma 2.6, in the form its proof gives (see the notes below):
  `IsAdmissibleNoise.isEpsDeltaDP_smoothNoiseMechanism`, giving
  `(ε, (1 + e^{ε/2}) δ / 2)`-DP.
* The general step behind Lemma 2.6, with separate parameters for the sliding and the dilation
  property: `SmoothSensitivity.isEpsDeltaDP_of_dilation_of_sliding`.

## Notes on the paper

* Proof of Lemma 2.6 (Section 2.2.1, p. 9, v1.0): the last line of the display,
  `Pr[z ∈ S₃] e^ε + (δ/2) e^{ε/2} + δ/2 = Pr[A(y) ∈ S] e^ε + δ`, is not an equality for
  `ε > 0`, since `(δ/2) e^{ε/2} + δ/2 > δ`. The argument proves
  `(ε, (1 + e^{ε/2}) δ / 2)`-differential privacy, which is what we formalize; we do not settle
  whether `(ε, δ)` holds for every admissible distribution. When the sliding property holds with
  no additive term (as for Laplace noise), the argument applied in the order dilation, then
  sliding gives `(ε, δ/2)`, which implies the paper's `(ε, δ)`
  (`SmoothSensitivity.isEpsDeltaDP_of_dilation_of_sliding`).
* The proof of Lemma 2.6 divides by `N(x) = S(x)/α`, which may be `0`; then `S` vanishes at `x`
  and its neighbours, `f(x) = f(y)` and the two output laws coincide (handled separately here).

## Not formalized

* Vector-valued queries (`d > 1`), Corollary 2.4 item 1 and Lemma 2.7 (Cauchy-type noise),
  Lemma 2.10 (Gaussian noise), and Sections 3–5 (computing smooth sensitivity, including the
  median of Proposition 3.4, and sample and aggregate).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace InformationTheory

variable {ι D : Type*} [Fintype ι] {f : (ι → D) → ℝ}

/-! ### Admissible noise distributions -/

/-- A measure `ν` on `ℝ` is **`(α, β)`-admissible** for the privacy parameters
`(ε, δ)` (Nissim–Raskhodnikova–Smith, Definition 2.5, case `d = 1`) if for all `|Δ| ≤ α`,
`|s| ≤ β` and every measurable set `E`, with `Z ∼ ν`:
* (sliding) `P[Z ∈ E] ≤ e^{ε/2} P[Z ∈ E + Δ] + δ/2`, and
* (dilation) `P[Z ∈ E] ≤ e^{ε/2} P[Z ∈ e^s · E] + δ/2`.
The translate `E + Δ` is written as the preimage `{z | z - Δ ∈ E}` and the dilate `e^s · E` as
`{z | e^{-s} z ∈ E}`.

The definition is meant for probability measures `ν` (as the paper's noise distributions and
`isAdmissibleNoise_laplace` are): `ν.real` sends sets of infinite measure to `0`, so for an
infinite `ν` the conditions are close to vacuous. -/
structure IsAdmissibleNoise (ν : Measure ℝ) (α β ε δ : ℝ) : Prop where
  sliding ⦃Δ : ℝ⦄ : |Δ| ≤ α → ∀ E, MeasurableSet E →
    ν.real E ≤ exp (ε / 2) * ν.real ((· - Δ) ⁻¹' E) + δ / 2
  dilation ⦃s : ℝ⦄ : |s| ≤ β → ∀ E, MeasurableSet E →
    ν.real E ≤ exp (ε / 2) * ν.real ((exp (-s) * ·) ⁻¹' E) + δ / 2

/-! ### The mechanism -/

variable [Finite D] [MeasurableSpace D] [MeasurableSingletonClass D]

/-- The **smooth sensitivity mechanism** `A(x) = f(x) + S(x)/α · Z` with `Z ∼ ν`
(Nissim–Raskhodnikova–Smith, Lemma 2.6, case `d = 1`): on database `x` it outputs a sample of
the law of `f(x) + S(x)/α · Z`. Here `S` is meant to be a smooth upper bound on the local
sensitivity of `f`. -/
noncomputable def smoothNoiseMechanism (ν : Measure ℝ) (f : (ι → D) → ℝ) (S : (ι → D) → ℝ)
    (α : ℝ) : Kernel (ι → D) ℝ :=
  Kernel.ofFunOfCountable fun x ↦ ν.map fun z ↦ f x + S x / α * z

variable {ν : Measure ℝ} {S : (ι → D) → ℝ} {α : ℝ}

lemma smoothNoiseMechanism_apply (x : ι → D) :
    smoothNoiseMechanism ν f S α x = ν.map fun z ↦ f x + S x / α * z := rfl

lemma smoothNoiseMechanism_real_apply (x : ι → D) {E : Set ℝ} (hE : MeasurableSet E) :
    (smoothNoiseMechanism ν f S α x).real E = ν.real {z | f x + S x / α * z ∈ E} := by
  rw [smoothNoiseMechanism_apply, map_measureReal_apply (by fun_prop) hE]
  rfl

instance [IsProbabilityMeasure ν] : IsMarkovKernel (smoothNoiseMechanism ν f S α) :=
  ⟨fun x ↦ by
    rw [smoothNoiseMechanism_apply]
    infer_instance⟩

/-! ### Privacy of the smooth sensitivity mechanism -/

namespace SmoothSensitivity

variable [DecidableEq D] {β ε₁ ε₂ δ₁ δ₂ : ℝ}

/-- `|log (a / b)| ≤ β` when `a ≤ e^β b` and `b ≤ e^β a`, for `a, b > 0`. -/
private lemma abs_log_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ exp β * b)
    (hba : b ≤ exp β * a) : |log (a / b)| ≤ β := by
  have h₁ : log a ≤ β + log b := by
    have := log_le_log ha hab
    rwa [log_mul (exp_pos β).ne' hb.ne', log_exp] at this
  have h₂ : log b ≤ β + log a := by
    have := log_le_log hb hba
    rwa [log_mul (exp_pos β).ne' ha.ne', log_exp] at this
  rw [log_div ha.ne' hb.ne', abs_le]
  constructor <;> linarith

/-- **The step behind Nissim–Raskhodnikova–Smith, Lemma 2.6**, with separate parameters for the
two properties of Definition 2.5: if `ν` satisfies the sliding property
`P[Z ∈ E] ≤ e^{ε₁} P[Z ∈ E + Δ] + δ₁` for `|Δ| ≤ α` and the dilation property
`P[Z ∈ E] ≤ e^{ε₂} P[Z ∈ e^s E] + δ₂` for `|s| ≤ β`, and `S` is a `β`-smooth upper bound on
`LS_f`, then `x ↦ f(x) + S(x)/α · Z` is `(ε₁ + ε₂, e^{ε₂} δ₁ + δ₂)`-differentially private.
As in the paper, `A(y)` is a dilation and a shift of `A(x)`; we dilate first, then shift. -/
theorem isEpsDeltaDP_of_dilation_of_sliding
    (hS : IsSmoothUpperBound f β S) (hα : 0 < α) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hslide : ∀ ⦃Δ : ℝ⦄, |Δ| ≤ α → ∀ E, MeasurableSet E →
      ν.real E ≤ exp ε₁ * ν.real ((· - Δ) ⁻¹' E) + δ₁)
    (hdil : ∀ ⦃s : ℝ⦄, |s| ≤ β → ∀ E, MeasurableSet E →
      ν.real E ≤ exp ε₂ * ν.real ((exp (-s) * ·) ⁻¹' E) + δ₂) :
    IsEpsDeltaDP (smoothNoiseMechanism ν f S α) (fun x y ↦ hammingDist x y = 1)
      (ε₁ + ε₂) (exp ε₂ * δ₁ + δ₂) := by
  rw [isEpsDeltaDP_iff_forall_measurableSet]
  intro x y hxy E hE
  have hyx : hammingDist y x = 1 := by rwa [hammingDist_comm]
  rw [smoothNoiseMechanism_real_apply x hE, smoothNoiseMechanism_real_apply y hE]
  have hmeas (a b : ℝ) : MeasurableSet {z : ℝ | a + b * z ∈ E} :=
    hE.preimage (by fun_prop : Measurable fun z : ℝ ↦ a + b * z)
  rcases (hS.nonneg x).eq_or_lt with hx | hx
  · -- if `S x = 0`, then `S y = 0` and `f x = f y`: both outputs are the point mass at `f x`
    have hy : S y = 0 :=
      le_antisymm (by simpa [← hx] using hS.le_exp_mul hyx) (hS.nonneg y)
    have hf : f x = f y := by
      have := hS.abs_sub_le hxy
      rw [← hx] at this
      exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
    rw [← hx, hy, hf]
    nlinarith [one_le_exp (add_nonneg hε₁ hε₂), mul_nonneg (exp_pos ε₂).le hδ₁,
      measureReal_nonneg (μ := ν) (s := {z | f y + 0 / α * z ∈ E})]
  have hy : 0 < S y := by
    by_contra! h
    nlinarith [hS.le_exp_mul hxy, exp_pos β, hS.nonneg y]
  have hα₀ := hα.ne'
  have hx₀ := hx.ne'
  have hy₀ := hy.ne'
  -- dilation by `e^s = S(x)/S(y)` turns the noise scale `S(x)/α` into `S(y)/α`
  have hsβ : |log (S x / S y)| ≤ β :=
    abs_log_div_le hx hy (hS.le_exp_mul hxy) (hS.le_exp_mul hyx)
  have hexp : exp (-log (S x / S y)) = S y / S x := by
    rw [exp_neg, exp_log (div_pos hx hy), inv_div]
  have h₁ := hdil hsβ _ (hmeas (f x) (S x / α))
  have e₁ : (exp (-log (S x / S y)) * ·) ⁻¹' {z | f x + S x / α * z ∈ E} =
      {z | f x + S y / α * z ∈ E} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq, hexp]
    rw [show S x / α * (S y / S x * z) = S y / α * z by field_simp]
  -- sliding by `Δ = (f(x) - f(y)) / (S(y)/α)` turns the centre `f(x)` into `f(y)`
  have hΔα : |(f x - f y) / (S y / α)| ≤ α := by
    rw [abs_div, abs_of_pos (div_pos hy hα), div_le_iff₀ (div_pos hy hα)]
    calc |f x - f y| = |f y - f x| := abs_sub_comm _ _
      _ ≤ S y := hS.abs_sub_le hyx
      _ = α * (S y / α) := by field_simp
  have h₂ := hslide hΔα _ (hmeas (f x) (S y / α))
  have e₂ : (· - (f x - f y) / (S y / α)) ⁻¹' {z | f x + S y / α * z ∈ E} =
      {z | f y + S y / α * z ∈ E} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq]
    rw [show f x + S y / α * (z - (f x - f y) / (S y / α)) = f y + S y / α * z by
      field_simp
      ring]
  rw [e₁] at h₁
  rw [e₂] at h₂
  calc _ ≤ _ := h₁
    _ ≤ exp ε₂ * (exp ε₁ * ν.real {z | f y + S y / α * z ∈ E} + δ₁) + δ₂ := by gcongr
    _ = _ := by
      rw [add_comm ε₁, exp_add]
      ring

end SmoothSensitivity

/-- **Nissim–Raskhodnikova–Smith, Lemma 2.6** (case `d = 1`, in the form its proof gives): if
the noise distribution `ν` is `(α, β)`-admissible for `(ε, δ)` and `S` is a `β`-smooth upper
bound on the local sensitivity of `f`, then `A(x) = f(x) + S(x)/α · Z`, `Z ∼ ν`, is
`(ε, (1 + e^{ε/2}) δ / 2)`-differentially private. The paper claims `(ε, δ)`, see the notes in
the module docstring. -/
theorem IsAdmissibleNoise.isEpsDeltaDP_smoothNoiseMechanism [DecidableEq D]
    {β ε δ : ℝ} (hν : IsAdmissibleNoise ν α β ε δ)
    (hS : IsSmoothUpperBound f β S) (hα : 0 < α) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    IsEpsDeltaDP (smoothNoiseMechanism ν f S α) (fun x y ↦ hammingDist x y = 1) ε
      ((1 + exp (ε / 2)) * δ / 2) := by
  have h := SmoothSensitivity.isEpsDeltaDP_of_dilation_of_sliding hS hα (by positivity)
    (by positivity) (by positivity) (by positivity) hν.sliding hν.dilation
  rw [add_halves] at h
  convert h using 1
  ring

end InformationTheory
