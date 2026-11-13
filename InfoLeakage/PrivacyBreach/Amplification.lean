/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.LocalPrivacy.Basic

/-!
# Privacy breaches and amplification

This file formalizes the privacy-breach framework of A. Evfimievski, J. Gehrke and R. Srikant,
*Limiting privacy breaches in privacy preserving data mining*, PODS 2003 (San Diego, June 2003);
there is no arXiv version. Numbers refer to the PODS paper.

A client holds a private value `X ∈ V_X` drawn from a prior `p_X` and releases `Y = R(X) ∈ V_Y`,
where the randomization operator `R` has transition probabilities `p[x → y]`. For a property
`Q : V_X → {true, false}`, a `ρ₁`-to-`ρ₂` (upward) privacy breach occurs when releasing `y` lifts
the probability of `Q(X)` from at most `ρ₁` to at least `ρ₂`; a downward `ρ₂`-to-`ρ₁` breach is
the reverse. The operator is at most `γ`-amplifying for `y` if `p[x₁ → y] ≤ γ p[x₂ → y]` for all
`x₁, x₂`. Statement 1 says that amplification rules out breaches for every prior: if
`ρ₂ (1 - ρ₁) / (ρ₁ (1 - ρ₂)) > γ`, revealing `y` causes neither kind of breach. Being at most
`γ`-amplifying for every `y` is `ε`-local differential privacy with `ε = log γ`
(`isAmplifying_iff_isLocalDP`), so Statement 1 bounds the breaches of a locally private channel
(`not_isUpwardBreach_of_isLocalDP`).

Alphabets are finite; priors are vectors `pX : α → ℝ` and operators are matrices `R : α → β → ℝ`,
as in `IsLocalDP` and `outputLaw`. The law of `Y` is `outputLaw pX R`.

## Main definitions

* `PrivacyBreach.priorProb pX Q`: the prior probability `P[Q(X)]`.
* `PrivacyBreach.posteriorProb pX R Q y`: the posterior probability `P[Q(X) | Y = y]`.
* `IsUpwardBreach pX R Q ρ₁ ρ₂ y`: a (straight or upward) `ρ₁`-to-`ρ₂` privacy breach with respect
  to `Q`, caused by `y` (Definitions 1 and 2).
* `IsDownwardBreach pX R Q ρ₁ ρ₂ y`: an inverse or downward `ρ₂`-to-`ρ₁` privacy breach
  (Definition 2).
* `IsAmplifyingAt R γ y`, `IsAmplifying R γ`: `R` is at most `γ`-amplifying for `y`, and for every
  `y` (Definition 3).

## Main statements

* `PrivacyBreach.sum_mul_sum_le_of_isAmplifyingAt`: the key inequality of the proof of
  Statement 1, posterior odds are at most `γ` times prior odds:
  `P[¬Q(X)] P[Q(X), Y = y] ≤ γ P[Q(X)] P[¬Q(X), Y = y]`.
* `not_isUpwardBreach_of_isAmplifyingAt`, `not_isDownwardBreach_of_isAmplifyingAt`:
  **Statement 1**.
* `isAmplifying_iff_isLocalDP`: `R` is at most `γ`-amplifying (for all `y`) iff it is
  `log γ`-locally differentially private.
* `not_isUpwardBreach_of_isLocalDP`, `not_isDownwardBreach_of_isLocalDP`: Statement 1 for an
  `ε`-locally differentially private operator, with `γ = e^ε`.

## Correspondence with the paper

* Section 3, the law of `Y` and the posteriors: `outputLaw`, `PrivacyBreach.priorProb`,
  `PrivacyBreach.posteriorProb`.
* Definition 1: `IsUpwardBreach` (Definition 1 is the upward case of Definition 2).
* Definition 2: `IsUpwardBreach`, `IsDownwardBreach`; the reduction of downward breaches to upward
  breaches of `¬Q`: `isDownwardBreach_iff_isUpwardBreach_not`.
* Definition 3, eq. (2): `IsAmplifyingAt`, `IsAmplifying`.
* Statement 1, eq. (3): `not_isUpwardBreach_of_isAmplifyingAt`,
  `not_isDownwardBreach_of_isAmplifyingAt`; their common core is
  `PrivacyBreach.sum_mul_sum_le_of_isAmplifyingAt`.

## Implementation notes

* Definition 3 is stated in the paper as a bound on ratios `p[x₁ → y] / p[x₂ → y] ≤ γ`, together
  with `γ ≥ 1` and `∃ x, p[x → y] > 0`. We use the multiplied-out form
  `p[x₁ → y] ≤ γ p[x₂ → y]`, which avoids division. When some
  `p[x → y] > 0` the two forms agree (all `p[x → y]` are then positive, as the proof of
  Statement 1 notes), and `γ ≥ 1` follows. Statement 1 is proved without the hypothesis
  `∃ x, p[x → y] > 0`: it follows from `P[Y = y] > 0`, which is part of Definitions 1 and 2.
* Definitions 1 and 2 are stated in the paper for a property `Q` and a value `y` with
  `P[Y = y] > 0`; this positivity is part of `IsUpwardBreach` and `IsDownwardBreach`, so the
  posterior is never the junk value `x / 0 = 0`.
* Properties are predicates `Q : α → Prop` with `[DecidablePred Q]`.

## Not formalized

Section 4.1's example operator `R₃` and the background-knowledge remark; Sections 4.2–5 (itemset
randomization, select-a-size, pseudorandom generators, Statements 2–5); Section 6 (worst-case
information, Statement 6).
-/

@[expose] public section

open Finset Real

namespace InformationTheory

variable {α β : Type*}

/-! ### Definitions -/

section Definitions

variable [Fintype α]

namespace PrivacyBreach

/-- The prior probability `P[Q(X)] = ∑_{x : Q x} p_X(x)` of a property `Q` (Section 3 of
Evfimievski–Gehrke–Srikant). -/
def priorProb (pX : α → ℝ) (Q : α → Prop) [DecidablePred Q] : ℝ :=
  ∑ x with Q x, pX x

/-- The posterior probability `P[Q(X) | Y = y] = ∑_{x : Q x} p_X(x) p[x → y] / P[Y = y]` of a
property `Q` once `Y = R(X) = y` is revealed (Section 3 of Evfimievski–Gehrke–Srikant). It is
meaningful when `P[Y = y] = outputLaw pX R y > 0`. -/
noncomputable def posteriorProb (pX : α → ℝ) (R : α → β → ℝ) (Q : α → Prop) [DecidablePred Q]
    (y : β) : ℝ :=
  (∑ x with Q x, pX x * R x y) / outputLaw pX R y

end PrivacyBreach

open PrivacyBreach

/-- A **(straight or upward) `ρ₁`-to-`ρ₂` privacy breach** with respect to the property `Q`,
caused by the value `y` (Definitions 1 and 2 of Evfimievski–Gehrke–Srikant):
`P[Y = y] > 0`, `P[Q(X)] ≤ ρ₁` and `P[Q(X) | Y = y] ≥ ρ₂`. -/
def IsUpwardBreach (pX : α → ℝ) (R : α → β → ℝ) (Q : α → Prop) [DecidablePred Q]
    (ρ₁ ρ₂ : ℝ) (y : β) : Prop :=
  0 < outputLaw pX R y ∧ priorProb pX Q ≤ ρ₁ ∧ ρ₂ ≤ posteriorProb pX R Q y

/-- An **(inverse or downward) `ρ₂`-to-`ρ₁` privacy breach** with respect to the property `Q`,
caused by the value `y` (Definition 2 of Evfimievski–Gehrke–Srikant): `P[Y = y] > 0`,
`P[Q(X)] ≥ ρ₂` and `P[Q(X) | Y = y] ≤ ρ₁`. -/
def IsDownwardBreach (pX : α → ℝ) (R : α → β → ℝ) (Q : α → Prop) [DecidablePred Q]
    (ρ₁ ρ₂ : ℝ) (y : β) : Prop :=
  0 < outputLaw pX R y ∧ ρ₂ ≤ priorProb pX Q ∧ posteriorProb pX R Q y ≤ ρ₁

end Definitions

/-- The randomization operator `R` is **at most `γ`-amplifying for `y`** (Definition 3, eq. (2),
of Evfimievski–Gehrke–Srikant, multiplied out to avoid division):
`p[x₁ → y] ≤ γ p[x₂ → y]` for all `x₁, x₂`. -/
def IsAmplifyingAt (R : α → β → ℝ) (γ : ℝ) (y : β) : Prop :=
  ∀ x₁ x₂, R x₁ y ≤ γ * R x₂ y

/-- The randomization operator `R` is **at most `γ`-amplifying** if it is at most `γ`-amplifying
for every `y` (Definition 3 of Evfimievski–Gehrke–Srikant). -/
def IsAmplifying (R : α → β → ℝ) (γ : ℝ) : Prop :=
  ∀ y, IsAmplifyingAt R γ y

/-! ### Amplification and local differential privacy -/

/-- Being at most `γ`-amplifying is `log γ`-local differential privacy. -/
theorem isAmplifying_iff_isLocalDP {R : α → β → ℝ} {γ : ℝ} (hγ : 0 < γ) :
    IsAmplifying R γ ↔ IsLocalDP R (log γ) := by
  simp only [IsAmplifying, IsAmplifyingAt, IsLocalDP, exp_log hγ]
  exact ⟨fun h x₁ x₂ y ↦ h y x₁ x₂, fun h y x₁ x₂ ↦ h x₁ x₂ y⟩

/-- An `ε`-locally differentially private operator is at most `e^ε`-amplifying. -/
theorem IsLocalDP.isAmplifying {R : α → β → ℝ} {ε : ℝ} (h : IsLocalDP R ε) :
    IsAmplifying R (exp ε) :=
  fun y x₁ x₂ ↦ h x₁ x₂ y

/-! ### Statement 1 -/

section Statement1

variable [Fintype α] {pX : α → ℝ} {R : α → β → ℝ} {γ ρ₁ ρ₂ : ℝ} {y : β}

namespace PrivacyBreach

omit [Fintype α] in
/-- The key step of the proof of **Statement 1** of Evfimievski–Gehrke–Srikant: if `R` is at most
`γ`-amplifying for `y`, then for all sets `S, T` of private values,
`P[X ∈ T] P[X ∈ S, Y = y] ≤ γ P[X ∈ S] P[X ∈ T, Y = y]`. With `S = {Q}` and `T = {¬Q}` this says
that the posterior odds of `Q(X)` given `Y = y` are at most `γ` times its prior odds. -/
theorem sum_mul_sum_le_of_isAmplifyingAt (hp : ∀ x, 0 ≤ pX x) (hR : IsAmplifyingAt R γ y)
    (S T : Finset α) :
    (∑ x ∈ T, pX x) * ∑ x ∈ S, pX x * R x y ≤
      γ * ((∑ x ∈ S, pX x) * ∑ x ∈ T, pX x * R x y) := by
  rw [sum_mul_sum, sum_mul_sum, sum_comm, mul_sum]
  refine sum_le_sum fun x _ ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun x' _ ↦ ?_
  have := mul_le_mul_of_nonneg_left (hR x x') (mul_nonneg (hp x) (hp x'))
  linarith

/-- The probability of `¬Q(X)` is `1 - P[Q(X)]`. -/
lemma priorProb_not (hp₁ : ∑ x, pX x = 1) (Q : α → Prop) [DecidablePred Q] :
    priorProb pX (fun x ↦ ¬Q x) = 1 - priorProb pX Q := by
  rw [priorProb, priorProb, ← hp₁, ← sum_filter_add_sum_filter_not univ Q]
  ring

/-- Given `Y = y` with `P[Y = y] > 0`, the posterior probability of `¬Q(X)` is
`1 - P[Q(X) | Y = y]`. -/
lemma posteriorProb_not (h : 0 < outputLaw pX R y) (Q : α → Prop) [DecidablePred Q] :
    posteriorProb pX R (fun x ↦ ¬Q x) y = 1 - posteriorProb pX R Q y := by
  have h' := h
  rw [outputLaw, ← sum_filter_add_sum_filter_not univ Q] at h'
  rw [posteriorProb, posteriorProb, outputLaw, ← sum_filter_add_sum_filter_not univ Q]
  field_simp
  ring

/-- An operator that is at most `γ`-amplifying for some `y` with `P[Y = y] > 0` has `0 ≤ γ`. -/
lemma nonneg_of_isAmplifyingAt (hp : ∀ x, 0 ≤ pX x) (hR : IsAmplifyingAt R γ y)
    (h : 0 < outputLaw pX R y) : 0 ≤ γ := by
  by_contra! hγ
  have hle : ∀ x, R x y ≤ 0 := fun x ↦ by nlinarith [hR x x]
  have : outputLaw pX R y ≤ 0 :=
    sum_nonpos fun x _ ↦ mul_nonpos_of_nonneg_of_nonpos (hp x) (hle x)
  linarith

end PrivacyBreach

open PrivacyBreach

/-- A downward `ρ₂`-to-`ρ₁` breach with respect to `Q` is an upward `(1 - ρ₂)`-to-`(1 - ρ₁)`
breach with respect to `¬Q` (Section 3 and proof of Statement 1 of Evfimievski–Gehrke–Srikant).
-/
theorem isDownwardBreach_iff_isUpwardBreach_not (hp₁ : ∑ x, pX x = 1) (Q : α → Prop)
    [DecidablePred Q] :
    IsDownwardBreach pX R Q ρ₁ ρ₂ y ↔ IsUpwardBreach pX R (fun x ↦ ¬Q x) (1 - ρ₂) (1 - ρ₁) y := by
  refine ⟨fun ⟨h, h₁, h₂⟩ ↦ ⟨h, ?_, ?_⟩, fun ⟨h, h₁, h₂⟩ ↦ ⟨h, ?_, ?_⟩⟩
  · rw [priorProb_not hp₁]; linarith
  · rw [posteriorProb_not h]; linarith
  · rw [priorProb_not hp₁] at h₁; linarith
  · rw [posteriorProb_not h] at h₂; linarith

/-- **Statement 1** of Evfimievski–Gehrke–Srikant, upward breaches: let `0 < ρ₁ < ρ₂ < 1`, and
let `R` be at most `γ`-amplifying for `y`, with `ρ₂ / ρ₁ · (1 - ρ₁) / (1 - ρ₂) > γ` (condition
(3)). Then for every prior `p_X` and every property `Q`, revealing `R(X) = y` causes no upward
`ρ₁`-to-`ρ₂` privacy breach. The paper's further hypothesis `∃ x, p[x → y] > 0` is not needed: it
follows from `P[Y = y] > 0`, which is part of the definition of a breach. -/
theorem not_isUpwardBreach_of_isAmplifyingAt (hp : ∀ x, 0 ≤ pX x) (hp₁ : ∑ x, pX x = 1)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hR : IsAmplifyingAt R γ y)
    (hγ : γ < ρ₂ / ρ₁ * ((1 - ρ₁) / (1 - ρ₂))) (Q : α → Prop) [DecidablePred Q] :
    ¬IsUpwardBreach pX R Q ρ₁ ρ₂ y := by
  rintro ⟨hy, hq, hpost⟩
  have hγ₀ := nonneg_of_isAmplifyingAt hp hR hy
  have hodds := sum_mul_sum_le_of_isAmplifyingAt hp hR {x | Q x} {x | ¬Q x}
  have hsplit := sum_filter_add_sum_filter_not univ Q (fun x ↦ pX x * R x y)
  have hsplit₁ := sum_filter_add_sum_filter_not univ Q pX
  rw [← outputLaw] at hsplit
  rw [hp₁] at hsplit₁
  rw [posteriorProb, le_div_iff₀ hy] at hpost
  rw [priorProb] at hq
  rw [div_mul_div_comm, lt_div_iff₀ (mul_pos hρ₁ (by linarith))] at hγ
  set q := ∑ x with Q x, pX x
  set a := ∑ x with Q x, pX x * R x y
  set b := ∑ x with ¬Q x, pX x * R x y
  have hq₀ : 0 ≤ q := sum_nonneg fun x _ ↦ hp x
  have hnot : ∑ x with ¬Q x, pX x = 1 - q := by linarith
  rw [hnot] at hodds
  have ha : 0 < a := by nlinarith
  -- `ρ₂ (1 - q) a ≤ γ q ρ₂ b ≤ γ q (1 - ρ₂) a`
  have h1 : ρ₂ * (1 - q) * a ≤ γ * q * (1 - ρ₂) * a := by
    have hb : ρ₂ * b ≤ (1 - ρ₂) * a := by nlinarith
    nlinarith [mul_nonneg hγ₀ hq₀]
  have h2 : ρ₂ * (1 - q) ≤ γ * q * (1 - ρ₂) := le_of_mul_le_mul_right h1 ha
  nlinarith [mul_nonneg hγ₀ (sub_nonneg.2 hρ₂.le)]

/-- **Statement 1** of Evfimievski–Gehrke–Srikant, downward breaches: let `0 < ρ₁ < ρ₂ < 1`, and
let `R` be at most `γ`-amplifying for `y`, with `ρ₂ / ρ₁ · (1 - ρ₁) / (1 - ρ₂) > γ` (condition
(3)). Then for every prior `p_X` and every property `Q`, revealing `R(X) = y` causes no downward
`ρ₂`-to-`ρ₁` privacy breach. As in the paper, this is the upward case applied to `¬Q` with
`ρ₁' = 1 - ρ₂` and `ρ₂' = 1 - ρ₁`. -/
theorem not_isDownwardBreach_of_isAmplifyingAt (hp : ∀ x, 0 ≤ pX x) (hp₁ : ∑ x, pX x = 1)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hR : IsAmplifyingAt R γ y)
    (hγ : γ < ρ₂ / ρ₁ * ((1 - ρ₁) / (1 - ρ₂))) (Q : α → Prop) [DecidablePred Q] :
    ¬IsDownwardBreach pX R Q ρ₁ ρ₂ y := by
  rw [isDownwardBreach_iff_isUpwardBreach_not hp₁]
  refine not_isUpwardBreach_of_isAmplifyingAt hp hp₁ (by linarith) (by linarith) (by linarith)
    hR ?_ _
  convert hγ using 1
  rw [sub_sub_cancel, sub_sub_cancel]
  ring

/-- Statement 1 of Evfimievski–Gehrke–Srikant for an `ε`-locally differentially private operator
(`γ = e^ε`): if `0 < ρ₁ < ρ₂ < 1` and `e^ε < ρ₂ / ρ₁ · (1 - ρ₁) / (1 - ρ₂)`, no value `y` causes an
upward `ρ₁`-to-`ρ₂` privacy breach, for any prior and any property. -/
theorem not_isUpwardBreach_of_isLocalDP {ε : ℝ} (hp : ∀ x, 0 ≤ pX x) (hp₁ : ∑ x, pX x = 1)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hR : IsLocalDP R ε)
    (hε : exp ε < ρ₂ / ρ₁ * ((1 - ρ₁) / (1 - ρ₂))) (Q : α → Prop) [DecidablePred Q] (y : β) :
    ¬IsUpwardBreach pX R Q ρ₁ ρ₂ y :=
  not_isUpwardBreach_of_isAmplifyingAt hp hp₁ hρ₁ hρ₁₂ hρ₂ (hR.isAmplifying y) hε Q

/-- Statement 1 of Evfimievski–Gehrke–Srikant for an `ε`-locally differentially private operator
(`γ = e^ε`): if `0 < ρ₁ < ρ₂ < 1` and `e^ε < ρ₂ / ρ₁ · (1 - ρ₁) / (1 - ρ₂)`, no value `y` causes a
downward `ρ₂`-to-`ρ₁` privacy breach, for any prior and any property. -/
theorem not_isDownwardBreach_of_isLocalDP {ε : ℝ} (hp : ∀ x, 0 ≤ pX x) (hp₁ : ∑ x, pX x = 1)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hR : IsLocalDP R ε)
    (hε : exp ε < ρ₂ / ρ₁ * ((1 - ρ₁) / (1 - ρ₂))) (Q : α → Prop) [DecidablePred Q] (y : β) :
    ¬IsDownwardBreach pX R Q ρ₁ ρ₂ y :=
  not_isDownwardBreach_of_isAmplifyingAt hp hp₁ hρ₁ hρ₁₂ hρ₂ (hR.isAmplifying y) hε Q

end Statement1

end InformationTheory
