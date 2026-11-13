/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.Amplification.HockeyStick
public import Mathlib.Algebra.BigOperators.Field

/-!
# The canonical `(ε, δ)`-differentially private pair

This file formalizes the operational core of

* P. Kairouz, S. Oh and P. Viswanath, *The composition theorem for differential privacy*,
  ICML 2015 / IEEE Trans. Inf. Theory 63(6), 2017
  ([arXiv:1311.0776](https://arxiv.org/abs/1311.0776)); result, section, equation and page
  numbers follow arXiv v4 (6 Dec 2015).

The paper's key device is a single pair of distributions on four symbols,
`P̃₀ = (δ, (1 - δ) e^ε / (1 + e^ε), (1 - δ) / (1 + e^ε), 0)` and
`P̃₁ = (0, (1 - δ) / (1 + e^ε), (1 - δ) e^ε / (1 + e^ε), δ)` (equations (17) and (18)), which is
`(ε, δ)`-DP and tight at slope `e^ε`. By Blackwell's theorem (the paper's Theorem 2.5) every
`(ε, δ)`-differentially private pair of output distributions is a post-processing of this pair
(Section 6.1, "all `(ε, δ)`-differentially private mechanisms are dominated by this mechanism").
We prove this domination statement directly, for finite output alphabets, by constructing the
post-processing kernel: one trims mass `δ` from each of the two distributions so that the
remainders have likelihood ratios in `[e^{-ε}, e^ε]`, and splits the remainders along the two
randomized-response symbols.

`(ε, δ)`-DP is `IsEpsDeltaDP` of `InfoLeakage.FDP.Basic`, stated through the hockey-stick
divergence `hockeyStickDiv` of `InfoLeakage.Amplification.HockeyStick`:
`D_{e^ε}(μ ‖ ν) ≤ δ` iff `μ(S) ≤ e^ε ν(S) + δ` for all `S`. The composition theorem built on
this file is in `InfoLeakage.OptimalComposition.Composition` (non-adaptive composition and the
closed form of the optimal region) and `InfoLeakage.OptimalComposition.Adaptive` (adaptive
composition).

## Main definitions

* `OptimalComposition.canonicalProb ε δ b`: the probability mass functions `P̃₀` (`b = false`)
  and `P̃₁` (`b = true`) of equations (17)–(18).
* `OptimalComposition.canonicalMechanism ε δ`: the canonical mechanism `M̃` of Section 6.1, as a
  kernel `Bool → Fin 4`.

## Main statements (paper result → Lean name)

* Section 6.1, "`d_ε(P̃₀, P̃₁) = δ`": `hockeyStickDiv_canonicalMechanism`; the canonical mechanism
  is `(ε, δ)`-DP (`isEpsDeltaDP_canonicalMechanism`), tight at slope `e^ε`
  (`hockeyStickDiv_canonicalMechanism`); this is one inclusion of the paper's "the privacy
  region of a single access to this mechanism is `R(ε, δ)`", whose converse is not formalized.
* Theorem 2.5 (Blackwell) specialised to the canonical pair, combined with Theorems 2.1 and 2.4,
  i.e. the domination step of Section 6.1: a pair `(μ, ν)` on a finite alphabet is a
  post-processing `(T ∘ P̃₀, T ∘ P̃₁)` of the canonical pair iff `D_{e^ε}(μ ‖ ν) ≤ δ` and
  `D_{e^ε}(ν ‖ μ) ≤ δ`: `exists_kernel_comp_canonicalMechanism_iff`; for mechanisms:
  `isEpsDeltaDP_iff_forall_exists_kernel`.
* Theorem 2.1 (privacy as hypothesis testing) and Theorem 2.4 (data processing) are already in
  the library: `fEpsDelta_le_tradeoff_iff`, `isEpsDeltaDP_iff_isFDP` (`InfoLeakage.FDP.Basic`)
  and `tradeoff_le_tradeoff_comp`, `hockeyStickDiv_comp_le`.

## Not formalized

* Blackwell's theorem (Theorem 2.5) for general pairs of experiments, and Remark 6.1 (the
  privacy region as the intersection of the regions `R(ε̃, d_ε̃(P₀, P₁))`).
* Output spaces that are not finite.

## Notes on the paper

* Section 7 (p. 19) says "In our example, `X = {1, 2, 3, 4}`", while equations (17)–(18) index
  the four symbols by `{0, 1, 2, 3}`; this is only a relabelling and affects no result.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

namespace OptimalComposition

/-! ### Finite-sum constructions -/

section FiniteSum

variable {Y : Type*} [Fintype Y]

/-- A row of a stochastic matrix with prescribed weight `c`: `f / c` if `c ≠ 0` and the
probability vector `g` otherwise, so that `c • row f c g = f` whenever `∑ f = c`. -/
private noncomputable def row (f : Y → ℝ) (c : ℝ) (g : Y → ℝ) : Y → ℝ :=
  if c = 0 then g else fun y ↦ f y / c

omit [Fintype Y] in
private lemma row_nonneg {f g : Y → ℝ} {c : ℝ} (hf : ∀ y, 0 ≤ f y) (hc : 0 ≤ c)
    (hg : ∀ y, 0 ≤ g y) (y : Y) : 0 ≤ row f c g y := by
  unfold row
  split_ifs
  · exact hg y
  · exact div_nonneg (hf y) hc

private lemma sum_row {f g : Y → ℝ} {c : ℝ} (hfc : ∑ y, f y = c) (hg : ∑ y, g y = 1) :
    ∑ y, row f c g y = 1 := by
  unfold row
  split_ifs with h
  · exact hg
  · rw [← Finset.sum_div, hfc, div_self h]

private lemma mul_row {f g : Y → ℝ} {c : ℝ} (hf : ∀ y, 0 ≤ f y) (hfc : ∑ y, f y = c) (y : Y) :
    c * row f c g y = f y := by
  unfold row
  split_ifs with h
  · subst h
    rw [zero_mul, eq_comm]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ hf y).1 hfc y (Finset.mem_univ y)
  · exact mul_div_cancel₀ (f y) h

/-- Between two functions `a ≤ b` there is a function of any prescribed sum between `∑ a`
and `∑ b`. -/
private lemma exists_between_sum {a b : Y → ℝ} (hab : ∀ y, a y ≤ b y) {t : ℝ}
    (ht₁ : ∑ y, a y ≤ t) (ht₂ : t ≤ ∑ y, b y) :
    ∃ c : Y → ℝ, (∀ y, a y ≤ c y ∧ c y ≤ b y) ∧ ∑ y, c y = t := by
  set θ := (t - ∑ y, a y) / (∑ y, b y - ∑ y, a y)
  have hθ₀ : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ₁ : θ ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  refine ⟨fun y ↦ a y + θ * (b y - a y), fun y ↦ ⟨?_, ?_⟩, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg hθ₀ (sub_nonneg.2 (hab y)))
  · linarith [mul_le_of_le_one_left (sub_nonneg.2 (hab y)) hθ₁]
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rcases eq_or_ne (∑ y, b y - ∑ y, a y) 0 with h | h
    · rw [h, mul_zero]
      linarith
    · rw [div_mul_cancel₀ _ h]
      ring

private lemma min_eq_sub_max (a b : ℝ) : min a b = a - max 0 (a - b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

/-- The key step, assuming `∑ min(p, E q) ≤ ∑ min(q, E p)`: one can remove mass `δ` from each of
`p` and `q` so that the remainders `p'`, `q'` satisfy `p' ≤ E q'` and `q' ≤ E p'` pointwise. -/
private lemma exists_trim_aux {p q : Y → ℝ} {E δ : ℝ} (hE : 1 ≤ E) (hp : ∀ y, 0 ≤ p y)
    (hq : ∀ y, 0 ≤ q y) (hp₁ : ∑ y, p y = 1) (hδ₁ : δ ≤ 1)
    (hP : ∑ y, max 0 (p y - E * q y) ≤ δ)
    (hle : ∑ y, min (p y) (E * q y) ≤ ∑ y, min (q y) (E * p y)) :
    ∃ p' q' : Y → ℝ, (∀ y, 0 ≤ p' y ∧ p' y ≤ p y ∧ 0 ≤ q' y ∧ q' y ≤ q y ∧ p' y ≤ E * q' y ∧
      q' y ≤ E * p' y) ∧ ∑ y, p' y = 1 - δ ∧ ∑ y, q' y = 1 - δ := by
  have hE₀ : 0 < E := zero_lt_one.trans_le hE
  set p₀ : Y → ℝ := fun y ↦ min (p y) (E * q y) with hp₀_def
  set q₀ : Y → ℝ := fun y ↦ min (q y) (E * p y) with hq₀_def
  set m := ∑ y, p₀ y with hm_def
  have hp₀ (y : Y) : 0 ≤ p₀ y := le_min (hp y) (mul_nonneg hE₀.le (hq y))
  have hm₀ : 0 ≤ m := Finset.sum_nonneg fun y _ ↦ hp₀ y
  have hm : 1 - δ ≤ m := by
    have : m = 1 - ∑ y, max 0 (p y - E * q y) := by
      rw [hm_def, ← hp₁, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ min_eq_sub_max _ _
    linarith
  have hlow (y : Y) : p₀ y / E ≤ q₀ y := by
    refine le_min ?_ ?_
    · rw [div_le_iff₀ hE₀, mul_comm]
      exact min_le_right _ _
    · calc p₀ y / E ≤ p y / E := div_le_div_of_nonneg_right (min_le_left _ _) hE₀.le
        _ ≤ p y := div_le_self (hp y) hE
        _ ≤ E * p y := le_mul_of_one_le_left (hp y) hE
  obtain ⟨q₁, hq₁, hq₁m⟩ := exists_between_sum (t := m) hlow
    (by rw [← Finset.sum_div]; exact div_le_self hm₀ hE) hle
  set s := (1 - δ) / m with hs_def
  have hs₀ : 0 ≤ s := div_nonneg (by linarith) hm₀
  have hs₁ : s ≤ 1 := div_le_one_of_le₀ hm hm₀
  have hsm : s * m = 1 - δ := by
    rcases eq_or_ne m 0 with h | h
    · rw [h, mul_zero]
      linarith
    · exact div_mul_cancel₀ _ h
  refine ⟨fun y ↦ s * p₀ y, fun y ↦ s * q₁ y, fun y ↦ ?_, ?_, ?_⟩
  · have h₁ : p₀ y / E ≤ q₁ y := (hq₁ y).1
    have h₂ : q₁ y ≤ q₀ y := (hq₁ y).2
    have h₃ : 0 ≤ q₁ y := (div_nonneg (hp₀ y) hE₀.le).trans h₁
    have h₄ : p₀ y ≤ E * q₁ y := by rwa [div_le_iff₀ hE₀, mul_comm] at h₁
    have h₅ : q₀ y ≤ E * p₀ y := by
      rcases min_choice (p y) (E * q y) with h | h <;> simp only [hp₀_def, h]
      · exact min_le_right _ _
      · calc q₀ y ≤ q y := min_le_left _ _
          _ ≤ E * q y := le_mul_of_one_le_left (hq y) hE
          _ ≤ E * (E * q y) := le_mul_of_one_le_left (mul_nonneg hE₀.le (hq y)) hE
    refine ⟨mul_nonneg hs₀ (hp₀ y), ?_, mul_nonneg hs₀ h₃, ?_, ?_, ?_⟩
    · exact (mul_le_of_le_one_left (hp₀ y) hs₁).trans (min_le_left _ _)
    · exact (mul_le_of_le_one_left h₃ hs₁).trans (h₂.trans (min_le_left _ _))
    · nlinarith
    · nlinarith
  · rw [← Finset.mul_sum, ← hm_def, hsm]
  · rw [← Finset.mul_sum, hq₁m, hsm]

/-- Trimming lemma: if `∑ [p - E q]₊ ≤ δ` and `∑ [q - E p]₊ ≤ δ`, one can remove mass `δ` from
each of `p` and `q` so that the remainders `p'`, `q'` satisfy `p' ≤ E q'` and `q' ≤ E p'`. -/
private lemma exists_trim {p q : Y → ℝ} {E δ : ℝ} (hE : 1 ≤ E) (hp : ∀ y, 0 ≤ p y)
    (hq : ∀ y, 0 ≤ q y) (hp₁ : ∑ y, p y = 1) (hq₁ : ∑ y, q y = 1) (hδ₁ : δ ≤ 1)
    (hP : ∑ y, max 0 (p y - E * q y) ≤ δ) (hQ : ∑ y, max 0 (q y - E * p y) ≤ δ) :
    ∃ p' q' : Y → ℝ, (∀ y, 0 ≤ p' y ∧ p' y ≤ p y ∧ 0 ≤ q' y ∧ q' y ≤ q y ∧ p' y ≤ E * q' y ∧
      q' y ≤ E * p' y) ∧ ∑ y, p' y = 1 - δ ∧ ∑ y, q' y = 1 - δ := by
  rcases le_total (∑ y, min (p y) (E * q y)) (∑ y, min (q y) (E * p y)) with h | h
  · exact exists_trim_aux hE hp hq hp₁ hδ₁ hP h
  · obtain ⟨q', p', h, h₁, h₂⟩ := exists_trim_aux hE hq hp hq₁ hδ₁ hQ h
    exact ⟨p', q', fun y ↦ ⟨(h y).2.2.1, (h y).2.2.2.1, (h y).1, (h y).2.1, (h y).2.2.2.2.2,
      (h y).2.2.2.2.1⟩, h₂, h₁⟩

/-- The simulation step on finite sums: if `p, q` are probability vectors with
`∑ [p - E q]₊ ≤ δ` and `∑ [q - E p]₊ ≤ δ`, there is a stochastic matrix `t` from `Fin 4` to `Y`
carrying the canonical pair (with `E = e^ε`) to `(p, q)`. -/
private lemma exists_stochastic {p q : Y → ℝ} {E δ : ℝ} (hE : 1 ≤ E) (hδ₀ : 0 ≤ δ)
    (hδ₁ : δ ≤ 1) (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 ≤ q y) (hp₁ : ∑ y, p y = 1)
    (hq₁ : ∑ y, q y = 1) (hP : ∑ y, max 0 (p y - E * q y) ≤ δ)
    (hQ : ∑ y, max 0 (q y - E * p y) ≤ δ) :
    ∃ t : Fin 4 → Y → ℝ, (∀ x y, 0 ≤ t x y) ∧ (∀ x, ∑ y, t x y = 1) ∧
      (∀ y, δ * t 0 y + (1 - δ) * E / (1 + E) * t 1 y + (1 - δ) / (1 + E) * t 2 y = p y) ∧
      (∀ y, (1 - δ) / (1 + E) * t 1 y + (1 - δ) * E / (1 + E) * t 2 y + δ * t 3 y = q y) := by
  obtain ⟨p', q', hpq, hp', hq'⟩ := exists_trim hE hp hq hp₁ hq₁ hδ₁ hP hQ
  have hE₁ : (0 : ℝ) < 1 + E := by linarith
  have hc : 0 ≤ (1 - δ) / (1 + E) := div_nonneg (by linarith) hE₁.le
  set a : Y → ℝ := fun y ↦ p' y / (1 + E) + (p' y - q' y) / (E ^ 2 - 1) with ha_def
  set b : Y → ℝ := fun y ↦ q' y / (1 + E) + (q' y - p' y) / (E ^ 2 - 1) with hb_def
  have hab (y : Y) : 0 ≤ a y ∧ 0 ≤ b y ∧ E * a y + b y = p' y ∧ a y + E * b y = q' y := by
    obtain ⟨-, -, hq'₀, -, h₁, h₂⟩ := hpq y
    rcases eq_or_lt_of_le hE with h | h
    · have he : p' y = q' y := by rw [← h] at h₁ h₂; linarith
      simp only [ha_def, hb_def, he, sub_self, zero_div, add_zero, ← h]
      exact ⟨div_nonneg hq'₀ (by norm_num), div_nonneg hq'₀ (by norm_num), by ring, by ring⟩
    · have hd : 0 < E ^ 2 - 1 := by nlinarith
      have hd' : E ^ 2 - 1 ≠ 0 := hd.ne'
      have hE₁' : 1 + E ≠ 0 := hE₁.ne'
      have ha' : a y = (E * p' y - q' y) / (E ^ 2 - 1) := by
        simp only [ha_def]; field_simp; ring
      have hb' : b y = (E * q' y - p' y) / (E ^ 2 - 1) := by
        simp only [hb_def]; field_simp; ring
      rw [ha', hb']
      refine ⟨div_nonneg (by linarith) hd.le, div_nonneg (by linarith) hd.le, ?_, ?_⟩ <;>
        field_simp <;> ring
  have hsa : ∑ y, a y = (1 - δ) / (1 + E) := by
    simp only [ha_def, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, hp', hq',
      sub_self, zero_div, add_zero]
  have hsb : ∑ y, b y = (1 - δ) / (1 + E) := by
    simp only [hb_def, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, hp', hq',
      sub_self, zero_div, add_zero]
  have hs₀ : ∑ y, (p y - p' y) = δ := by rw [Finset.sum_sub_distrib, hp₁, hp']; ring
  have hs₃ : ∑ y, (q y - q' y) = δ := by rw [Finset.sum_sub_distrib, hq₁, hq']; ring
  have h₀ (y : Y) : 0 ≤ p y - p' y := sub_nonneg.2 (hpq y).2.1
  have h₃ (y : Y) : 0 ≤ q y - q' y := sub_nonneg.2 (hpq y).2.2.2.1
  have ha₀ (y : Y) : 0 ≤ a y := (hab y).1
  have hb₀ (y : Y) : 0 ≤ b y := (hab y).2.1
  refine ⟨![row (fun y ↦ p y - p' y) δ p, row a ((1 - δ) / (1 + E)) p,
    row b ((1 - δ) / (1 + E)) p, row (fun y ↦ q y - q' y) δ p], fun x y ↦ ?_, fun x ↦ ?_,
    fun y ↦ ?_, fun y ↦ ?_⟩
  · fin_cases x
    · exact row_nonneg h₀ hδ₀ hp y
    · exact row_nonneg ha₀ hc hp y
    · exact row_nonneg hb₀ hc hp y
    · exact row_nonneg h₃ hδ₀ hp y
  · fin_cases x
    · exact sum_row hs₀ hp₁
    · exact sum_row hsa hp₁
    · exact sum_row hsb hp₁
    · exact sum_row hs₃ hp₁
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination mul_row (g := p) h₀ hs₀ y + E * mul_row (g := p) ha₀ hsa y +
      mul_row (g := p) hb₀ hsb y + (hab y).2.2.1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination mul_row (g := p) ha₀ hsa y + E * mul_row (g := p) hb₀ hsb y +
      mul_row (g := p) h₃ hs₃ y + (hab y).2.2.2

end FiniteSum

/-! ### The canonical pair -/

/-- The probability mass functions `P̃₀ = canonicalProb ε δ false` and
`P̃₁ = canonicalProb ε δ true` on `{0, 1, 2, 3}` of the canonical `(ε, δ)`-DP pair, equations (17)
and (18) of Kairouz–Oh–Viswanath:
`P̃₀ = (δ, (1 - δ) e^ε / (1 + e^ε), (1 - δ) / (1 + e^ε), 0)` and
`P̃₁ = (0, (1 - δ) / (1 + e^ε), (1 - δ) e^ε / (1 + e^ε), δ)`. -/
noncomputable def canonicalProb (ε δ : ℝ) : Bool → Fin 4 → ℝ
  | false => ![δ, (1 - δ) * exp ε / (1 + exp ε), (1 - δ) / (1 + exp ε), 0]
  | true => ![0, (1 - δ) / (1 + exp ε), (1 - δ) * exp ε / (1 + exp ε), δ]

variable {ε δ : ℝ}

lemma canonicalProb_nonneg (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (b : Bool) (x : Fin 4) :
    0 ≤ canonicalProb ε δ b x := by
  have h₁ : 0 ≤ 1 - δ := by linarith
  have h₂ : 0 ≤ 1 + exp ε := by positivity
  have h₃ : 0 ≤ (1 - δ) * exp ε / (1 + exp ε) := div_nonneg (mul_nonneg h₁ (exp_pos ε).le) h₂
  have h₄ : 0 ≤ (1 - δ) / (1 + exp ε) := div_nonneg h₁ h₂
  cases b <;> fin_cases x <;> simp [canonicalProb, hδ₀, h₃, h₄]

lemma sum_canonicalProb (ε δ : ℝ) (b : Bool) : ∑ x, canonicalProb ε δ b x = 1 := by
  have h₂ : 1 + exp ε ≠ 0 := by positivity
  cases b <;> simp only [canonicalProb, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] <;> field_simp <;> ring

/-- The **canonical `(ε, δ)`-differentially private mechanism** `M̃` of Section 6.1 of
Kairouz–Oh–Viswanath, as a kernel from the hypothesis `b : Bool` (`false` for the null
hypothesis, `true` for the alternative) to `Fin 4`: it outputs `x` with probability
`canonicalProb ε δ b x`. It is a Markov kernel for `δ ∈ [0, 1]`
(`isMarkovKernel_canonicalMechanism`). -/
noncomputable def canonicalMechanism (ε δ : ℝ) : Kernel Bool (Fin 4) :=
  Kernel.ofFunOfCountable fun b ↦ ∑ x, ENNReal.ofReal (canonicalProb ε δ b x) • Measure.dirac x

lemma canonicalMechanism_apply_singleton (ε δ : ℝ) (b : Bool) (x : Fin 4) :
    canonicalMechanism ε δ b {x} = ENNReal.ofReal (canonicalProb ε δ b x) := by
  simp [canonicalMechanism, Kernel.ofFunOfCountable,
    Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator]

lemma isMarkovKernel_canonicalMechanism (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    IsMarkovKernel (canonicalMechanism ε δ) :=
  ⟨fun b ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [canonicalMechanism_apply_singleton]
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ canonicalProb_nonneg hδ₀ hδ₁ b x,
      sum_canonicalProb, ENNReal.ofReal_one]⟩⟩

lemma canonicalMechanism_real_singleton (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (b : Bool) (x : Fin 4) :
    (canonicalMechanism ε δ b).real {x} = canonicalProb ε δ b x := by
  rw [measureReal_def, canonicalMechanism_apply_singleton,
    ENNReal.toReal_ofReal (canonicalProb_nonneg hδ₀ hδ₁ b x)]

/-- The canonical pair has hockey-stick divergence `d_ε(P̃₀, P̃₁) = d_ε(P̃₁, P̃₀) = δ`
(Section 6.1, after the definition of `d_ε`: "`d_ε(P̃₀, P̃₁) = δ`"). -/
theorem hockeyStickDiv_canonicalMechanism (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (b : Bool) :
    hockeyStickDiv (exp ε) (canonicalMechanism ε δ b) (canonicalMechanism ε δ (!b)) = δ := by
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  have hE : 1 ≤ exp ε := one_le_exp hε
  have h₁ : 0 ≤ 1 - δ := by linarith
  have h₂ : 0 < 1 + exp ε := by positivity
  have k₁ : (1 - δ) * exp ε / (1 + exp ε) - exp ε * ((1 - δ) / (1 + exp ε)) = 0 := by ring
  have k₁' : (1 - δ) / (1 + exp ε) - exp ε * ((1 - δ) / (1 + exp ε)) ≤ 0 := by
    rw [show (1 - δ) / (1 + exp ε) - exp ε * ((1 - δ) / (1 + exp ε))
      = (1 - δ) * (1 - exp ε) / (1 + exp ε) by ring]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h₁ (by linarith)) h₂.le
  have k₂ : (1 - δ) / (1 + exp ε) - exp ε * ((1 - δ) * exp ε / (1 + exp ε)) ≤ 0 := by
    rw [show (1 - δ) / (1 + exp ε) - exp ε * ((1 - δ) * exp ε / (1 + exp ε))
      = (1 - δ) * (1 - exp ε * exp ε) / (1 + exp ε) by ring]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h₁ (by nlinarith)) h₂.le
  have k₃ : 0 - exp ε * δ ≤ 0 := by nlinarith
  rw [hockeyStickDiv_eq_sum]
  simp only [canonicalMechanism_real_singleton hδ₀ hδ₁]
  cases b <;> simp only [canonicalProb, Bool.not_false, Bool.not_true, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_zero, sub_zero]
  · rw [max_eq_right hδ₀, k₁, max_self, max_eq_left k₂, max_eq_left k₃]
    ring
  · rw [max_eq_right hδ₀, k₁, max_self, max_eq_left k₂, max_eq_left k₃]
    ring

/-- The canonical mechanism is `(ε, δ)`-differentially private when every pair of hypotheses is
neighbouring, tight at slope `e^ε` (`hockeyStickDiv_canonicalMechanism`). This is one inclusion
of Section 6.1's "the privacy region of a single access to this mechanism is `R(ε, δ)`". -/
theorem isEpsDeltaDP_canonicalMechanism (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    IsEpsDeltaDP (canonicalMechanism ε δ) (fun _ _ ↦ True) ε δ := by
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  refine isEpsDeltaDP_iff_forall_hockeyStickDiv_le.2 fun b b' _ ↦ ?_
  cases b <;> cases b'
  · exact (hockeyStickDiv_self (one_le_exp hε)).trans_le hδ₀
  · exact (hockeyStickDiv_canonicalMechanism hε hδ₀ hδ₁ false).le
  · exact (hockeyStickDiv_canonicalMechanism hε hδ₀ hδ₁ true).le
  · exact (hockeyStickDiv_self (one_le_exp hε)).trans_le hδ₀

/-! ### Every `(ε, δ)`-DP pair is simulated by the canonical pair -/

section Simulation

variable {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]

omit [MeasurableSingletonClass Y] in
private lemma ext_of_measureReal_singleton [Countable Y] {μ ν : Measure Y} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ y, μ.real {y} = ν.real {y}) : μ = ν :=
  Measure.ext_of_singleton fun y ↦
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (h y)

/-- **Every `(ε, δ)`-indistinguishable pair is a post-processing of the canonical pair.**
For probability measures `μ, ν` on a finite alphabet `Y` (with measurable singletons), `ε ≥ 0`
and `δ ∈ [0, 1]`, there is a Markov kernel `T : Fin 4 → Y` with `T ∘ P̃₀ = μ` and `T ∘ P̃₁ = ν`
iff `D_{e^ε}(μ ‖ ν) ≤ δ` and `D_{e^ε}(ν ‖ μ) ≤ δ`, i.e. iff
`μ(S) ≤ e^ε ν(S) + δ` and `ν(S) ≤ e^ε μ(S) + δ` for every `S`.

This is the step of Section 6.1 of Kairouz–Oh–Viswanath (arXiv v4): "by Theorem 2.5, all
`(ε, δ)`-differentially private mechanisms are dominated by this mechanism". The paper derives it
from Blackwell's theorem (Theorem 2.5) and the privacy-region characterization (Theorem 2.1);
here the kernel `T` is constructed explicitly, and Blackwell's theorem itself is not used. The
direction `⟹` is the data-processing inequality (Theorem 2.4, `hockeyStickDiv_comp_le`). -/
theorem exists_kernel_comp_canonicalMechanism_iff [Finite Y] {μ ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ)
    (hδ₁ : δ ≤ 1) :
    (∃ T : Kernel (Fin 4) Y, IsMarkovKernel T ∧ T ∘ₘ canonicalMechanism ε δ false = μ ∧
      T ∘ₘ canonicalMechanism ε δ true = ν) ↔
      hockeyStickDiv (exp ε) μ ν ≤ δ ∧ hockeyStickDiv (exp ε) ν μ ≤ δ := by
  have := Fintype.ofFinite Y
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  constructor
  · rintro ⟨T, hT, rfl, rfl⟩
    exact ⟨(hockeyStickDiv_comp_le T _ _).trans
        (hockeyStickDiv_canonicalMechanism hε hδ₀ hδ₁ false).le,
      (hockeyStickDiv_comp_le T _ _).trans
        (hockeyStickDiv_canonicalMechanism hε hδ₀ hδ₁ true).le⟩
  · rintro ⟨hP, hQ⟩
    rw [hockeyStickDiv_eq_sum] at hP hQ
    obtain ⟨t, ht₀, ht₁, hp, hq⟩ := exists_stochastic (one_le_exp hε) hδ₀ hδ₁
      (fun y ↦ measureReal_nonneg (μ := μ) (s := {y}))
      (fun y ↦ measureReal_nonneg (μ := ν) (s := {y})) (by simp) (by simp) hP hQ
    set T : Kernel (Fin 4) Y :=
      Kernel.ofFunOfCountable fun x ↦ ∑ y, ENNReal.ofReal (t x y) • Measure.dirac y
    have hT (x : Fin 4) (y : Y) : T x {y} = ENNReal.ofReal (t x y) := by
      classical
      simp [T, Kernel.ofFunOfCountable, Measure.dirac_apply' _ (measurableSet_singleton y),
        Set.indicator, Set.mem_singleton_iff]
    have : IsMarkovKernel T := ⟨fun x ↦ ⟨by
      rw [← Finset.coe_univ, ← sum_measure_singleton]
      simp_rw [hT]
      rw [← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ ht₀ x y, ht₁, ENNReal.ofReal_one]⟩⟩
    have hTr (x : Fin 4) (y : Y) : (T x).real {y} = t x y := by
      rw [measureReal_def, hT, ENNReal.toReal_ofReal (ht₀ x y)]
    refine ⟨T, this, ext_of_measureReal_singleton fun y ↦ ?_,
      ext_of_measureReal_singleton fun y ↦ ?_⟩
    · rw [measureReal_comp_singleton, ← hp y]
      simp only [hTr, canonicalMechanism_real_singleton hδ₀ hδ₁, Fin.sum_univ_four,
        canonicalProb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    · rw [measureReal_comp_singleton, ← hq y]
      simp only [hTr, canonicalMechanism_real_singleton hδ₀ hδ₁, Fin.sum_univ_four,
        canonicalProb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring

/-- **The canonical mechanism dominates every `(ε, δ)`-DP mechanism** (Section 6.1 of
Kairouz–Oh–Viswanath, via Theorems 2.1 and 2.5): for a Markov kernel `M` into a finite alphabet
and a symmetric neighbouring relation, `M` is `(ε, δ)`-DP iff for all neighbours `S, S'` there is
a Markov kernel `T` with `T ∘ P̃₀ = M(S)` and `T ∘ P̃₁ = M(S')`. Here `ε ≥ 0` and
`δ ∈ [0, 1]`. -/
theorem isEpsDeltaDP_iff_forall_exists_kernel {𝒟 : Type*} [MeasurableSpace 𝒟] [Finite Y]
    {M : Kernel 𝒟 Y} [IsMarkovKernel M] {Adj : 𝒟 → 𝒟 → Prop} [Std.Symm Adj] (hε : 0 ≤ ε)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    IsEpsDeltaDP M Adj ε δ ↔ ∀ ⦃S S'⦄, Adj S S' → ∃ T : Kernel (Fin 4) Y, IsMarkovKernel T ∧
      T ∘ₘ canonicalMechanism ε δ false = M S ∧ T ∘ₘ canonicalMechanism ε δ true = M S' := by
  rw [isEpsDeltaDP_iff_forall_hockeyStickDiv_le]
  exact ⟨fun h S S' hS ↦ (exists_kernel_comp_canonicalMechanism_iff hε hδ₀ hδ₁).2
      ⟨h hS, h (Std.Symm.symm _ _ hS)⟩,
    fun h S S' hS ↦ ((exists_kernel_comp_canonicalMechanism_iff hε hδ₀ hδ₁).1 (h hS)).1⟩

end Simulation

end OptimalComposition

end InformationTheory
