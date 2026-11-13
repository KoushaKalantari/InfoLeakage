/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Exponential
public import InfoLeakage.DP.Basic
public import Mathlib.InformationTheory.Hamming

/-!
# Identifiability, differential privacy and Hamming distortion

This file formalizes results of W. Wang, L. Ying and J. Zhang, *On the relation between
identifiability, differential privacy and mutual-information privacy*, IEEE Trans. Inf. Theory
62(9), 2016 ([arXiv:1402.3757](https://arxiv.org/abs/1402.3757)); numbers refer to arXiv v3.

A database `x : ι → D` has `n = |ι|` rows with values in a finite domain `D` of size `m ≥ 2`, a
prior `pX` is a probability measure on databases, and a mechanism is a Markov kernel
`M : Kernel (ι → D) (ι → D)` releasing a synthetic database. Neighbours have Hamming distance one,
and `ε`-DP (Definition 3) is `IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε`, whose pointwise
form (2) is `isEpsDP_iff_forall_singleton`. Distortion is the expected Hamming distance (5).

## Main definitions

* `Identifiability.outputProb`, `Identifiability.posterior`: `p_Y` and `p_{X|Y}`.
* `IsIdentifiable pX M ε`: `ε`-identifiability (Definition 2).
* `Identifiability.distortion pX M`: the expected Hamming distortion (5).
* `Identifiability.optDistortion ι D ε`: the function `h(ε) = n / (1 + e^ε / (m - 1))` of (32),
  and `Identifiability.invOptDistortion ι D` its inverse `h⁻¹` of (17).
* `Identifiability.hammingExpMechanism ι D ε`: the mechanism `E_d` of (27).
* `dpPrivacyDistortion pX`, `idPrivacyDistortion pX`: the privacy–distortion functions `ε*_d`
  and `ε*_i` of (6).

## Main statements (paper result → Lean name)

* Lemma 1, claim (33) → `Identifiability.optDistortion_le_sum_mul_hammingDist`; the
  normalization and distortion computations (41)–(42) of its second claim →
  `Identifiability.sum_exp_neg_mul_hammingDist`, `Identifiability.sum_exp_neg_mul_hammingDist_mul`.
* Lemma 2, (43) and (44), in distortion form → `IsIdentifiable.optDistortion_le_distortion`,
  `IsEpsDP.optDistortion_le_distortion`.
* Lemma 3, pointwise form → `IsIdentifiable.measureReal_le`.
* Equation (25) (`ε`-DP implies `(ε + ε_X)`-identifiability) → `IsEpsDP.isIdentifiable`.
* Lemma 5 → `isEpsDP_hammingExpMechanism`, `distortion_hammingExpMechanism`.
* Theorem 1, (19), for `0 < D < n`: upper bound (any prior) →
  `dpPrivacyDistortion_le_max_invOptDistortion`; lower bound →
  `max_invOptDistortion_sub_le_dpPrivacyDistortion`, together with `dpPrivacyDistortion_nonneg`.
* Theorem 1, (18), lower bound `ε*_i(D) ≥ max {h⁻¹(D), ε_X}`, for `0 < D < n` and pairwise in
  `ε_X` → `max_invOptDistortion_log_le_idPrivacyDistortion` (from
  `invOptDistortion_le_idPrivacyDistortion` and `log_div_le_idPrivacyDistortion`).
* Identifiability in terms of the joint law → `Identifiability.isIdentifiable_iff`.

## Implementation notes

* The constant `ε_X` of (16) is not defined: results take any `ε_X` with
  `p_X(x) ≤ e^{ε_X} p_X(x')` for all neighbours, of which (16) is the least (finite exactly when
  `pX` has full support). With (16) itself they are the paper's statements.
* The posterior is `0` when `p_Y(y) = 0`; identifiability then holds trivially at `y`, as it does
  for the paper's joint-law form `isIdentifiable_iff`.
* The privacy–distortion functions take the infimum over real `ε ≥ 0` (the paper allows
  `ε = +∞`) in `EReal`, where an empty set has infimum `⊤`. Theorem 1 is stated for `0 < D < n`,
  where `h⁻¹(D)` is a real number; at `D = 0` and `D = n` the paper's `h⁻¹` is `±∞`.
* Claim (33) is proved row by row rather than by the paper's layer-by-layer reduction: changing
  row `i` away from `y_i` gives `(m - 1)` neighbours, so `P(X_i ≠ y_i) ≥ r P(X_i = y_i)` with
  `r = (m - 1) e^{-ε}` (`Identifiability.card_sub_one_mul_le_sum_ne`), and `h(ε) = n r / (1 + r)`.
* `E_d` is Dwork–Roth's exponential mechanism `exponentialMechanism` with score `-d`, privacy
  parameter `2ε` and sensitivity `1`. Its generic privacy bound only gives `2ε`-DP; Lemma 5's `ε`
  uses that the normalizing constant `(1 + (m - 1) e^{-ε})^n` does not depend on the input.

## Notes on the paper

* Appendix A, proof of Lemma 1, second claim (verification of constraint (20), p. 12 of v3): the
  triangle inequality is written `d(x, y) ≤ d(x', y) - d(x', x) = d(x', y) - 1`; it should read
  `d(x, y) ≥ d(x', y) - d(x', x)`, which is what the next display uses. The claim is true (its
  computation is the one in the proof of `isEpsDP_hammingExpMechanism`).

## Not formalized

* Lemma 1 as stated, (31): that the optimum of R-PD equals `h(ε)`, in particular the feasibility
  of the posterior (41) for some output law; claim (33) gives the lower bound `≥ h(ε)`.
* Lemma 4 (the mechanism `E_i` of (26) and the constant `ε̃_X`), hence the equality case and the
  upper bound in (18), and the endpoints `D = 0`, `D = n` of (19).
* Section 4: mutual-information privacy (Definition 4) and Theorem 2 (optimality of `E_i` for the
  rate–distortion problem PD-MIP, via the KKT conditions).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset

namespace InformationTheory

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]
  [MeasurableSpace D]

namespace Identifiability

/-- The output law `p_Y(y) = ∑_x p_X(x) p_{Y|X}(y | x)` of the mechanism `M` on input `X ∼ pX`. -/
noncomputable def outputProb (pX : Measure (ι → D)) (M : Kernel (ι → D) (ι → D)) (y : ι → D) : ℝ :=
  ∑ x, pX.real {x} * (M x).real {y}

/-- The posterior `p_{X|Y}(x | y) = p_X(x) p_{Y|X}(y | x) / p_Y(y)` (with the convention `0` when
`p_Y(y) = 0`). -/
noncomputable def posterior (pX : Measure (ι → D)) (M : Kernel (ι → D) (ι → D)) (x y : ι → D) :
    ℝ :=
  pX.real {x} * (M x).real {y} / outputProb pX M y

/-- The expected Hamming distortion `E[d(X, Y)] = ∑_{x,y} p_X(x) p_{Y|X}(y | x) d(x, y)` (WYZ,
equation (5)). -/
noncomputable def distortion (pX : Measure (ι → D)) (M : Kernel (ι → D) (ι → D)) : ℝ :=
  ∑ x, ∑ y, pX.real {x} * (M x).real {y} * hammingDist x y

variable (ι D) in
/-- The function `h(ε) = n / (1 + e^ε / (m - 1))` of WYZ, equation (32), where `n` is the number
of rows and `m` the size of the row domain: the least distortion of the relaxed problem R-PD. -/
noncomputable def optDistortion (ε : ℝ) : ℝ :=
  Fintype.card ι / (1 + exp ε / (Fintype.card D - 1))

end Identifiability

open Identifiability

/-- **Identifiability** (Wang–Ying–Zhang, Definition 2): the mechanism `M` with input prior `pX`
is `ε`-identifiable if `p_{X|Y}(x | y) ≤ e^ε p_{X|Y}(x' | y)` for all neighbouring databases
`x, x'` (Hamming distance one) and all outputs `y`. -/
def IsIdentifiable (pX : Measure (ι → D)) (M : Kernel (ι → D) (ι → D)) (ε : ℝ) : Prop :=
  ∀ ⦃x x'⦄, hammingDist x x' = 1 → ∀ y, posterior pX M x y ≤ exp ε * posterior pX M x' y

variable {pX : Measure (ι → D)} {M : Kernel (ι → D) (ι → D)} {ε εX : ℝ}

namespace Identifiability

/-- Identifiability in terms of the joint law: `p(x) p(y | x) ≤ e^ε p(x') p(y | x')`. -/
theorem isIdentifiable_iff : IsIdentifiable pX M ε ↔ ∀ ⦃x x'⦄, hammingDist x x' = 1 → ∀ y,
    pX.real {x} * (M x).real {y} ≤ exp ε * (pX.real {x'} * (M x').real {y}) := by
  have hj (x y : ι → D) : 0 ≤ pX.real {x} * (M x).real {y} :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  refine ⟨fun h x x' hxx' y ↦ ?_, fun h x x' hxx' y ↦ ?_⟩
  · rcases (sum_nonneg fun x _ ↦ hj x y : 0 ≤ outputProb pX M y).eq_or_lt with h0 | hpos
    · have := (sum_eq_zero_iff_of_nonneg fun x _ ↦ hj x y).1 h0.symm x (mem_univ _)
      rw [this]
      exact mul_nonneg (exp_pos _).le (hj _ _)
    · have := h hxx' y
      rw [posterior, posterior, mul_div_assoc'] at this
      exact (div_le_div_iff_of_pos_right (hpos : 0 < outputProb pX M y)).1 this
  · rw [posterior, posterior, mul_div_assoc']
    exact div_le_div_of_nonneg_right (h hxx' y) (sum_nonneg fun x _ ↦ hj x y)

end Identifiability

variable [MeasurableSingletonClass D]

/-- **Wang–Ying–Zhang, Lemma 3** (pointwise form): an `ε`-identifiable mechanism forces
`p_X(x) ≤ e^ε p_X(x')` for all neighbouring `x, x'`, i.e. `ε ≥ ε_X` with `ε_X` of (16). -/
theorem IsIdentifiable.measureReal_le [IsMarkovKernel M] (h : IsIdentifiable pX M ε) {x x' : ι → D}
    (hxx' : hammingDist x x' = 1) : pX.real {x} ≤ exp ε * pX.real {x'} := by
  have hs : ∑ y, pX.real {x} * (M x).real {y} ≤ ∑ y, exp ε * (pX.real {x'} * (M x').real {y}) :=
    sum_le_sum fun y _ ↦ isIdentifiable_iff.1 h hxx' y
  simpa [← mul_sum] using hs

/-- **Wang–Ying–Zhang, equation (25)** (the relaxation step in the proof of Theorem 1): if `M` is
`ε`-DP and the prior satisfies `p_X(x) ≤ e^{ε_X} p_X(x')` for all neighbours (that is,
`ε_X` is at least the constant (16)), then `M` is `(ε + ε_X)`-identifiable. -/
theorem IsEpsDP.isIdentifiable [IsFiniteKernel M]
    (h : IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε)
    (hX : ∀ ⦃x x' : ι → D⦄, hammingDist x x' = 1 → pX.real {x} ≤ exp εX * pX.real {x'}) :
    IsIdentifiable pX M (ε + εX) := by
  refine isIdentifiable_iff.2 fun x x' hxx' y ↦ ?_
  calc pX.real {x} * (M x).real {y} ≤ (exp εX * pX.real {x'}) * (exp ε * (M x').real {y}) :=
        mul_le_mul (hX hxx') (isEpsDP_iff_forall_singleton.1 h hxx' y) measureReal_nonneg
          (mul_nonneg (exp_pos _).le measureReal_nonneg)
    _ = exp (ε + εX) * (pX.real {x'} * (M x').real {y}) := by rw [exp_add]; ring

namespace Identifiability

omit [DecidableEq ι] [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- Changing the `i`-th row of a database to a different value gives a Hamming neighbour. -/
lemma hammingDist_funSplitAt_symm [DecidableEq ι] (i : ι) {c c' : D} (hc : c ≠ c')
    (r : {j // j ≠ i} → D) :
    hammingDist ((Equiv.funSplitAt i D).symm (c, r)) ((Equiv.funSplitAt i D).symm (c', r)) = 1 := by
  rw [hammingDist, ← card_singleton i]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.funSplitAt_symm_apply, hc]
  · simp [Equiv.funSplitAt_symm_apply, hj]

omit [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- The per-row step of the proof of the claim in Lemma 1: if `q` is a law on databases with
`q(x) ≤ e^ε q(x')` for all neighbours, then the probability that row `i` differs from `y_i` is at
least `(m - 1) e^{-ε}` times the probability that it agrees with `y_i`. -/
lemma card_sub_one_mul_le_sum_ne {q : (ι → D) → ℝ}
    (hq : ∀ ⦃x x' : ι → D⦄, hammingDist x x' = 1 → q x ≤ exp ε * q x') (i : ι) (c : D) :
    (Fintype.card D - 1) * exp (-ε) * ∑ x with x i = c, q x ≤ ∑ x with x i ≠ c, q x := by
  set e := Equiv.funSplitAt i D
  have hsplit (p : D → Prop) [DecidablePred p] :
      ∑ x with p (x i), q x = ∑ c' with p c', ∑ r, q (e.symm (c', r)) := by
    rw [sum_filter, ← e.symm.sum_comp, Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun c' _ ↦ ?_
    split_ifs with h <;> simp [e, Equiv.funSplitAt_symm_apply, h]
  rw [hsplit (· = c), hsplit (· ≠ c), filter_eq']
  simp only [mem_univ, ↓reduceIte, sum_singleton]
  have hcard : ((#({c' | c' ≠ c} : Finset D) : ℕ) : ℝ) = Fintype.card D - 1 := by
    rw [filter_ne' univ c, card_erase_of_mem (mem_univ c), card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.2 ⟨c⟩)]
    simp
  rw [← hcard, ← nsmul_eq_mul, ← sum_const, sum_mul]
  refine sum_le_sum fun c' hc' ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun r _ ↦ ?_
  have := hq (hammingDist_funSplitAt_symm i (Ne.symm (mem_filter.1 hc').2) r)
  calc exp (-ε) * q (e.symm (c, r)) ≤ exp (-ε) * (exp ε * q (e.symm (c', r))) :=
        mul_le_mul_of_nonneg_left this (exp_pos _).le
    _ = q (e.symm (c', r)) := by rw [← mul_assoc, ← exp_add]; simp

omit [DecidableEq ι] [DecidableEq D] [MeasurableSpace D] in
/-- `h(ε) = n r / (1 + r)` with `r = (m - 1) e^{-ε}`, for `m ≥ 2`. -/
lemma optDistortion_eq (hm : 2 ≤ Fintype.card D) (ε : ℝ) :
    optDistortion ι D ε = Fintype.card ι * ((Fintype.card D - 1) * exp (-ε) /
      (1 + (Fintype.card D - 1) * exp (-ε))) := by
  have hm' : (0 : ℝ) < Fintype.card D - 1 := by
    have : (2 : ℝ) ≤ Fintype.card D := by exact_mod_cast hm
    linarith
  rw [optDistortion, exp_neg]
  field_simp
  ring

omit [MeasurableSpace D] in
/-- **Wang–Ying–Zhang, Lemma 1, claim (33)**: every law `q` on databases (a feasible posterior
`p_{X|Y}(· | y)` of the relaxed problem R-PD) with `q(x) ≤ e^ε q(x')` for all neighbours has
`∑_x q(x) d(x, y) ≥ h(ε)`, for any row domain with `m ≥ 2` values. The proof is not the paper's
layer-by-layer argument but a row-by-row one: by `card_sub_one_mul_le_sum_ne`, row `i` differs
from `y_i` with probability at least `r / (1 + r)`, `r = (m - 1) e^{-ε}`, and
`h(ε) = n r / (1 + r)`. -/
theorem optDistortion_le_sum_mul_hammingDist (hm : 2 ≤ Fintype.card D) {q : (ι → D) → ℝ}
    (hq1 : ∑ x, q x = 1) (hq : ∀ ⦃x x' : ι → D⦄, hammingDist x x' = 1 → q x ≤ exp ε * q x')
    (y : ι → D) : optDistortion ι D ε ≤ ∑ x, q x * hammingDist x y := by
  set r : ℝ := (Fintype.card D - 1) * exp (-ε)
  have hr : 0 ≤ r := by
    have : (2 : ℝ) ≤ Fintype.card D := by exact_mod_cast hm
    exact mul_nonneg (by linarith) (exp_pos _).le
  have hd : ∑ x, q x * hammingDist x y = ∑ i, ∑ x with x i ≠ y i, q x := by
    simp_rw [hammingDist, natCast_card_filter, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    simp_rw [sum_filter]
  have hb (i : ι) : r / (1 + r) ≤ ∑ x with x i ≠ y i, q x := by
    have h₁ := card_sub_one_mul_le_sum_ne hq i (y i)
    have h₂ := sum_filter_add_sum_filter_not univ (fun x : ι → D ↦ x i = y i) q
    rw [hq1] at h₂
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [hd, optDistortion_eq hm]
  calc Fintype.card ι * (r / (1 + r)) = ∑ _i : ι, r / (1 + r) := by simp
    _ ≤ _ := sum_le_sum fun i _ ↦ hb i

end Identifiability

open Identifiability

variable [IsProbabilityMeasure pX] [IsMarkovKernel M]

/-- **Wang–Ying–Zhang, Lemma 2, (43)**, in distortion form: an `ε`-identifiable mechanism has
expected Hamming distortion at least `h(ε)` (equivalently `ε*_i(D) ≥ h⁻¹(D)`). Row domains have
`m ≥ 2` values, as in the paper. -/
theorem IsIdentifiable.optDistortion_le_distortion (hm : 2 ≤ Fintype.card D)
    (h : IsIdentifiable pX M ε) : optDistortion ι D ε ≤ distortion pX M := by
  have hJ (x y : ι → D) : 0 ≤ pX.real {x} * (M x).real {y} :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  have hY : ∑ y, outputProb pX M y = 1 := by
    simp_rw [outputProb]
    rw [sum_comm]
    simp [← mul_sum]
  have key (y : ι → D) : outputProb pX M y * optDistortion ι D ε ≤
      ∑ x, pX.real {x} * (M x).real {y} * hammingDist x y := by
    rcases (show 0 ≤ outputProb pX M y from sum_nonneg fun x _ ↦ hJ x y).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      exact sum_nonneg fun x _ ↦ mul_nonneg (hJ x y) (Nat.cast_nonneg _)
    have hq1 : ∑ x, posterior pX M x y = 1 := by
      simp_rw [posterior, ← sum_div]
      exact div_self hpos.ne'
    have := optDistortion_le_sum_mul_hammingDist hm hq1 (fun x x' hxx' ↦ h hxx' y) y
    rw [mul_comm, ← le_div_iff₀ hpos]
    refine this.trans_eq ?_
    simp_rw [posterior, sum_div, div_mul_eq_mul_div]
  calc optDistortion ι D ε = ∑ y, outputProb pX M y * optDistortion ι D ε := by
        rw [← sum_mul, hY, one_mul]
    _ ≤ ∑ y, ∑ x, pX.real {x} * (M x).real {y} * hammingDist x y := sum_le_sum fun y _ ↦ key y
    _ = distortion pX M := sum_comm

/-- **Wang–Ying–Zhang, Lemma 2, (44)**, in distortion form: if `M` is `ε`-DP and `ε_X` bounds the
log prior ratio of neighbours as in (16), then `M` has expected Hamming distortion at least
`h(ε + ε_X)` (equivalently `ε*_d(D) ≥ h⁻¹(D) - ε_X`). -/
theorem IsEpsDP.optDistortion_le_distortion (hm : 2 ≤ Fintype.card D)
    (h : IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε)
    (hX : ∀ ⦃x x' : ι → D⦄, hammingDist x x' = 1 → pX.real {x} ≤ exp εX * pX.real {x'}) :
    optDistortion ι D (ε + εX) ≤ distortion pX M :=
  (h.isIdentifiable hX).optDistortion_le_distortion hm

/-! ### The exponential mechanism `E_d` -/

namespace Identifiability

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- `∑_c (if c₀ = c then b else a) = b + (m - 1) a`. -/
private lemma sum_ite_eq_add (c₀ : D) (a b : ℝ) :
    ∑ c, (if c₀ = c then b else a) = b + (Fintype.card D - 1) * a := by
  rw [sum_ite, filter_eq, filter_ne]
  simp only [mem_univ, ↓reduceIte, sum_const, card_singleton, one_smul,
    card_erase_of_mem, card_univ, nsmul_eq_mul]
  rw [Nat.cast_sub (Fintype.card_pos_iff.2 ⟨c₀⟩), Nat.cast_one]

omit [DecidableEq ι] [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- `e^{-ε d(x, y)}` factorizes over the rows. -/
private lemma exp_neg_mul_hammingDist (ε : ℝ) (x y : ι → D) :
    exp (-ε * hammingDist x y) = ∏ i, (if x i = y i then 1 else exp (-ε)) := by
  rw [hammingDist, natCast_card_filter, mul_sum, exp_sum]
  refine prod_congr rfl fun i _ ↦ ?_
  by_cases h : x i = y i <;> simp [h]

omit [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- The normalizing constant of `E_d`: `∑_y e^{-ε d(x, y)} = (1 + (m - 1) e^{-ε})^n`. -/
lemma sum_exp_neg_mul_hammingDist (ε : ℝ) (x : ι → D) :
    ∑ y, exp (-ε * hammingDist x y) =
      (1 + (Fintype.card D - 1) * exp (-ε)) ^ Fintype.card ι := by
  simp_rw [exp_neg_mul_hammingDist]
  rw [← Fintype.prod_sum (fun i c ↦ if x i = c then (1 : ℝ) else exp (-ε))]
  simp_rw [sum_ite_eq_add]
  rw [prod_const, card_univ]

omit [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- `∑_y e^{-ε d(x, y)} d(x, y) = n (A / B) B^n` with `A = (m - 1) e^{-ε}` and `B = 1 + A`. -/
lemma sum_exp_neg_mul_hammingDist_mul [Nonempty D] (ε : ℝ) (x : ι → D) :
    ∑ y, exp (-ε * hammingDist x y) * hammingDist x y =
      Fintype.card ι * ((Fintype.card D - 1) * exp (-ε) /
        (1 + (Fintype.card D - 1) * exp (-ε))) *
        (1 + (Fintype.card D - 1) * exp (-ε)) ^ Fintype.card ι := by
  set A : ℝ := (Fintype.card D - 1) * exp (-ε)
  set B : ℝ := 1 + A
  have hB : 0 < B := by
    have : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
    have : 0 ≤ A := mul_nonneg (by linarith) (exp_pos _).le
    linarith
  have hd (y : ι → D) : (hammingDist x y : ℝ) = ∑ i, if x i = y i then 0 else 1 := by
    rw [hammingDist, natCast_card_filter]
    exact sum_congr rfl fun i _ ↦ by by_cases h : x i = y i <;> simp [h]
  have key (i : ι) : ∑ y : ι → D, (∏ j, if x j = y j then 1 else exp (-ε)) *
      (if x i = y i then 0 else 1) = A / B * B ^ Fintype.card ι := by
    have h₁ (y : ι → D) : (∏ j, if x j = y j then 1 else exp (-ε)) * (if x i = y i then 0 else 1) =
        ∏ j, ((if x j = y j then 1 else exp (-ε)) *
          if j = i then (if x j = y j then 0 else 1) else 1) := by
      rw [prod_mul_distrib, prod_ite_eq' univ i]
      simp
    simp_rw [h₁]
    rw [← Fintype.prod_sum (fun j c ↦ (if x j = c then 1 else exp (-ε)) *
      if j = i then (if x j = c then 0 else 1) else (1 : ℝ))]
    have h₂ (j : ι) : ∑ c, (if x j = c then 1 else exp (-ε)) *
        (if j = i then (if x j = c then 0 else 1) else (1 : ℝ)) =
          B * (if j = i then A / B else 1) := by
      by_cases hj : j = i
      · have h₃ (c : D) : (if x j = c then 1 else exp (-ε)) * (if x j = c then 0 else (1 : ℝ)) =
            if x j = c then 0 else exp (-ε) := by split_ifs <;> simp
        subst hj
        simp only [↓reduceIte]
        simp_rw [h₃]
        rw [sum_ite_eq_add, mul_div_cancel₀ _ hB.ne', zero_add]
      · simp only [hj, ↓reduceIte, mul_one]
        rw [sum_ite_eq_add]
    simp_rw [h₂]
    rw [prod_mul_distrib, prod_const, card_univ, prod_ite_eq' univ i]
    simp only [mem_univ, ↓reduceIte]
    ring
  simp_rw [exp_neg_mul_hammingDist]
  simp_rw [hd, mul_sum]
  rw [sum_comm]
  simp_rw [key]
  rw [sum_const, card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq D] [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- The normalizing base `1 + (m - 1) e^{-ε}` is positive. -/
private lemma one_add_mul_exp_pos [Nonempty D] (ε : ℝ) :
    0 < 1 + (Fintype.card D - 1) * exp (-ε) := by
  have : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
  have : 0 ≤ (Fintype.card D - 1) * exp (-ε) := mul_nonneg (by linarith) (exp_pos _).le
  linarith

variable (ι D) in
/-- The mechanism `E_d` of Wang–Ying–Zhang, (27): on input `x`, output `y` with probability
`e^{-ε d(x, y)} / (1 + (m - 1) e^{-ε})^n`. It is the exponential mechanism with score `-d`
(Dwork–Roth's calibration with privacy parameter `2ε` and sensitivity `1`), see
`hammingExpMechanism_real_singleton`. -/
noncomputable def hammingExpMechanism (ε : ℝ) : Kernel (ι → D) (ι → D) :=
  exponentialMechanism (fun x y ↦ -(hammingDist x y : ℝ)) (2 * ε) 1

/-- The output probabilities of `E_d`, WYZ (27): `e^{-ε d(x, y)} / (1 + (m - 1) e^{-ε})^n`. -/
lemma hammingExpMechanism_real_singleton (ε : ℝ) (x y : ι → D) :
    (hammingExpMechanism ι D ε x).real {y} = exp (-ε * hammingDist x y) /
      (1 + (Fintype.card D - 1) * exp (-ε)) ^ Fintype.card ι := by
  classical
  rw [hammingExpMechanism, exponentialMechanism_real_apply (fun _ ↦ measurable_of_finite _) x {y}]
  have hf : ({r | r ∈ ({y} : Set (ι → D))} : Finset (ι → D)) = {y} := by ext; simp
  have h2 (t : ℝ) : 2 * ε * -t / (2 * 1) = -ε * t := by ring
  rw [hf, sum_singleton, exponentialMechanismProb]
  simp_rw [h2]
  rw [sum_exp_neg_mul_hammingDist]

/-- `E_d` is a Markov kernel. -/
instance [Nonempty D] (ε : ℝ) : IsMarkovKernel (hammingExpMechanism ι D ε) :=
  isMarkovKernel_exponentialMechanism fun _ ↦ measurable_of_finite _

end Identifiability

open Identifiability

/-- **Wang–Ying–Zhang, Lemma 5**, privacy part: for `ε ≥ 0`, the mechanism `E_d` is `ε`-DP. (The
general bound for the exponential mechanism only gives `2ε`; here the normalizing constant does
not depend on the input.) -/
theorem isEpsDP_hammingExpMechanism [Nonempty D] (hε : 0 ≤ ε) :
    IsEpsDP (hammingExpMechanism ι D ε) (fun x x' ↦ hammingDist x x' = 1) ε := by
  refine isEpsDP_iff_forall_singleton.2 fun x x' hxx' y ↦ ?_
  rw [hammingExpMechanism_real_singleton, hammingExpMechanism_real_singleton, mul_div_assoc',
    div_le_div_iff_of_pos_right (pow_pos (one_add_mul_exp_pos ε) _), ← exp_add, exp_le_exp]
  have h := hammingDist_triangle x' x y
  rw [hammingDist_comm x' x, hxx'] at h
  have h' : (hammingDist x' y : ℝ) ≤ 1 + hammingDist x y := by exact_mod_cast h
  nlinarith

/-- **Wang–Ying–Zhang, Lemma 5**, distortion part: for every prior, the expected Hamming
distortion of `E_d` is `h(ε)` (row domains have `m ≥ 2` values). -/
theorem distortion_hammingExpMechanism (hm : 2 ≤ Fintype.card D) (ε : ℝ) :
    distortion pX (hammingExpMechanism ι D ε) = optDistortion ι D ε := by
  have : Nonempty D := Fintype.card_pos_iff.1 (by omega)
  have hB := one_add_mul_exp_pos (D := D) ε
  have hx (x : ι → D) : ∑ y, (hammingExpMechanism ι D ε x).real {y} * hammingDist x y =
      optDistortion ι D ε := by
    simp_rw [hammingExpMechanism_real_singleton, div_mul_eq_mul_div, ← sum_div,
      sum_exp_neg_mul_hammingDist_mul, optDistortion_eq hm]
    exact mul_div_cancel_right₀ _ (pow_pos hB _).ne'
  simp_rw [distortion, mul_assoc, ← mul_sum, hx, ← sum_mul]
  simp

/-! ### Privacy–distortion functions -/

namespace Identifiability

variable (ι D) in
/-- The inverse `h⁻¹(D) = ln (n / D - 1) + ln (m - 1)` of `h = optDistortion`, WYZ (17). It is the
inverse of `h` for `0 < D < n` (`optDistortion_le_iff`). -/
noncomputable def invOptDistortion (Dist : ℝ) : ℝ :=
  log (Fintype.card ι / Dist - 1) + log (Fintype.card D - 1)

omit [DecidableEq ι] [DecidableEq D] [MeasurableSpace D] [MeasurableSingletonClass D] in
/-- `h(t) ≤ D ↔ h⁻¹(D) ≤ t` for `0 < D < n` and `m ≥ 2`: `h` is a decreasing bijection from `ℝ`
onto `(0, n)` with inverse `h⁻¹`. -/
lemma optDistortion_le_iff (hm : 2 ≤ Fintype.card D) {Dist : ℝ} (hD : 0 < Dist)
    (hDn : Dist < Fintype.card ι) (t : ℝ) :
    optDistortion ι D t ≤ Dist ↔ invOptDistortion ι D Dist ≤ t := by
  have hK : (0 : ℝ) < Fintype.card D - 1 := by
    have : (2 : ℝ) ≤ Fintype.card D := by exact_mod_cast hm
    linarith
  have hn : 0 < (Fintype.card ι : ℝ) / Dist - 1 := by
    rw [sub_pos, one_lt_div hD]; exact hDn
  rw [optDistortion, invOptDistortion, ← log_mul hn.ne' hK.ne', log_le_iff_le_exp (by positivity),
    div_le_iff₀ (by positivity)]
  have e₁ : Dist * (1 + exp t / (Fintype.card D - 1)) =
      Dist + Dist * exp t / (Fintype.card D - 1) := by ring
  have e₂ : ((Fintype.card ι : ℝ) / Dist - 1) * (Fintype.card D - 1) =
      ((Fintype.card ι : ℝ) - Dist) * (Fintype.card D - 1) / Dist := by field_simp
  rw [e₁, e₂, div_le_iff₀' hD, ← le_div_iff₀ hK]
  constructor <;> intro h <;> linarith

end Identifiability

open Identifiability

variable (pX) in
/-- The **privacy–distortion function under differential privacy** `ε*_d(D)` of WYZ, (6): the
infimum of the privacy levels `ε ≥ 0` for which some mechanism is `ε`-DP with expected Hamming
distortion at most `D`, in `EReal` (it is `⊤` when no such mechanism exists). Privacy levels
range over reals rather than `[0, ∞]`. -/
noncomputable def dpPrivacyDistortion (Dist : ℝ) : EReal :=
  sInf {e | ∃ ε : ℝ, (ε : EReal) = e ∧ 0 ≤ ε ∧ ∃ M : Kernel (ι → D) (ι → D), IsMarkovKernel M ∧
    IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε ∧ distortion pX M ≤ Dist}

variable (pX) in
/-- The **privacy–distortion function under identifiability** `ε*_i(D)` of WYZ, (6). -/
noncomputable def idPrivacyDistortion (Dist : ℝ) : EReal :=
  sInf {e | ∃ ε : ℝ, (ε : EReal) = e ∧ 0 ≤ ε ∧ ∃ M : Kernel (ι → D) (ι → D), IsMarkovKernel M ∧
    IsIdentifiable pX M ε ∧ distortion pX M ≤ Dist}

omit [MeasurableSingletonClass D] [IsProbabilityMeasure pX] [IsMarkovKernel M] in
/-- The privacy–distortion function under differential privacy is nonnegative. -/
theorem dpPrivacyDistortion_nonneg (Dist : ℝ) : 0 ≤ dpPrivacyDistortion pX Dist :=
  le_sInf fun _ ⟨_, he, hε, _⟩ ↦ he ▸ EReal.coe_nonneg.2 hε

omit [MeasurableSingletonClass D] [IsProbabilityMeasure pX] [IsMarkovKernel M] in
/-- The privacy–distortion function under identifiability is nonnegative. -/
theorem idPrivacyDistortion_nonneg (Dist : ℝ) : 0 ≤ idPrivacyDistortion pX Dist :=
  le_sInf fun _ ⟨_, he, hε, _⟩ ↦ he ▸ EReal.coe_nonneg.2 hε

omit [IsMarkovKernel M] in
/-- **Wang–Ying–Zhang, Theorem 1, (19)**, upper bound, for finite rows and domain with `m ≥ 2`
and `0 < D < n`: `ε*_d(D) ≤ max {h⁻¹(D), 0}`, for every prior. It is attained by the mechanism
`E_d` (Lemma 5). -/
theorem dpPrivacyDistortion_le_max_invOptDistortion (hm : 2 ≤ Fintype.card D) {Dist : ℝ}
    (hD : 0 < Dist) (hDn : Dist < Fintype.card ι) :
    dpPrivacyDistortion pX Dist ≤ ((max (invOptDistortion ι D Dist) 0 : ℝ) : EReal) := by
  have : Nonempty D := Fintype.card_pos_iff.1 (by omega)
  refine sInf_le ⟨_, rfl, le_max_right _ _, hammingExpMechanism ι D _, inferInstance,
    isEpsDP_hammingExpMechanism (le_max_right _ _), ?_⟩
  rw [distortion_hammingExpMechanism hm, optDistortion_le_iff hm hD hDn]
  exact le_max_left _ _

omit [IsMarkovKernel M] in
/-- **Wang–Ying–Zhang, Theorem 1, (19)**, lower bound, for finite rows and domain with `m ≥ 2`
and `0 < D < n`: `max {h⁻¹(D) - ε_X, 0} ≤ ε*_d(D)`. Here `ε_X` is any bound on the log prior
ratio of neighbouring databases; the least one is the constant (16), finite exactly when the prior
has full support (for other priors the paper's bound is `max {-∞, 0} = 0`, which is
`dpPrivacyDistortion_nonneg`). -/
theorem max_invOptDistortion_sub_le_dpPrivacyDistortion (hm : 2 ≤ Fintype.card D) {Dist : ℝ}
    (hD : 0 < Dist) (hDn : Dist < Fintype.card ι)
    (hX : ∀ ⦃x x' : ι → D⦄, hammingDist x x' = 1 → pX.real {x} ≤ exp εX * pX.real {x'}) :
    ((max (invOptDistortion ι D Dist - εX) 0 : ℝ) : EReal) ≤ dpPrivacyDistortion pX Dist := by
  refine le_sInf ?_
  rintro e ⟨ε, rfl, hε, M, hM, hDP, hdist⟩
  refine EReal.coe_le_coe_iff.2 (max_le ?_ hε)
  have := (hDP.optDistortion_le_distortion hm hX).trans hdist
  rw [optDistortion_le_iff hm hD hDn] at this
  linarith

omit [IsMarkovKernel M] in
/-- **Wang–Ying–Zhang, Theorem 1, (18)**, lower bound `ε*_i(D) ≥ h⁻¹(D)`, for finite rows and
domain with `m ≥ 2` and `0 < D < n`. -/
theorem invOptDistortion_le_idPrivacyDistortion (hm : 2 ≤ Fintype.card D) {Dist : ℝ}
    (hD : 0 < Dist) (hDn : Dist < Fintype.card ι) :
    (invOptDistortion ι D Dist : EReal) ≤ idPrivacyDistortion pX Dist := by
  refine le_sInf ?_
  rintro e ⟨ε, rfl, -, M, hM, hid, hdist⟩
  refine EReal.coe_le_coe_iff.2 ?_
  rw [← optDistortion_le_iff hm hD hDn]
  exact (hid.optDistortion_le_distortion hm).trans hdist

omit [IsProbabilityMeasure pX] [IsMarkovKernel M] in
/-- **Wang–Ying–Zhang, Theorem 1, (18)**, lower bound `ε*_i(D) ≥ ε_X` (via Lemma 3), pairwise:
`log (p_X(x) / p_X(x')) ≤ ε*_i(D)` for all neighbours `x, x'` with `p_X(x') > 0` and every `D`.
Taking the maximum over neighbours gives `ε*_i(D) ≥ ε_X` for a prior with full support. -/
theorem log_div_le_idPrivacyDistortion {x x' : ι → D} (hxx' : hammingDist x x' = 1)
    (hx' : 0 < pX.real {x'}) (Dist : ℝ) :
    (log (pX.real {x} / pX.real {x'}) : EReal) ≤ idPrivacyDistortion pX Dist := by
  refine le_sInf ?_
  rintro e ⟨ε, rfl, hε, M, hM, hid, -⟩
  refine EReal.coe_le_coe_iff.2 ?_
  rcases (measureReal_nonneg : 0 ≤ pX.real {x}).eq_or_lt with h0 | h0
  · rw [← h0, zero_div, log_zero]; exact hε
  rw [log_le_iff_le_exp (div_pos h0 hx'), div_le_iff₀ hx']
  exact hid.measureReal_le hxx'

omit [IsMarkovKernel M] in
/-- **Wang–Ying–Zhang, Theorem 1, (18)**, the lower bound `ε*_i(D) ≥ max {h⁻¹(D), ε_X}`, pairwise
in `ε_X`, for finite rows and domain with `m ≥ 2` and `0 < D < n`: for all neighbours `x, x'`
with `p_X(x') > 0`, `max {h⁻¹(D), log (p_X(x) / p_X(x'))} ≤ ε*_i(D)`. -/
theorem max_invOptDistortion_log_le_idPrivacyDistortion (hm : 2 ≤ Fintype.card D) {Dist : ℝ}
    (hD : 0 < Dist) (hDn : Dist < Fintype.card ι) {x x' : ι → D} (hxx' : hammingDist x x' = 1)
    (hx' : 0 < pX.real {x'}) :
    ((max (invOptDistortion ι D Dist) (log (pX.real {x} / pX.real {x'})) : ℝ) : EReal) ≤
      idPrivacyDistortion pX Dist := by
  rw [EReal.coe_strictMono.monotone.map_max]
  exact max_le (invOptDistortion_le_idPrivacyDistortion hm hD hDn)
    (log_div_le_idPrivacyDistortion hxx' hx' Dist)

end InformationTheory
