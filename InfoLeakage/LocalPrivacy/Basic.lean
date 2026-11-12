/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DPHamming.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Local privacy and strong data processing inequalities

This file formalizes the information-theoretic core of J. C. Duchi, M. I. Jordan and
M. J. Wainwright, *Local privacy, data processing inequalities, and minimax rates*,
[arXiv:1302.3203v4](https://arxiv.org/abs/1302.3203) (2014; conference version *Local privacy and
statistical minimax rates*, FOCS 2013). Result and equation numbers refer to arXiv v4.

A data value `X ∼ P` on a finite alphabet `α` is released through a channel `Q`, with `Q x z` the
probability of the private view `z ∈ β` when the data is `x`. The channel is `ε`-locally
differentially private (`IsLocalDP Q ε`) if `Q(z | x) ≤ e^ε Q(z | x')` for all `x, x', z`. The law
of the private view is `M = Q ∘ P`. Theorem 1 is a strong data processing inequality: local
privacy contracts the symmetrized Kullback–Leibler divergence of the output laws to a multiple of
the squared total variation distance of the input laws. Corollary 1 tensorizes it over `n`
independent samples released through a sequentially interactive channel, and (14) turns it into a
bound on mutual information for Fano's method. Theorem 2 is a variational refinement for a
family `{P_ν}` of input laws, through the unit ball of `ℓ∞`.

Laws are vectors `P : α → ℝ` (with nonnegativity and total mass `1` assumed where needed),
divergences are finite sums in nats, and `‖P₁ - P₂‖_TV = (1/2) ∑ |P₁ x - P₂ x|`, which equals the
paper's `sup_S |P₁(S) - P₂(S)|` (`isGreatest_tvDistSum`).

## Main definitions

* `outputLaw P Q`: the output law `M = Q ∘ P` (the marginalization (3) for one sample).
* `tvDistSum p q`: the total variation distance.
* `klDivSum p q`: the Kullback–Leibler divergence `∑ p log (p / q)`; for probability measures with
  `μ ≪ ν` it agrees with Mathlib's `klDiv` (`klDiv_eq_ofReal_klDivSum`).
* `seqMarginal P Q n`: the law (3) of `Z_{1:n}` for independent `X_i ∼ P i` released through the
  sequentially interactive channel `Q i z_{1:i-1}`.
* `mixture p`: the uniform mixture `|ι|⁻¹ ∑_ν p ν`.
* `mutualInfoUniform M`: the mutual information `I(Z; V)` for `V` uniform and `Z | V = ν ∼ M ν`.

## Main statements

* `klDivSum_add_klDivSum_outputLaw_le_min`: finite-alphabet case of **Theorem 1**, eq. (12):
  `D(M₁ ‖ M₂) + D(M₂ ‖ M₁) ≤ min {4, e^{2ε}} (e^ε - 1)² ‖P₁ - P₂‖²_TV`.
* `klDivSum_add_klDivSum_outputLaw_le`: Theorem 1 with constant `1` instead of `min {4, e^{2ε}}`.
* `klDivSum_add_klDivSum_seqMarginal_le_four`: finite-alphabet case of **Corollary 1**, eq. (13)
  (interactive channels): `D(M^n ‖ M'^n) + D(M'^n ‖ M^n) ≤ 4 (e^ε - 1)² ∑_i ‖P_i - P'_i‖²_TV`.
* `mutualInfoUniform_seqMarginal_le_four`: finite-alphabet case of the **mutual information
  bound** (14).
* `sum_klDivSum_add_klDivSum_mixture_le`: finite-alphabet case of **Theorem 2**, eq. (24):
  `|V|⁻¹ ∑_ν (D(M_ν ‖ M̄) + D(M̄ ‖ M_ν)) ≤ (e^ε - 1)² / |V| sup_{‖γ‖_∞ ≤ 1} ∑_ν φ_ν(γ)²`.

## Correspondence with the paper

* Definitions (1) and (2): `IsLocalDP` (from `InfoLeakage.DPHamming.Basic`), applied to every
  step `Q i h` for (1); agreement with the event form `sup_S Q(S | x) / Q(S | x') ≤ e^ε`:
  `isLocalDP_iff_forall_finset`.
* Total variation (Section 2): `tvDistSum`, `isGreatest_tvDistSum`.
* Theorem 1: `klDivSum_add_klDivSum_outputLaw_le_min`; sharper forms
  `klDivSum_add_klDivSum_outputLaw_le` and the one-sided `klDivSum_outputLaw_le`
  (`D(M₁ ‖ M₂) ≤ (e^ε - 1)² ‖P₁ - P₂‖²_TV`).
* Lemma 3, eq. (49): `abs_outputLaw_sub_le_min`; sharper form (constant `1` instead of
  `min {2, e^ε}`) `abs_outputLaw_sub_le_infProb`; eq. (50): `abs_outputLaw_sub_le`.
* Lemma 4: `log_div_le_abs_sub_div_min`, and `abs_log_div_le_abs_sub_div_min`.
* Mutual absolute continuity of the output laws (proof of Theorem 1): `outputLaw_eq_zero_iff`,
  `seqMarginal_eq_zero_iff`.
* Corollary 1: `klDivSum_add_klDivSum_seqMarginal_le_four`; sharper forms
  `klDivSum_add_klDivSum_seqMarginal_le` (constant `2`) and the one-sided
  `klDivSum_seqMarginal_le` (constant `1`). The chain rule of its proof (Section 7.2):
  `klDivSum_seqMarginal_succ`; the factorization of `M^n`: `seqMarginal_eq_prod`.
* Theorem 2: `sum_klDivSum_add_klDivSum_mixture_le`; sharper form (constant `(e^ε - 1)² / 4`)
  `sum_klDivSum_add_klDivSum_mixture_le_div_four`; key step of its proof (Section 8.1):
  `sum_sq_outputLaw_sub_le`.
* Eq. (14): `mutualInfoUniform_le` (first inequality, convexity), and
  `mutualInfoUniform_seqMarginal_le_four`; sharper form `mutualInfoUniform_seqMarginal_le`.
* Corollary 3, only its mutual information step `I(Z_{1:n}; V) ≤ 4 n ε² κ² δ²` for
  `ε ∈ [0, 22/35]`, not the Fano bound (19): `mutualInfoUniform_seqMarginal_le_four_mul`. It
  assumes the total variation bound `‖P_ν - P_ν'‖²_TV ≤ κ² δ² / 2` that the paper derives from the
  packing condition (17) by Pinsker's inequality, rather than (17) itself; sharper form
  `mutualInfoUniform_seqMarginal_le_two_mul` (`2 n ε² r` for `ε ∈ [0, log 2]`).
* Mathlib's `klDiv`: `klDiv_eq_ofReal_klDivSum`. There is no bridge from `outputLaw`,
  `seqMarginal` or `tvDistSum` to Mathlib's measures, kernels or total variation.

## Remarks on the paper

* The constant `1` in place of `min {2, e^ε}` in Lemma 3 and of `min {4, e^{2ε}}` in Theorem 1
  (`abs_outputLaw_sub_le_infProb`, `klDivSum_add_klDivSum_outputLaw_le`, `klDivSum_outputLaw_le`)
  is an observation that follows in one line from the paper's own bound (50): every
  `Q(z | x) ≤ e^ε inf_x' Q(z | x')`, so
  `sup_x Q(z | x) - inf_x Q(z | x) ≤ (e^ε - 1) inf_x Q(z | x)`, and the rest of the proof of
  Theorem 1 is unchanged. Related bounds: Kairouz, Oh and Viswanath,
  *Extremal mechanisms for local differential privacy* (arXiv:1407.1338), Corollary 9 (constant
  `2 (1 + δ) / (e^ε + 1)` for `ε` small enough, depending on `P₀, P₁, δ`); Duchi and Ruan, *The
  right complexity measure in locally private estimation* (arXiv:1806.05756), Proposition 8
  (strong data processing for the `|t - 1|^k`-divergences); and Asoodeh and Zhang, *Contraction of
  locally differentially private mechanisms* (arXiv:2210.13386), Theorem 2
  (`χ²(M₁ ‖ M₂) ≤ e^{-ε} (e^ε - 1)² min {4 ‖P₁ - P₂‖²_TV, ‖P₁ - P₂‖_TV}`, which, as `D ≤ χ²`,
  beats the one-sided constant `1` for `ε > log 4`). The constant `1` is asymptotically tight as
  `ε → 0`: randomized response on two point masses (`‖P₁ - P₂‖_TV = 1`) gives
  `D(M₁ ‖ M₂) + D(M₂ ‖ M₁) = 2 ε tanh (ε / 2) ∼ (e^ε - 1)²` (a direct computation, not formalized
  here).
* The proof of Corollary 1 (Section 7.2) bounds each one-sided divergence `D(M^n_ν ‖ M^n_ν')`
  through the chain rule and Theorem 1, by `min {4, e^{2ε}} (e^ε - 1)² ∑_i ‖P_{ν,i} - P_{ν',i}‖²_TV`
  (written there with `4`). Because the chain rules for the two directions average over different
  laws of the history, adding the two directions gives only the constant `2 min {4, e^{2ε}}` for
  the symmetrized sum (13), which exceeds the stated `4` exactly when `ε > (log 2) / 2`. The
  statement (13) is nevertheless true: by the one-line observation above, the one-sided bound holds
  with constant `1`, so the symmetrized sum is at most `2 (e^ε - 1)² ∑_i ‖P_{ν,i} - P_{ν',i}‖²_TV`
  (`klDivSum_add_klDivSum_seqMarginal_le`). Nothing downstream is affected: (14), Proposition 1,
  Corollaries 2 and 3, and Proposition 2 use only the one-sided bound, which the paper's proof does
  establish.
* Theorem 2 holds with `(e^ε - 1)² / 4` in place of `(e^ε - 1)²`. This is again an observation on
  the paper's own proof (Section 8.1): centering `Q(z | ·)` at the midpoint of
  `[inf_x Q(z | x), e^ε inf_x Q(z | x)]`, instead of shifting it to `[0, (e^ε - 1) inf_x Q(z | x)]`,
  halves the sup-norm of the resulting `γ`.

## Implementation notes

* Steps are indexed from `0`; the channel at step `i` is `Q i : (Fin i → β) → α → β → ℝ`, a
  function of the history `z_{1:i}` (in `0`-indexing, the first `i` outputs).
* `klDivSum` uses `Real.log` and its convention `log 0 = 0`; it is the true divergence whenever
  the first law is absolutely continuous with respect to the second, which holds for all pairs of
  output laws of a locally private channel.
* The theorems on `seqMarginal` (Corollaries 1 and 3, (14)) assume the hypotheses on the sources
  `P i` and channels `Q i` (and the total variation bounds `hr`, `hP`) for every `i : ℕ`, not only
  for `i < n`. This is harmless: `seqMarginal P Q n` depends only on the entries with `i < n`, so
  the others can be set to any probability vectors and channels satisfying the hypotheses.

## Not formalized

Theorem 3 (the Assouad-type bound), Corollary 4 (tensorization of Theorem 2 for non-interactive
channels), Lemma 1, the minimax parts of Corollaries 2 and 3
(Le Cam and Fano), Pinsker's inequality, and the estimation results (Propositions 1–9). Only
finite alphabets are treated.
-/

@[expose] public section

open Finset Real

namespace InformationTheory

variable {α β : Type*}

/-! ### Definitions -/

section Definitions

variable [Fintype α] [Fintype β]

/-- The law `M = Q ∘ P` of the private view `Z` of `X ∼ P` released through the channel `Q`,
`M(z) = ∑_x P(x) Q(z | x)` (the marginalization (3) of Duchi–Jordan–Wainwright, one sample). -/
noncomputable def outputLaw (P : α → ℝ) (Q : α → β → ℝ) (z : β) : ℝ :=
  ∑ x, P x * Q x z

/-- The total variation distance `‖p - q‖_TV = (1/2) ∑_x |p x - q x|` of two vectors. For
probability vectors this is `sup_S |p(S) - q(S)|`, the normalization of Duchi–Jordan–Wainwright
(see `isGreatest_tvDistSum`). -/
noncomputable def tvDistSum (p q : α → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- The Kullback–Leibler divergence `D(p ‖ q) = ∑_z p z log (p z / q z)` of two vectors on a finite
alphabet, in nats. It is the true divergence of probability vectors when `p ≪ q`; the junk value
`log 0 = 0` is never used below, where the laws are mutually absolutely continuous
(`outputLaw_eq_zero_iff`, `seqMarginal_eq_zero_iff`). -/
noncomputable def klDivSum (p q : β → ℝ) : ℝ :=
  ∑ z, p z * log (p z / q z)

/-- The uniform mixture `|ι|⁻¹ ∑_ν p ν` of a finite family of vectors. -/
noncomputable def mixture {ι γ : Type*} [Fintype ι] (p : ι → γ → ℝ) (z : γ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ ν, p ν z

end Definitions

/-! ### Local differential privacy -/

/-- For a channel with finite output alphabet, the singleton form `IsLocalDP Q ε`
(`Q(z | x) ≤ e^ε Q(z | x')`) agrees with the definition (2) of Duchi–Jordan–Wainwright,
`sup_S sup_{x, x'} Q(S | x) / Q(S | x') ≤ e^ε` over all output events `S`, written without
division. -/
theorem isLocalDP_iff_forall_finset {Q : α → β → ℝ} {ε : ℝ} :
    IsLocalDP Q ε ↔ ∀ x x' (S : Finset β), ∑ z ∈ S, Q x z ≤ exp ε * ∑ z ∈ S, Q x' z := by
  refine ⟨fun h x x' S ↦ ?_, fun h x x' z ↦ by simpa using h x x' {z}⟩
  rw [mul_sum]
  exact sum_le_sum fun z _ ↦ h x x' z

/-- An `ε`-locally differentially private channel has `0 ≤ ε` as soon as some output has positive
probability. -/
lemma IsLocalDP.nonneg_of_pos {Q : α → β → ℝ} {ε : ℝ} (h : IsLocalDP Q ε) {x : α} {z : β}
    (hxz : 0 < Q x z) : 0 ≤ ε := by
  have := h x x z
  rw [← exp_le_exp, exp_zero]
  nlinarith

/-! ### Total variation -/

section TV

variable [Fintype α] {p q : α → ℝ}

lemma two_mul_max_sub_zero (t : ℝ) : 2 * max t 0 = |t| + t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- For vectors of equal total mass, the total variation distance is the sum of the positive
parts of `p - q`. -/
lemma sum_max_sub_zero_eq_tvDistSum (h : ∑ x, p x = ∑ x, q x) :
    ∑ x, max (p x - q x) 0 = tvDistSum p q := by
  have h₀ : ∑ x, (p x - q x) = 0 := by rw [sum_sub_distrib, h, sub_self]
  have : 2 * ∑ x, max (p x - q x) 0 = ∑ x, |p x - q x| := by
    rw [mul_sum]
    simp_rw [two_mul_max_sub_zero]
    rw [sum_add_distrib, h₀, add_zero]
  rw [tvDistSum]
  linarith

lemma tvDistSum_comm : tvDistSum p q = tvDistSum q p := by
  simp_rw [tvDistSum, abs_sub_comm]

lemma tvDistSum_nonneg : 0 ≤ tvDistSum p q := by
  unfold tvDistSum
  positivity

/-- Every event `S` has `|p(S) - q(S)| ≤ ‖p - q‖_TV` for vectors of equal total mass. -/
theorem abs_sum_sub_sum_le_tvDistSum (h : ∑ x, p x = ∑ x, q x) (S : Finset α) :
    |∑ x ∈ S, p x - ∑ x ∈ S, q x| ≤ tvDistSum p q := by
  have key : ∀ {p q : α → ℝ}, ∑ x, p x = ∑ x, q x →
      ∑ x ∈ S, p x - ∑ x ∈ S, q x ≤ tvDistSum p q := by
    intro p q h
    rw [← sum_max_sub_zero_eq_tvDistSum h, ← sum_sub_distrib]
    calc ∑ x ∈ S, (p x - q x) ≤ ∑ x ∈ S, max (p x - q x) 0 :=
          sum_le_sum fun x _ ↦ le_max_left _ _
      _ ≤ ∑ x, max (p x - q x) 0 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S) fun x _ _ ↦ le_max_right _ _
  rw [abs_le]
  refine ⟨?_, key h⟩
  have := key h.symm
  rw [tvDistSum_comm] at this
  linarith

/-- The event `{p > q}` attains the total variation distance. -/
theorem sum_filter_lt_sub_eq_tvDistSum (h : ∑ x, p x = ∑ x, q x) :
    ∑ x with q x < p x, p x - ∑ x with q x < p x, q x = tvDistSum p q := by
  rw [← sum_max_sub_zero_eq_tvDistSum h, ← sum_sub_distrib, sum_filter]
  refine sum_congr rfl fun x _ ↦ ?_
  split_ifs with hx
  · rw [max_eq_left (sub_nonneg.2 hx.le)]
  · rw [max_eq_right (sub_nonpos.2 (not_lt.1 hx))]

/-- **Total variation distance** (Section 2 of Duchi–Jordan–Wainwright): for vectors of equal total
mass (in particular probability vectors), `‖p - q‖_TV = sup_S |p(S) - q(S)|`, the supremum being
attained. -/
theorem isGreatest_tvDistSum (h : ∑ x, p x = ∑ x, q x) :
    IsGreatest {t | ∃ S : Finset α, t = |∑ x ∈ S, p x - ∑ x ∈ S, q x|} (tvDistSum p q) := by
  refine ⟨⟨univ.filter fun x ↦ q x < p x, ?_⟩, ?_⟩
  · rw [sum_filter_lt_sub_eq_tvDistSum h, abs_of_nonneg tvDistSum_nonneg]
  · rintro _ ⟨S, rfl⟩
    exact abs_sum_sub_sum_le_tvDistSum h S

end TV

/-! ### The two lemmas of the proof of Theorem 1 -/

section Lemmas

variable [Fintype α] {P₁ P₂ : α → ℝ} {Q : α → β → ℝ} {ε : ℝ}

/-- For input vectors of equal total mass, `M₁(z) - M₂(z) = ∑_x (P₁ x - P₂ x) (Q(z | x) - c)` for
every constant `c`. -/
lemma outputLaw_sub_outputLaw_eq (h : ∑ x, P₁ x = ∑ x, P₂ x) (z : β) (c : ℝ) :
    outputLaw P₁ Q z - outputLaw P₂ Q z = ∑ x, (P₁ x - P₂ x) * (Q x z - c) := by
  have h₀ : ∑ x, (P₁ x - P₂ x) = 0 := by rw [sum_sub_distrib, h, sub_self]
  have : ∑ x, (P₁ x - P₂ x) * (Q x z - c) =
      ∑ x, (P₁ x - P₂ x) * Q x z - (∑ x, (P₁ x - P₂ x)) * c := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ ↦ by ring
  rw [this, h₀, zero_mul, sub_zero, outputLaw, outputLaw, ← sum_sub_distrib]
  exact sum_congr rfl fun x _ ↦ by ring

/-- Bound (50) of Duchi–Jordan–Wainwright: if `a ≤ Q(z | x) ≤ b` for all inputs `x`, then
`|M₁(z) - M₂(z)| ≤ (b - a) ‖P₁ - P₂‖_TV` for input vectors of equal total mass. -/
theorem abs_outputLaw_sub_le (h : ∑ x, P₁ x = ∑ x, P₂ x) {z : β} {a b : ℝ}
    (ha : ∀ x, a ≤ Q x z) (hb : ∀ x, Q x z ≤ b) :
    |outputLaw P₁ Q z - outputLaw P₂ Q z| ≤ (b - a) * tvDistSum P₁ P₂ := by
  set c := (a + b) / 2 with hc_def
  have hc := outputLaw_sub_outputLaw_eq (Q := Q) h z c
  rw [hc]
  calc |∑ x, (P₁ x - P₂ x) * (Q x z - c)| ≤ ∑ x, |P₁ x - P₂ x| * ((b - a) / 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
        rw [abs_mul]
        have : |Q x z - c| ≤ (b - a) / 2 :=
          abs_le.2 ⟨by linarith [ha x, hc_def], by linarith [hb x, hc_def]⟩
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = (b - a) * tvDistSum P₁ P₂ := by rw [← sum_mul, tvDistSum]; ring

variable [Nonempty α]

/-- The smallest probability `inf_x Q(z | x)` of the output `z` under the channel `Q`. -/
noncomputable def infProb (Q : α → β → ℝ) (z : β) : ℝ :=
  univ.inf' univ_nonempty fun x ↦ Q x z

lemma infProb_le (Q : α → β → ℝ) (x : α) (z : β) : infProb Q z ≤ Q x z :=
  inf'_le _ (mem_univ x)

lemma infProb_nonneg (hQ₀ : ∀ x z, 0 ≤ Q x z) (z : β) : 0 ≤ infProb Q z :=
  le_inf' _ _ fun x _ ↦ hQ₀ x z

/-- Under `ε`-local differential privacy every output probability is within a factor `e^ε` of the
smallest one: `Q(z | x) ≤ e^ε inf_x' Q(z | x')`. -/
lemma IsLocalDP.le_exp_mul_infProb (hQ : IsLocalDP Q ε) (x : α) (z : β) :
    Q x z ≤ exp ε * infProb Q z := by
  obtain ⟨x', -, hx'⟩ := exists_mem_eq_inf' (univ_nonempty (α := α)) fun x ↦ Q x z
  rw [infProb, hx']
  exact hQ x x' z

omit [Nonempty α] in
/-- The output law of a probability vector through a channel is a probability vector. -/
lemma sum_outputLaw [Fintype β] {P : α → ℝ} (hQ₁ : ∀ x, ∑ z, Q x z = 1) (hP₁ : ∑ x, P x = 1) :
    ∑ z, outputLaw P Q z = 1 := by
  simp_rw [outputLaw]
  rw [sum_comm]
  simp_rw [← mul_sum, hQ₁, mul_one, hP₁]

lemma infProb_le_outputLaw {P : α → ℝ} (hP₀ : ∀ x, 0 ≤ P x) (hP₁ : ∑ x, P x = 1) (z : β) :
    infProb Q z ≤ outputLaw P Q z :=
  calc infProb Q z = ∑ x, P x * infProb Q z := by rw [← sum_mul, hP₁, one_mul]
    _ ≤ outputLaw P Q z := sum_le_sum fun x _ ↦
      mul_le_mul_of_nonneg_left (infProb_le Q x z) (hP₀ x)

lemma outputLaw_le_exp_mul_infProb (hQ : IsLocalDP Q ε) {P : α → ℝ} (hP₀ : ∀ x, 0 ≤ P x)
    (hP₁ : ∑ x, P x = 1) (z : β) : outputLaw P Q z ≤ exp ε * infProb Q z :=
  calc outputLaw P Q z ≤ ∑ x, P x * (exp ε * infProb Q z) := sum_le_sum fun x _ ↦
        mul_le_mul_of_nonneg_left (hQ.le_exp_mul_infProb x z) (hP₀ x)
    _ = exp ε * infProb Q z := by rw [← sum_mul, hP₁, one_mul]

/-- Under local differential privacy an output has probability zero under one input law iff it has
probability zero under every input law: the output laws are mutually absolutely continuous (first
line of the proof of Theorem 1 of Duchi–Jordan–Wainwright). -/
lemma outputLaw_eq_zero_iff (hQ₀ : ∀ x z, 0 ≤ Q x z) (hQ : IsLocalDP Q ε) {P : α → ℝ}
    (hP₀ : ∀ x, 0 ≤ P x) (hP₁ : ∑ x, P x = 1) (z : β) :
    outputLaw P Q z = 0 ↔ infProb Q z = 0 := by
  have h₁ := infProb_le_outputLaw (Q := Q) hP₀ hP₁ z
  have h₂ := outputLaw_le_exp_mul_infProb hQ hP₀ hP₁ z
  have h₀ := infProb_nonneg hQ₀ z
  constructor
  · intro h; linarith
  · intro h; rw [h, mul_zero] at h₂; linarith

/-- **Lemma 3** of Duchi–Jordan–Wainwright, in a sharper form: for an `ε`-locally differentially
private channel and input vectors of equal total mass,
`|M₁(z) - M₂(z)| ≤ (e^ε - 1) inf_x Q(z | x) ‖P₁ - P₂‖_TV`.
The paper has the extra factor `c_ε = min {2, e^ε} ≥ 1` (see `abs_outputLaw_sub_le_min`). -/
theorem abs_outputLaw_sub_le_infProb (hQ : IsLocalDP Q ε) (h : ∑ x, P₁ x = ∑ x, P₂ x) (z : β) :
    |outputLaw P₁ Q z - outputLaw P₂ Q z| ≤ (exp ε - 1) * infProb Q z * tvDistSum P₁ P₂ := by
  have := abs_outputLaw_sub_le h (infProb_le Q · z) (hQ.le_exp_mul_infProb · z)
  rwa [← sub_one_mul] at this

/-- Finite-alphabet case of **Lemma 3** of Duchi–Jordan–Wainwright (eq. (49)): for an `ε`-locally
differentially private channel with `ε ≥ 0` and input vectors of equal total mass,
`|M₁(z) - M₂(z)| ≤ c_ε inf_x Q(z | x) (e^ε - 1) ‖P₁ - P₂‖_TV` with `c_ε = min {2, e^ε}`. -/
theorem abs_outputLaw_sub_le_min (hQ₀ : ∀ x z, 0 ≤ Q x z) (hQ : IsLocalDP Q ε) (hε : 0 ≤ ε)
    (h : ∑ x, P₁ x = ∑ x, P₂ x) (z : β) :
    |outputLaw P₁ Q z - outputLaw P₂ Q z| ≤
      min 2 (exp ε) * infProb Q z * (exp ε - 1) * tvDistSum P₁ P₂ := by
  have h₁ : 1 ≤ min 2 (exp ε) := le_min one_le_two (one_le_exp hε)
  have h₂ : 0 ≤ (exp ε - 1) * infProb Q z * tvDistSum P₁ P₂ :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 (one_le_exp hε)) (infProb_nonneg hQ₀ z))
      tvDistSum_nonneg
  calc |outputLaw P₁ Q z - outputLaw P₂ Q z| ≤ (exp ε - 1) * infProb Q z * tvDistSum P₁ P₂ :=
        abs_outputLaw_sub_le_infProb hQ h z
    _ ≤ min 2 (exp ε) * ((exp ε - 1) * infProb Q z * tvDistSum P₁ P₂) := le_mul_of_one_le_left h₂ h₁
    _ = min 2 (exp ε) * infProb Q z * (exp ε - 1) * tvDistSum P₁ P₂ := by ring

end Lemmas

/-- **Lemma 4** of Duchi–Jordan–Wainwright, in absolute value: for `a, b > 0`,
`|log (a / b)| ≤ |a - b| / min {a, b}`. -/
theorem abs_log_div_le_abs_sub_div_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |log (a / b)| ≤ |a - b| / min a b := by
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (log_nonneg ((one_le_div hb).2 hab)), min_eq_right hab,
      abs_of_nonneg (sub_nonneg.2 hab), sub_div, div_self hb.ne']
    exact log_le_sub_one_of_pos (div_pos ha hb)
  · rw [abs_of_nonpos (log_nonpos (div_nonneg ha.le hb.le) ((div_le_one hb).2 hab)),
      min_eq_left hab, abs_of_nonpos (sub_nonpos.2 hab), neg_sub, sub_div, div_self ha.ne',
      ← log_inv, inv_div]
    exact log_le_sub_one_of_pos (div_pos hb ha)

/-- **Lemma 4** of Duchi–Jordan–Wainwright: for `a, b > 0`, `log (a / b) ≤ |a - b| / min {a, b}`. -/
theorem log_div_le_abs_sub_div_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    log (a / b) ≤ |a - b| / min a b :=
  (le_abs_self _).trans (abs_log_div_le_abs_sub_div_min ha hb)

/-! ### Theorem 1: the strong data processing inequality -/

section Theorem1

/-- Pointwise step of the proof of Theorem 1: if `0 ≤ a ≤ min {m₁, m₂}` and `|m₁ - m₂| ≤ c a`, then
`(m₁ - m₂) log (m₁ / m₂) ≤ c² a`. -/
lemma sub_mul_log_div_le {m₁ m₂ a c : ℝ} (ha : 0 ≤ a) (h₁ : a ≤ m₁) (h₂ : a ≤ m₂)
    (h : |m₁ - m₂| ≤ c * a) : (m₁ - m₂) * log (m₁ / m₂) ≤ c ^ 2 * a := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [mul_zero, abs_nonpos_iff, sub_eq_zero] at h
    simp [h]
  have hd := abs_nonneg (m₁ - m₂)
  calc (m₁ - m₂) * log (m₁ / m₂) ≤ |m₁ - m₂| * |log (m₁ / m₂)| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |m₁ - m₂| * (|m₁ - m₂| / a) := by
        refine mul_le_mul_of_nonneg_left ?_ hd
        exact (abs_log_div_le_abs_sub_div_min (ha.trans_le h₁) (ha.trans_le h₂)).trans
          (div_le_div_of_nonneg_left hd ha (le_min h₁ h₂))
    _ = |m₁ - m₂| ^ 2 / a := by ring
    _ ≤ (c * a) ^ 2 / a := by gcongr
    _ = c ^ 2 * a := by field_simp

/-- Pointwise step of the one-sided bound: if `0 ≤ a ≤ min {m₁, m₂}` and `|m₁ - m₂| ≤ c a`, then
`m₁ log (m₁ / m₂) ≤ (m₁ - m₂) + c² a`. -/
lemma mul_log_div_le {m₁ m₂ a c : ℝ} (ha : 0 ≤ a) (h₁ : a ≤ m₁) (h₂ : a ≤ m₂)
    (h : |m₁ - m₂| ≤ c * a) : m₁ * log (m₁ / m₂) ≤ (m₁ - m₂) + c ^ 2 * a := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [mul_zero, abs_nonpos_iff, sub_eq_zero] at h
    subst h
    rcases eq_or_ne m₁ 0 with h | h <;> simp [*]
  have hm₁ := ha.trans_le h₁
  have hm₂ := ha.trans_le h₂
  calc m₁ * log (m₁ / m₂) ≤ m₁ * (m₁ / m₂ - 1) :=
        mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hm₁ hm₂)) hm₁.le
    _ = (m₁ - m₂) + |m₁ - m₂| ^ 2 / m₂ := by rw [sq_abs]; field_simp; ring
    _ ≤ (m₁ - m₂) + |m₁ - m₂| ^ 2 / a := by gcongr
    _ ≤ (m₁ - m₂) + (c * a) ^ 2 / a := by gcongr
    _ = (m₁ - m₂) + c ^ 2 * a := by field_simp

/-- The symmetrized divergence is `∑_z (p z - q z) log (p z / q z)`. -/
lemma klDivSum_add_klDivSum [Fintype β] (p q : β → ℝ) :
    klDivSum p q + klDivSum q p = ∑ z, (p z - q z) * log (p z / q z) := by
  rw [klDivSum, klDivSum, ← sum_add_distrib]
  refine sum_congr rfl fun z _ ↦ ?_
  rw [← inv_div, log_inv]
  ring

variable [Fintype α] [Fintype β] {P₁ P₂ : α → ℝ} {Q : α → β → ℝ} {ε : ℝ}

omit [Fintype β] in
lemma nonempty_of_sum_eq_one {P : α → ℝ} (hP₁ : ∑ x, P x = 1) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  simp at hP₁

/-- The smallest output probabilities of a channel sum to at most one. -/
lemma sum_infProb_le_one [Nonempty α] (hQ₁ : ∀ x, ∑ z, Q x z = 1) : ∑ z, infProb Q z ≤ 1 := by
  obtain ⟨x⟩ := ‹Nonempty α›
  calc ∑ z, infProb Q z ≤ ∑ z, Q x z := sum_le_sum fun z _ ↦ infProb_le Q x z
    _ = 1 := hQ₁ x

/-- **Theorem 1** of Duchi–Jordan–Wainwright (strong data processing inequality), in a sharper
form: if the channel `Q` is `ε`-locally differentially private, then for all input laws `P₁, P₂`
the output laws `M_j = Q ∘ P_j` satisfy
`D(M₁ ‖ M₂) + D(M₂ ‖ M₁) ≤ (e^ε - 1)² ‖P₁ - P₂‖²_TV`.
The constant `min {4, e^{2ε}}` of the paper is replaced by `1`
(the paper's form is `klDivSum_add_klDivSum_outputLaw_le_min`). -/
theorem klDivSum_add_klDivSum_outputLaw_le (hQ₀ : ∀ x z, 0 ≤ Q x z) (hQ₁ : ∀ x, ∑ z, Q x z = 1)
    (hQ : IsLocalDP Q ε) (hP₁₀ : ∀ x, 0 ≤ P₁ x) (hP₁₁ : ∑ x, P₁ x = 1) (hP₂₀ : ∀ x, 0 ≤ P₂ x)
    (hP₂₁ : ∑ x, P₂ x = 1) :
    klDivSum (outputLaw P₁ Q) (outputLaw P₂ Q) + klDivSum (outputLaw P₂ Q) (outputLaw P₁ Q) ≤
      (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 := by
  have := nonempty_of_sum_eq_one hP₁₁
  rw [klDivSum_add_klDivSum]
  calc ∑ z, (outputLaw P₁ Q z - outputLaw P₂ Q z) * log (outputLaw P₁ Q z / outputLaw P₂ Q z)
      ≤ ∑ z, ((exp ε - 1) * tvDistSum P₁ P₂) ^ 2 * infProb Q z := sum_le_sum fun z _ ↦ by
        refine sub_mul_log_div_le (infProb_nonneg hQ₀ z) (infProb_le_outputLaw hP₁₀ hP₁₁ z)
          (infProb_le_outputLaw hP₂₀ hP₂₁ z) ?_
        have := abs_outputLaw_sub_le_infProb hQ (hP₁₁.trans hP₂₁.symm) z
        linarith
    _ ≤ ((exp ε - 1) * tvDistSum P₁ P₂) ^ 2 * 1 := by
        rw [← mul_sum]; gcongr; exact sum_infProb_le_one hQ₁
    _ = (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 := by ring

/-- Finite-alphabet case of **Theorem 1** of Duchi–Jordan–Wainwright, eq. (12): if the channel
`Q` is `ε`-locally differentially private (`ε ≥ 0` is then automatic), then for all input laws
`P₁, P₂` the output laws `M_j = Q ∘ P_j` satisfy
`D(M₁ ‖ M₂) + D(M₂ ‖ M₁) ≤ min {4, e^{2ε}} (e^ε - 1)² ‖P₁ - P₂‖²_TV`. -/
theorem klDivSum_add_klDivSum_outputLaw_le_min (hQ₀ : ∀ x z, 0 ≤ Q x z)
    (hQ₁ : ∀ x, ∑ z, Q x z = 1) (hQ : IsLocalDP Q ε) (hP₁₀ : ∀ x, 0 ≤ P₁ x)
    (hP₁₁ : ∑ x, P₁ x = 1) (hP₂₀ : ∀ x, 0 ≤ P₂ x) (hP₂₁ : ∑ x, P₂ x = 1) :
    klDivSum (outputLaw P₁ Q) (outputLaw P₂ Q) + klDivSum (outputLaw P₂ Q) (outputLaw P₁ Q) ≤
      min 4 (exp (2 * ε)) * (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 := by
  obtain ⟨x⟩ := nonempty_of_sum_eq_one hP₁₁
  obtain ⟨z, hz⟩ : ∃ z, Q x z ≠ 0 := by
    by_contra! h
    have := hQ₁ x
    simp [h] at this
  have hε : 0 ≤ ε := hQ.nonneg_of_pos ((hQ₀ x z).lt_of_ne' hz)
  have h₁ : 1 ≤ min 4 (exp (2 * ε)) := le_min (by norm_num) (one_le_exp (by linarith))
  calc _ ≤ (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 :=
        klDivSum_add_klDivSum_outputLaw_le hQ₀ hQ₁ hQ hP₁₀ hP₁₁ hP₂₀ hP₂₁
    _ ≤ min 4 (exp (2 * ε)) * ((exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2) :=
        le_mul_of_one_le_left (by positivity) h₁
    _ = min 4 (exp (2 * ε)) * (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 := by ring

/-- **One-sided Theorem 1**: under the hypotheses of Theorem 1 of Duchi–Jordan–Wainwright, already
the single divergence satisfies `D(M₁ ‖ M₂) ≤ (e^ε - 1)² ‖P₁ - P₂‖²_TV`. This is the form used in
the chain-rule proof of Corollary 1 (`klDivSum_seqMarginal_le`). -/
theorem klDivSum_outputLaw_le (hQ₀ : ∀ x z, 0 ≤ Q x z) (hQ₁ : ∀ x, ∑ z, Q x z = 1)
    (hQ : IsLocalDP Q ε) (hP₁₀ : ∀ x, 0 ≤ P₁ x) (hP₁₁ : ∑ x, P₁ x = 1) (hP₂₀ : ∀ x, 0 ≤ P₂ x)
    (hP₂₁ : ∑ x, P₂ x = 1) :
    klDivSum (outputLaw P₁ Q) (outputLaw P₂ Q) ≤ (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 := by
  have := nonempty_of_sum_eq_one hP₁₁
  calc klDivSum (outputLaw P₁ Q) (outputLaw P₂ Q)
      ≤ ∑ z, ((outputLaw P₁ Q z - outputLaw P₂ Q z) +
          ((exp ε - 1) * tvDistSum P₁ P₂) ^ 2 * infProb Q z) := sum_le_sum fun z _ ↦ by
        refine mul_log_div_le (infProb_nonneg hQ₀ z) (infProb_le_outputLaw hP₁₀ hP₁₁ z)
          (infProb_le_outputLaw hP₂₀ hP₂₁ z) ?_
        have := abs_outputLaw_sub_le_infProb hQ (hP₁₁.trans hP₂₁.symm) z
        linarith
    _ ≤ 0 + ((exp ε - 1) * tvDistSum P₁ P₂) ^ 2 * 1 := by
        rw [sum_add_distrib, sum_sub_distrib, sum_outputLaw hQ₁ hP₁₁, sum_outputLaw hQ₁ hP₂₁,
          sub_self, ← mul_sum]
        gcongr
        exact sum_infProb_le_one hQ₁
    _ = (exp ε - 1) ^ 2 * tvDistSum P₁ P₂ ^ 2 := by ring

end Theorem1

/-! ### Theorem 2: the variational mutual information bound -/

section Theorem2

variable {ι : Type*} [Fintype ι] [Fintype α] [Fintype β] {P : ι → α → ℝ} {Q : α → β → ℝ}
  {ε : ℝ}

omit [Fintype α] in
lemma sq_sum_mul_le_sq_sum_abs {γ d : α → ℝ} [Fintype α] (hγ : ∀ x, |γ x| ≤ 1) :
    (∑ x, γ x * d x) ^ 2 ≤ (∑ x, |d x|) ^ 2 := by
  rw [← sq_abs]
  refine pow_le_pow_left₀ (abs_nonneg _)
    ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)) 2
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hγ x)

omit [Fintype α] in
/-- The supremum over the unit ball `B∞` of `ℓ∞` in Theorem 2 is over a bounded set. -/
lemma bddAbove_range_sum_sq [Fintype α] (d : ι → α → ℝ) :
    BddAbove (Set.range fun γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1} ↦
      ∑ ν, (∑ x, γ.1 x * d ν x) ^ 2) :=
  ⟨∑ ν, (∑ x, |d ν x|) ^ 2, by
    rintro _ ⟨γ, rfl⟩
    exact sum_le_sum fun ν _ ↦ sq_sum_mul_le_sq_sum_abs γ.2⟩

omit [Fintype α] in
lemma iSup_sum_sq_nonneg [Fintype α] (d : ι → α → ℝ) :
    0 ≤ ⨆ γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1}, ∑ ν, (∑ x, γ.1 x * d ν x) ^ 2 :=
  le_ciSup_of_le (bddAbove_range_sum_sq d) ⟨fun _ ↦ 0, fun _ ↦ by norm_num⟩
    (sum_nonneg fun _ _ ↦ sq_nonneg _)

omit [Fintype β] in
/-- The mixture of the output laws is the output law of the mixture. -/
lemma mixture_outputLaw : mixture (fun ν ↦ outputLaw (P ν) Q) = outputLaw (mixture P) Q := by
  ext z
  simp_rw [mixture, outputLaw, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [mixture, mul_sum, sum_mul]
  exact sum_congr rfl fun ν _ ↦ by ring

omit [Fintype β] in
lemma sum_mixture [Nonempty ι] (hP₁ : ∀ ν, ∑ x, P ν x = 1) : ∑ x, mixture P x = 1 := by
  simp_rw [mixture, ← mul_sum]
  rw [sum_comm]
  simp_rw [hP₁, sum_const, card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

omit [Fintype α] [Fintype β] in
lemma mixture_nonneg (hP₀ : ∀ ν x, 0 ≤ P ν x) (x : α) : 0 ≤ mixture P x :=
  mul_nonneg (by positivity) (sum_nonneg fun ν _ ↦ hP₀ ν x)

omit [Fintype β] in
/-- Key step of the proof of Theorem 2: for each output `z`,
`∑_ν (M_ν(z) - M̄(z))² ≤ ((e^ε - 1) inf_x Q(z | x) / 2)² sup_{γ ∈ B∞} ∑_ν φ_ν(γ)²`. -/
lemma sum_sq_outputLaw_sub_le [Nonempty ι] [Nonempty α] (hQ : IsLocalDP Q ε)
    (hP₁ : ∀ ν, ∑ x, P ν x = 1) (z : β) :
    ∑ ν, (outputLaw (P ν) Q z - outputLaw (mixture P) Q z) ^ 2 ≤
      ((exp ε - 1) * infProb Q z / 2) ^ 2 * ⨆ γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1},
        ∑ ν, (∑ x, γ.1 x * (P ν x - mixture P x)) ^ 2 := by
  set a := infProb Q z with ha
  set h := (exp ε - 1) * a / 2 with hh
  set c := (a + exp ε * a) / 2 with hc
  have hQc : ∀ x, |Q x z - c| ≤ h := fun x ↦ by
    have h₁ := infProb_le Q x z
    have h₂ := hQ.le_exp_mul_infProb x z
    rw [← ha] at h₁ h₂
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hdiff : ∀ ν, outputLaw (P ν) Q z - outputLaw (mixture P) Q z =
      ∑ x, (P ν x - mixture P x) * (Q x z - c) := fun ν ↦
    outputLaw_sub_outputLaw_eq ((hP₁ ν).trans (sum_mixture hP₁).symm) z c
  rcases (abs_nonneg _ |>.trans (hQc (Classical.arbitrary α))).eq_or_lt with hh | hh
  · -- `h = 0`: the output probability `Q(z | x)` does not depend on `x`.
    have hQc' : ∀ x, Q x z - c = 0 := fun x ↦ abs_nonpos_iff.1 (hh ▸ hQc x)
    simp [hdiff, hQc', ← hh]
  set γ : α → ℝ := fun x ↦ (Q x z - c) / h
  have hγ : ∀ x, |γ x| ≤ 1 := fun x ↦ by
    rw [abs_div, abs_of_pos hh, div_le_one hh]
    exact hQc x
  calc ∑ ν, (outputLaw (P ν) Q z - outputLaw (mixture P) Q z) ^ 2
      = h ^ 2 * ∑ ν, (∑ x, γ x * (P ν x - mixture P x)) ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun ν _ ↦ ?_
        rw [hdiff, ← mul_pow, mul_sum]
        congr 1
        refine sum_congr rfl fun x _ ↦ ?_
        simp only [γ]
        field_simp
    _ ≤ h ^ 2 * ⨆ γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1},
          ∑ ν, (∑ x, γ.1 x * (P ν x - mixture P x)) ^ 2 := by
        gcongr
        exact le_ciSup (bddAbove_range_sum_sq fun ν x ↦ P ν x - mixture P x) ⟨γ, hγ⟩

/-- **Theorem 2** of Duchi–Jordan–Wainwright, eq. (24), in a sharper form: if the channel `Q` is
`ε`-locally differentially private, `{P_ν}` is a finite family of input laws with mixture
`P̄ = |V|⁻¹ ∑_ν P_ν`, and `M_ν = Q ∘ P_ν`, `M̄ = |V|⁻¹ ∑_ν M_ν`, then
`|V|⁻¹ ∑_ν (D(M_ν ‖ M̄) + D(M̄ ‖ M_ν)) ≤ (e^ε - 1)² / (4 |V|) sup_{γ ∈ B∞} ∑_ν φ_ν(γ)²`,
where `B∞ = {γ : ‖γ‖_∞ ≤ 1}` and `φ_ν(γ) = ∑_x γ(x) (P_ν(x) - P̄(x))`. The paper has the constant
`(e^ε - 1)² / |V|` (see `sum_klDivSum_add_klDivSum_mixture_le`). -/
theorem sum_klDivSum_add_klDivSum_mixture_le_div_four [Nonempty ι] (hQ₀ : ∀ x z, 0 ≤ Q x z)
    (hQ₁ : ∀ x, ∑ z, Q x z = 1) (hQ : IsLocalDP Q ε) (hP₀ : ∀ ν x, 0 ≤ P ν x)
    (hP₁ : ∀ ν, ∑ x, P ν x = 1) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ ν,
        (klDivSum (outputLaw (P ν) Q) (mixture fun ν ↦ outputLaw (P ν) Q) +
          klDivSum (mixture fun ν ↦ outputLaw (P ν) Q) (outputLaw (P ν) Q)) ≤
      (exp ε - 1) ^ 2 / 4 / Fintype.card ι * ⨆ γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1},
        ∑ ν, (∑ x, γ.1 x * (P ν x - mixture P x)) ^ 2 := by
  have : Nonempty α := nonempty_of_sum_eq_one (hP₁ (Classical.arbitrary ι))
  set S := ⨆ γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1}, ∑ ν, (∑ x, γ.1 x * (P ν x - mixture P x)) ^ 2
  have hS : 0 ≤ S := iSup_sum_sq_nonneg _
  have hmix₁ := sum_mixture hP₁
  have hmix₀ := mixture_nonneg hP₀
  rw [mixture_outputLaw]
  simp_rw [klDivSum_add_klDivSum]
  rw [sum_comm]
  have key : ∀ z, ∑ ν, (outputLaw (P ν) Q z - outputLaw (mixture P) Q z) *
      log (outputLaw (P ν) Q z / outputLaw (mixture P) Q z) ≤
        (exp ε - 1) ^ 2 / 4 * S * infProb Q z := fun z ↦ by
    set a := infProb Q z with ha_def
    rcases (infProb_nonneg hQ₀ z).eq_or_lt with ha | ha
    · have h₀ : ∀ ν, outputLaw (P ν) Q z = 0 := fun ν ↦
        (outputLaw_eq_zero_iff hQ₀ hQ (hP₀ ν) (hP₁ ν) z).2 ha.symm
      have h₁ : outputLaw (mixture P) Q z = 0 :=
        (outputLaw_eq_zero_iff hQ₀ hQ hmix₀ hmix₁ z).2 ha.symm
      simp [h₀, h₁, ha_def, ← ha]
    calc ∑ ν, (outputLaw (P ν) Q z - outputLaw (mixture P) Q z) *
          log (outputLaw (P ν) Q z / outputLaw (mixture P) Q z)
        ≤ ∑ ν, (|outputLaw (P ν) Q z - outputLaw (mixture P) Q z| / a) ^ 2 * a :=
          sum_le_sum fun ν _ ↦ sub_mul_log_div_le ha.le (infProb_le_outputLaw (hP₀ ν) (hP₁ ν) z)
            (infProb_le_outputLaw hmix₀ hmix₁ z) (div_mul_cancel₀ _ ha.ne').ge
      _ = (∑ ν, (outputLaw (P ν) Q z - outputLaw (mixture P) Q z) ^ 2) / a := by
          rw [sum_div]
          refine sum_congr rfl fun ν _ ↦ ?_
          rw [div_pow, sq_abs]
          field_simp
      _ ≤ (((exp ε - 1) * a / 2) ^ 2 * S) / a := by
          gcongr
          exact sum_sq_outputLaw_sub_le hQ hP₁ z
      _ = (exp ε - 1) ^ 2 / 4 * S * a := by
          field_simp
          ring
  calc (Fintype.card ι : ℝ)⁻¹ * ∑ z, ∑ ν, (outputLaw (P ν) Q z - outputLaw (mixture P) Q z) *
        log (outputLaw (P ν) Q z / outputLaw (mixture P) Q z)
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ z, (exp ε - 1) ^ 2 / 4 * S * infProb Q z := by
        gcongr with z
        exact key z
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ((exp ε - 1) ^ 2 / 4 * S * 1) := by
        rw [← mul_sum]
        gcongr
        exact sum_infProb_le_one hQ₁
    _ = (exp ε - 1) ^ 2 / 4 / Fintype.card ι * S := by ring

/-- Finite-alphabet case of **Theorem 2** of Duchi–Jordan–Wainwright, eq. (24): if the channel
`Q` is `ε`-locally differentially private, `{P_ν}` is a finite family of input laws with mixture
`P̄ = |V|⁻¹ ∑_ν P_ν`, and `M_ν = Q ∘ P_ν`, `M̄ = |V|⁻¹ ∑_ν M_ν`, then
`|V|⁻¹ ∑_ν (D(M_ν ‖ M̄) + D(M̄ ‖ M_ν)) ≤ (e^ε - 1)² / |V| sup_{γ ∈ B∞} ∑_ν φ_ν(γ)²`,
where `B∞ = {γ : ‖γ‖_∞ ≤ 1}` and `φ_ν(γ) = ∑_x γ(x) (P_ν(x) - P̄(x))`. -/
theorem sum_klDivSum_add_klDivSum_mixture_le [Nonempty ι] (hQ₀ : ∀ x z, 0 ≤ Q x z)
    (hQ₁ : ∀ x, ∑ z, Q x z = 1) (hQ : IsLocalDP Q ε) (hP₀ : ∀ ν x, 0 ≤ P ν x)
    (hP₁ : ∀ ν, ∑ x, P ν x = 1) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ ν,
        (klDivSum (outputLaw (P ν) Q) (mixture fun ν ↦ outputLaw (P ν) Q) +
          klDivSum (mixture fun ν ↦ outputLaw (P ν) Q) (outputLaw (P ν) Q)) ≤
      (exp ε - 1) ^ 2 / Fintype.card ι * ⨆ γ : {γ : α → ℝ // ∀ x, |γ x| ≤ 1},
        ∑ ν, (∑ x, γ.1 x * (P ν x - mixture P x)) ^ 2 := by
  refine (sum_klDivSum_add_klDivSum_mixture_le_div_four hQ₀ hQ₁ hQ hP₀ hP₁).trans ?_
  gcongr
  · exact iSup_sum_sq_nonneg _
  · linarith [sq_nonneg (exp ε - 1)]

end Theorem2

/-! ### Sequentially interactive channels and Corollary 1 -/

section Interactive

variable [Fintype α] [Fintype β]

/-- The law `M^n` of the private sample `Z_{1:n}` (the marginalization (3) of
Duchi–Jordan–Wainwright) when the `X_i ∼ P i` are independent and each `Z_i` is released through
the sequentially interactive channel `Q i z_{1:i-1} x_i z_i = Q_i(Z_i = z_i | X_i = x_i,
Z_{1:i-1} = z_{1:i-1})` (Figure 1, left):
`M^n(z_{1:n}) = ∑_{x_{1:n}} ∏_i P_i(x_i) Q_i(z_i | x_i, z_{1:i-1})`. Indices start at `0`. -/
noncomputable def seqMarginal (P : ℕ → α → ℝ) (Q : (i : ℕ) → (Fin i → β) → α → β → ℝ) (n : ℕ)
    (z : Fin n → β) : ℝ :=
  ∑ x : Fin n → α, ∏ i : Fin n, P i (x i) * Q i (fun j ↦ z (Fin.castLE i.isLt.le j)) (x i) (z i)

variable {P P' : ℕ → α → ℝ} {Q : (i : ℕ) → (Fin i → β) → α → β → ℝ} {ε : ℝ}

omit [Fintype β] in
/-- Since the `X_i` are independent, `M^n` factorizes into the one-step output laws
`M_i(· | z_{1:i-1}) = Q_i(· | ·, z_{1:i-1}) ∘ P_i`. -/
lemma seqMarginal_eq_prod (n : ℕ) (z : Fin n → β) :
    seqMarginal P Q n z =
      ∏ i : Fin n, outputLaw (P i) (Q i fun j ↦ z (Fin.castLE i.isLt.le j)) (z i) :=
  (Fintype.prod_sum fun (i : Fin n) a ↦
    P i a * Q i (fun j ↦ z (Fin.castLE i.isLt.le j)) a (z i)).symm

omit [Fintype β] in
/-- The chain rule for `M^n`: `M^{n+1}(z) = M^n(z_{1:n}) M_n(z_{n+1} | z_{1:n})`. -/
lemma seqMarginal_succ (n : ℕ) (z : Fin (n + 1) → β) :
    seqMarginal P Q (n + 1) z =
      seqMarginal P Q n (Fin.init z) * outputLaw (P n) (Q n (Fin.init z)) (z (Fin.last n)) := by
  rw [seqMarginal_eq_prod, seqMarginal_eq_prod, Fin.prod_univ_castSucc]
  rfl

omit [Fintype β] in
lemma seqMarginal_zero (z : Fin 0 → β) : seqMarginal P Q 0 z = 1 := by
  simp [seqMarginal]

/-- A sum over `(n + 1)`-tuples splits into a sum over the first `n` entries and the last one. -/
lemma sum_fin_succ_fun {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → β) → M) :
    ∑ z, f z = ∑ h : Fin n → β, ∑ b, f (Fin.snoc h b) := by
  rw [← (Fin.snocEquiv fun _ ↦ β).sum_comp, Fintype.sum_prod_type, sum_comm]
  rfl

omit [Fintype β] in
lemma seqMarginal_nonneg (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z) (hP₀ : ∀ i x, 0 ≤ P i x) (n : ℕ)
    (z : Fin n → β) : 0 ≤ seqMarginal P Q n z :=
  sum_nonneg fun _ _ ↦ prod_nonneg fun _ _ ↦ mul_nonneg (hP₀ _ _) (hQ₀ _ _ _ _)

lemma sum_seqMarginal (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1) (hP₁ : ∀ i, ∑ x, P i x = 1) (n : ℕ) :
    ∑ z, seqMarginal P Q n z = 1 := by
  induction n with
  | zero => simp [seqMarginal_zero]
  | succ n ih =>
    rw [sum_fin_succ_fun, ← ih]
    refine sum_congr rfl fun h _ ↦ ?_
    simp_rw [seqMarginal_succ, Fin.init_snoc, Fin.snoc_last, ← mul_sum,
      sum_outputLaw (hQ₁ n h) (hP₁ n), mul_one]

section Channel

variable (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z) (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1)
  (hQ : ∀ i h, IsLocalDP (Q i h) ε) (hP₀ : ∀ i x, 0 ≤ P i x) (hP₁ : ∀ i, ∑ x, P i x = 1)
  (hP'₀ : ∀ i x, 0 ≤ P' i x) (hP'₁ : ∀ i, ∑ x, P' i x = 1)
include hQ₀ hQ hP₀ hP₁ hP'₀ hP'₁

omit [Fintype β] in
/-- Under local differential privacy the laws `M^n` of two source sequences are mutually
absolutely continuous. -/
lemma seqMarginal_eq_zero_iff (n : ℕ) (z : Fin n → β) :
    seqMarginal P Q n z = 0 ↔ seqMarginal P' Q n z = 0 := by
  have := nonempty_of_sum_eq_one (hP₁ 0)
  simp_rw [seqMarginal_eq_prod, prod_eq_zero_iff,
    outputLaw_eq_zero_iff (hQ₀ _ _) (hQ _ _) (hP₀ _) (hP₁ _),
    outputLaw_eq_zero_iff (hQ₀ _ _) (hQ _ _) (hP'₀ _) (hP'₁ _)]

include hQ₁

/-- **Chain rule** for the divergence between the laws of two interactive private samples:
`D(M^{n+1} ‖ M'^{n+1}) = D(M^n ‖ M'^n) + ∑_h M^n(h) D(M_n(· | h) ‖ M'_n(· | h))`
(the chain rule step of the proof of Corollary 1 of Duchi–Jordan–Wainwright). -/
theorem klDivSum_seqMarginal_succ (n : ℕ) :
    klDivSum (seqMarginal P Q (n + 1)) (seqMarginal P' Q (n + 1)) =
      klDivSum (seqMarginal P Q n) (seqMarginal P' Q n) +
        ∑ h, seqMarginal P Q n h *
          klDivSum (outputLaw (P n) (Q n h)) (outputLaw (P' n) (Q n h)) := by
  have := nonempty_of_sum_eq_one (hP₁ 0)
  rw [klDivSum, klDivSum, sum_fin_succ_fun, ← sum_add_distrib]
  refine sum_congr rfl fun h _ ↦ ?_
  simp_rw [seqMarginal_succ, Fin.init_snoc, Fin.snoc_last, klDivSum, mul_sum]
  set M := seqMarginal P Q n h
  set M' := seqMarginal P' Q n h
  have hM : M * log (M / M') = ∑ b, outputLaw (P n) (Q n h) b * (M * log (M / M')) := by
    rw [← sum_mul, sum_outputLaw (hQ₁ n h) (hP₁ n), one_mul]
  rw [hM, ← sum_add_distrib]
  refine sum_congr rfl fun b _ ↦ ?_
  set m := outputLaw (P n) (Q n h) b
  set m' := outputLaw (P' n) (Q n h) b
  rcases eq_or_ne M 0 with hM0 | hM0
  · simp [hM0]
  rcases eq_or_ne m 0 with hm0 | hm0
  · simp [hm0]
  have hM'0 : M' ≠ 0 := fun h' ↦
    hM0 ((seqMarginal_eq_zero_iff hQ₀ hQ hP₀ hP₁ hP'₀ hP'₁ n h).2 h')
  have hm'0 : m' ≠ 0 := fun h' ↦ hm0 <| by
    rw [outputLaw_eq_zero_iff (hQ₀ n h) (hQ n h) (hP₀ n) (hP₁ n)]
    rwa [outputLaw_eq_zero_iff (hQ₀ n h) (hQ n h) (hP'₀ n) (hP'₁ n)] at h'
  rw [mul_div_mul_comm, log_mul (div_ne_zero hM0 hM'0) (div_ne_zero hm0 hm'0)]
  ring

/-- **Corollary 1** of Duchi–Jordan–Wainwright, one-sided and sharper form: for a sequentially
interactive channel each of whose steps is `ε`-locally differentially private, and independent
samples `X_i ∼ P_i` (resp. `P'_i`),
`D(M^n ‖ M'^n) ≤ (e^ε - 1)² ∑_{i<n} ‖P_i - P'_i‖²_TV`. -/
theorem klDivSum_seqMarginal_le (n : ℕ) :
    klDivSum (seqMarginal P Q n) (seqMarginal P' Q n) ≤
      (exp ε - 1) ^ 2 * ∑ i ∈ range n, tvDistSum (P i) (P' i) ^ 2 := by
  induction n with
  | zero => simp [klDivSum, seqMarginal_zero]
  | succ n ih =>
    rw [klDivSum_seqMarginal_succ hQ₀ hQ₁ hQ hP₀ hP₁ hP'₀ hP'₁, sum_range_succ, mul_add]
    refine add_le_add ih ?_
    calc ∑ h, seqMarginal P Q n h *
          klDivSum (outputLaw (P n) (Q n h)) (outputLaw (P' n) (Q n h))
        ≤ ∑ h, seqMarginal P Q n h * ((exp ε - 1) ^ 2 * tvDistSum (P n) (P' n) ^ 2) :=
          sum_le_sum fun h _ ↦ mul_le_mul_of_nonneg_left
            (klDivSum_outputLaw_le (hQ₀ n h) (hQ₁ n h) (hQ n h) (hP₀ n) (hP₁ n) (hP'₀ n)
              (hP'₁ n))
            (seqMarginal_nonneg hQ₀ hP₀ n h)
      _ = (exp ε - 1) ^ 2 * tvDistSum (P n) (P' n) ^ 2 := by
          rw [← sum_mul, sum_seqMarginal hQ₁ hP₁, one_mul]

/-- **Corollary 1** of Duchi–Jordan–Wainwright, symmetrized, with constant `2` instead of `4`:
`D(M^n ‖ M'^n) + D(M'^n ‖ M^n) ≤ 2 (e^ε - 1)² ∑_{i<n} ‖P_i - P'_i‖²_TV`. -/
theorem klDivSum_add_klDivSum_seqMarginal_le (n : ℕ) :
    klDivSum (seqMarginal P Q n) (seqMarginal P' Q n) +
        klDivSum (seqMarginal P' Q n) (seqMarginal P Q n) ≤
      2 * (exp ε - 1) ^ 2 * ∑ i ∈ range n, tvDistSum (P i) (P' i) ^ 2 := by
  have h₁ := klDivSum_seqMarginal_le hQ₀ hQ₁ hQ hP₀ hP₁ hP'₀ hP'₁ n
  have h₂ := klDivSum_seqMarginal_le hQ₀ hQ₁ hQ hP'₀ hP'₁ hP₀ hP₁ n
  simp_rw [tvDistSum_comm (p := P' _)] at h₂
  linarith

/-- Finite-alphabet case of **Corollary 1** of Duchi–Jordan–Wainwright, eq. (13): for a
sequentially interactive channel each of whose steps is `ε`-locally differentially private
(eq. (1)), and independent samples `X_i ∼ P_i` (resp. `P'_i`),
`D(M^n ‖ M'^n) + D(M'^n ‖ M^n) ≤ 4 (e^ε - 1)² ∑_{i<n} ‖P_i - P'_i‖²_TV`. The hypotheses are
assumed for all `i : ℕ`; only `i < n` matters. -/
theorem klDivSum_add_klDivSum_seqMarginal_le_four (n : ℕ) :
    klDivSum (seqMarginal P Q n) (seqMarginal P' Q n) +
        klDivSum (seqMarginal P' Q n) (seqMarginal P Q n) ≤
      4 * (exp ε - 1) ^ 2 * ∑ i ∈ range n, tvDistSum (P i) (P' i) ^ 2 := by
  have := klDivSum_add_klDivSum_seqMarginal_le hQ₀ hQ₁ hQ hP₀ hP₁ hP'₀ hP'₁ n
  have : 0 ≤ (exp ε - 1) ^ 2 * ∑ i ∈ range n, tvDistSum (P i) (P' i) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ ↦ sq_nonneg _)
  linarith

end Channel

end Interactive

/-! ### The mutual information bound (14) -/

section MutualInfo

variable {ι γ : Type*} [Fintype ι] [Fintype γ]

/-- The mutual information `I(Z; V) = E_V [D(M_V ‖ M̄)]` between `V` uniform on the finite set `ι`
and `Z` with conditional law `M ν` given `V = ν`, where `M̄ = |ι|⁻¹ ∑_ν M_ν` is the law of `Z`
(the definition of Section 2 of Duchi–Jordan–Wainwright, as used in (14)). -/
noncomputable def mutualInfoUniform (M : ι → γ → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ ν, klDivSum (M ν) (mixture M)

/-- Convexity of the divergence in its second argument:
`D(p ‖ |ι|⁻¹ ∑_ν q_ν) ≤ |ι|⁻¹ ∑_ν D(p ‖ q_ν)` when every `q_ν` is positive wherever `p` is
nonzero. -/
lemma klDivSum_mean_le [Nonempty ι] {p : γ → ℝ} {q : ι → γ → ℝ} (hp : ∀ z, 0 ≤ p z)
    (hq : ∀ ν z, p z ≠ 0 → 0 < q ν z) :
    klDivSum p (mixture q) ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ ν, klDivSum p (q ν) := by
  set w := (Fintype.card ι : ℝ)⁻¹
  have hw : 0 < w := inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hw₁ : ∑ _ν : ι, w = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  simp_rw [klDivSum, mixture, mul_sum]
  rw [sum_comm]
  refine sum_le_sum fun z _ ↦ ?_
  rcases (hp z).eq_or_lt with h | h
  · simp [← h]
  have hqz : ∀ ν, 0 < q ν z := fun ν ↦ hq ν z h.ne'
  have hmean : 0 < ∑ ν, w * q ν z := sum_pos (fun ν _ ↦ mul_pos hw (hqz ν)) univ_nonempty
  have hjensen : ∑ ν, w * log (q ν z) ≤ log (∑ ν, w * q ν z) :=
    strictConcaveOn_log_Ioi.concaveOn.le_map_sum (fun _ _ ↦ hw.le) hw₁
      fun ν _ ↦ Set.mem_Ioi.2 (hqz ν)
  calc p z * log (p z / ∑ ν, w * q ν z) = p z * (log (p z) - log (∑ ν, w * q ν z)) := by
        rw [log_div h.ne' hmean.ne']
    _ ≤ p z * (log (p z) - ∑ ν, w * log (q ν z)) := by gcongr
    _ = ∑ ν, w * (p z * log (p z / q ν z)) := by
        simp_rw [log_div h.ne' (hqz _).ne']
        have : ∑ ν, w * (p z * (log (p z) - log (q ν z))) =
            (∑ ν : ι, w) * (p z * log (p z)) - p z * ∑ ν, w * log (q ν z) := by
          rw [sum_mul, mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun ν _ ↦ by ring
        rw [this, hw₁]
        ring

/-- First inequality of (14) in Duchi–Jordan–Wainwright: if the laws `M ν` are mutually absolutely
continuous, `I(Z; V) ≤ |ι|⁻² ∑_{ν, ν'} D(M_ν ‖ M_ν')`. -/
theorem mutualInfoUniform_le [Nonempty ι] {M : ι → γ → ℝ} (hM₀ : ∀ ν z, 0 ≤ M ν z)
    (hM : ∀ ν ν' z, M ν z = 0 ↔ M ν' z = 0) :
    mutualInfoUniform M ≤
      (Fintype.card ι : ℝ)⁻¹ ^ 2 * ∑ ν, ∑ ν', klDivSum (M ν) (M ν') := by
  rw [mutualInfoUniform, sq, mul_assoc]
  gcongr
  rw [mul_sum]
  gcongr with ν
  refine klDivSum_mean_le (hM₀ ν) fun ν' z hz ↦ (hM₀ ν' z).lt_of_ne' fun h ↦ hz ?_
  exact (hM ν ν' z).2 h

variable [Fintype α] [Fintype β] [Nonempty ι] {P : ι → ℕ → α → ℝ}
  {Q : (i : ℕ) → (Fin i → β) → α → β → ℝ} {ε : ℝ}

/-- **Mutual information bound** (14) of Duchi–Jordan–Wainwright, sharper form: if `V` is uniform
on the finite set `ι` and, given `V = ν`, the independent samples `X_i ∼ P ν i` are released
through a sequentially interactive channel each of whose steps is `ε`-locally differentially
private, then
`I(Z_{1:n}; V) ≤ (e^ε - 1)² ∑_{i<n} |ι|⁻² ∑_{ν, ν'} ‖P_{ν,i} - P_{ν',i}‖²_TV`. -/
theorem mutualInfoUniform_seqMarginal_le (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z)
    (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1) (hQ : ∀ i h, IsLocalDP (Q i h) ε)
    (hP₀ : ∀ ν i x, 0 ≤ P ν i x) (hP₁ : ∀ ν i, ∑ x, P ν i x = 1) (n : ℕ) :
    mutualInfoUniform (fun ν ↦ seqMarginal (P ν) Q n) ≤
      (exp ε - 1) ^ 2 * ∑ i ∈ range n, (Fintype.card ι : ℝ)⁻¹ ^ 2 *
        ∑ ν, ∑ ν', tvDistSum (P ν i) (P ν' i) ^ 2 := by
  refine (mutualInfoUniform_le (fun ν ↦ seqMarginal_nonneg hQ₀ (hP₀ ν) n) fun ν ν' ↦
    seqMarginal_eq_zero_iff hQ₀ hQ (hP₀ ν) (hP₁ ν) (hP₀ ν') (hP₁ ν') n).trans ?_
  set c := (exp ε - 1) ^ 2
  set w := (Fintype.card ι : ℝ)⁻¹ ^ 2
  calc w * ∑ ν, ∑ ν', klDivSum (seqMarginal (P ν) Q n) (seqMarginal (P ν') Q n)
      ≤ w * ∑ ν, ∑ ν', c * ∑ i ∈ range n, tvDistSum (P ν i) (P ν' i) ^ 2 := by
        gcongr with ν _ ν' _
        exact klDivSum_seqMarginal_le hQ₀ hQ₁ hQ (hP₀ ν) (hP₁ ν) (hP₀ ν') (hP₁ ν') n
    _ = c * ∑ i ∈ range n, w * ∑ ν, ∑ ν', tvDistSum (P ν i) (P ν' i) ^ 2 := by
        simp_rw [mul_sum]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun ν _ ↦ ?_
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun ν' _ ↦ sum_congr rfl fun i _ ↦ ?_
        ring

/-- Finite-alphabet case of the **mutual information bound** (14) of Duchi–Jordan–Wainwright: if
`V` is uniform on the finite set `ι` and, given `V = ν`, the independent samples `X_i ∼ P ν i` are
released through a sequentially interactive channel each of whose steps is `ε`-locally
differentially private, then
`I(Z_{1:n}; V) ≤ 4 (e^ε - 1)² ∑_{i<n} |ι|⁻² ∑_{ν, ν'} ‖P_{ν,i} - P_{ν',i}‖²_TV`. The hypotheses
are assumed for all `i : ℕ`; only `i < n` matters. -/
theorem mutualInfoUniform_seqMarginal_le_four (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z)
    (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1) (hQ : ∀ i h, IsLocalDP (Q i h) ε)
    (hP₀ : ∀ ν i x, 0 ≤ P ν i x) (hP₁ : ∀ ν i, ∑ x, P ν i x = 1) (n : ℕ) :
    mutualInfoUniform (fun ν ↦ seqMarginal (P ν) Q n) ≤
      4 * (exp ε - 1) ^ 2 * ∑ i ∈ range n, (Fintype.card ι : ℝ)⁻¹ ^ 2 *
        ∑ ν, ∑ ν', tvDistSum (P ν i) (P ν' i) ^ 2 := by
  have := mutualInfoUniform_seqMarginal_le hQ₀ hQ₁ hQ hP₀ hP₁ n
  have : 0 ≤ (exp ε - 1) ^ 2 * ∑ i ∈ range n, (Fintype.card ι : ℝ)⁻¹ ^ 2 *
      ∑ ν, ∑ ν', tvDistSum (P ν i) (P ν' i) ^ 2 := by positivity
  linarith

/-- For `0 ≤ ε ≤ log 2`, `(e^ε - 1)² ≤ 4 ε²`. -/
lemma sq_exp_sub_one_le (hε₀ : 0 ≤ ε) (hε : ε ≤ log 2) : (exp ε - 1) ^ 2 ≤ 4 * ε ^ 2 := by
  have h₁ : exp ε - 1 ≤ ε * exp ε := by
    have h := add_one_le_exp (-ε)
    have h' : exp (-ε) * exp ε = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    nlinarith [mul_le_mul_of_nonneg_right h (exp_pos ε).le]
  have h₂ : exp ε ≤ 2 := by
    calc exp ε ≤ exp (log 2) := exp_le_exp.2 hε
      _ = 2 := exp_log two_pos
  have h₃ : 0 ≤ exp ε - 1 := sub_nonneg.2 (one_le_exp hε₀)
  have h₄ : exp ε - 1 ≤ 2 * ε := by nlinarith [mul_le_mul_of_nonneg_left h₂ hε₀]
  calc (exp ε - 1) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ h₃ h₄ 2
    _ = 4 * ε ^ 2 := by ring

/-- The mutual information step of **Corollary 3** (private local Fano) of Duchi–Jordan–Wainwright,
sharper form: if `‖P_{ν,i} - P_{ν',i}‖²_TV ≤ r / 2` for all `ν, ν', i` (the paper obtains this with
`r = κ²δ²` from a `(δ, κ)` local packing (17) by Pinsker's inequality; here it is a hypothesis)
and `0 ≤ ε ≤ log 2`, then `I(Z_{1:n}; V) ≤ 2 n ε² r`. -/
theorem mutualInfoUniform_seqMarginal_le_two_mul (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z)
    (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1) (hQ : ∀ i h, IsLocalDP (Q i h) ε)
    (hP₀ : ∀ ν i x, 0 ≤ P ν i x) (hP₁ : ∀ ν i, ∑ x, P ν i x = 1) (hε₀ : 0 ≤ ε)
    (hε : ε ≤ log 2) {r : ℝ} (hr : ∀ ν ν' i, tvDistSum (P ν i) (P ν' i) ^ 2 ≤ r / 2) (n : ℕ) :
    mutualInfoUniform (fun ν ↦ seqMarginal (P ν) Q n) ≤ 2 * n * ε ^ 2 * r := by
  obtain ⟨ν₀⟩ := ‹Nonempty ι›
  have hr₀ : 0 ≤ r / 2 := (sq_nonneg _).trans (hr ν₀ ν₀ 0)
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∑ i ∈ range n, (Fintype.card ι : ℝ)⁻¹ ^ 2 *
      ∑ ν, ∑ ν', tvDistSum (P ν i) (P ν' i) ^ 2 ≤ n * (r / 2) := by
    calc _ ≤ ∑ i ∈ range n, (Fintype.card ι : ℝ)⁻¹ ^ 2 * ∑ ν : ι, ∑ ν' : ι, r / 2 := by
          gcongr with i _ ν _ ν' _
          exact hr ν ν' i
      _ = n * (r / 2) := by
          simp only [sum_const, card_univ, card_range, nsmul_eq_mul]
          field_simp
  calc mutualInfoUniform (fun ν ↦ seqMarginal (P ν) Q n)
      ≤ (exp ε - 1) ^ 2 * (n * (r / 2)) :=
        (mutualInfoUniform_seqMarginal_le hQ₀ hQ₁ hQ hP₀ hP₁ n).trans
          (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
    _ ≤ 4 * ε ^ 2 * (n * (r / 2)) := by
        gcongr
        exact sq_exp_sub_one_le hε₀ hε
    _ = 2 * n * ε ^ 2 * r := by ring

/-- The mutual information step in the proof of **Corollary 3** (private local Fano) of
Duchi–Jordan–Wainwright, on finite alphabets: if `‖P_{ν,i} - P_{ν',i}‖²_TV ≤ κ²δ² / 2` for all
`ν, ν'` and all `i : ℕ` (only `i < n` matters) and `ε ∈ [0, 22/35]`, then
`I(Z_{1:n}; V) ≤ 4 n ε² κ² δ²`. This is not the Fano lower bound (19) itself, and it assumes the
total variation bound that the paper derives from the packing condition (17) by Pinsker's
inequality (not formalized here), rather than (17). -/
theorem mutualInfoUniform_seqMarginal_le_four_mul (hQ₀ : ∀ i h x z, 0 ≤ Q i h x z)
    (hQ₁ : ∀ i h x, ∑ z, Q i h x z = 1) (hQ : ∀ i h, IsLocalDP (Q i h) ε)
    (hP₀ : ∀ ν i x, 0 ≤ P ν i x) (hP₁ : ∀ ν i, ∑ x, P ν i x = 1) (hε₀ : 0 ≤ ε)
    (hε : ε ≤ 22 / 35) {κ δ : ℝ}
    (hP : ∀ ν ν' i, tvDistSum (P ν i) (P ν' i) ^ 2 ≤ κ ^ 2 * δ ^ 2 / 2) (n : ℕ) :
    mutualInfoUniform (fun ν ↦ seqMarginal (P ν) Q n) ≤ 4 * n * ε ^ 2 * κ ^ 2 * δ ^ 2 := by
  have hε' : ε ≤ log 2 := hε.trans (by linarith [log_two_gt_d9])
  have := mutualInfoUniform_seqMarginal_le_two_mul hQ₀ hQ₁ hQ hP₀ hP₁ hε₀ hε' hP n
  have : 0 ≤ 2 * n * ε ^ 2 * (κ ^ 2 * δ ^ 2) := by positivity
  linarith

end MutualInfo

/-! ### Agreement with Mathlib's Kullback–Leibler divergence -/

section Mathlib

open MeasureTheory

variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  {μ ν : Measure γ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- On a finite alphabet, the integral of the log-likelihood ratio of two probability measures
with `μ ≪ ν` is `klDivSum` of their point masses. -/
lemma integral_llr_eq_klDivSum (h : μ ≪ ν) :
    ∫ z, llr μ ν z ∂μ = klDivSum (fun z ↦ μ.real {z}) fun z ↦ ν.real {z} := by
  rw [integral_fintype .of_finite, klDivSum]
  refine sum_congr rfl fun z _ ↦ ?_
  rw [smul_eq_mul, llr_def]
  rcases eq_or_ne (μ {z}) 0 with hz | hz
  · simp [measureReal_def, hz]
  have hy_eq : μ {z} = μ.rnDeriv ν z * ν {z} := by
    rw [← Measure.setLIntegral_rnDeriv h, lintegral_singleton]
  have hνz : ν.real {z} ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨fun h0 ↦ hz (by simp [hy_eq, h0]), measure_ne_top _ _⟩
  rw [measureReal_def μ, hy_eq, ENNReal.toReal_mul, ← measureReal_def, mul_div_assoc,
    div_self hνz, mul_one]

/-- On a finite alphabet, Mathlib's Kullback–Leibler divergence of two probability measures with
`μ ≪ ν` is the finite sum `klDivSum` of their point masses; in particular it is finite. (Without
`μ ≪ ν`, `klDiv μ ν = ∞`.) -/
theorem klDiv_eq_ofReal_klDivSum (h : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal (klDivSum (fun z ↦ μ.real {z}) fun z ↦ ν.real {z}) := by
  rw [klDiv_of_ac_of_integrable h .of_finite, integral_llr_eq_klDivSum h]
  simp

end Mathlib

end InformationTheory
