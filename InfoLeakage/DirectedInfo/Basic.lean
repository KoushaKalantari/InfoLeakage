/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.LocalPrivacy.Basic
public import Mathlib.Probability.ConditionalProbability
public import Statlib.Divergence.MutualInformation.Basic

/-!
# Directed information

This file formalizes directed information and its basic theory from

* J. L. Massey, *Causality, feedback and directed information*, Proc. 1990 Int. Symp. on
  Information Theory and its Applications (ISITA), Waikiki, pp. 303–305 (not on arXiv; result and
  equation numbers refer to the preprint `BI532.pdf` of the ETH Massey archive,
  <http://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI532.pdf>);
* J. L. Massey and P. C. Massey, *Conservation of mutual and directed information*, Proc. IEEE
  ISIT 2005, pp. 157–158, doi:10.1109/ISIT.2005.1523313 (not on arXiv);
* G. Kramer, *Directed information for channels with feedback*, PhD thesis, ETH Zürich, 1998
  (causal conditioning).

Random variables are functions on a finite sample space `Ω` carrying a probability measure `μ`;
a pair of sequences is `X : Fin n → Ω → 𝓧`, `Y : Fin n → Ω → 𝓨`. The joint law of `(X^n, Y^n)`
is the special case `Ω = (Fin n → 𝓧) × (Fin n → 𝓨)`, `X i z = z.1 i`, `Y i z = z.2 i`, for which
the main results are also stated with Statlib's `mutualInfo`. Information is measured in nats.

## Main definitions

* `DirectedInfo.entropy μ f`, `DirectedInfo.mutualInfoSum μ f g`,
  `DirectedInfo.condMutualInfoSum μ f g h`: Shannon entropy, mutual information and conditional
  mutual information of finite-valued random variables, as finite sums over the sample space.
* `DirectedInfo.past Y k`: the past `Y^k = (Y₀, …, Y_{k-1})` of a sequence.
* `directedInfo μ X Y`: Massey's directed information `I(X^n → Y^n) = ∑_i I(X^i; Y_i | Y^{i-1})`.
* `delayedDirectedInfo μ Y X`: `I(0 ∗ Y^{n-1} → X^n) = ∑_i I(Y^{i-1}; X_i | X^{i-1})`.
* `IsWithoutFeedback`, `IsMemoryless`, `IsCausal`: Massey's conditions (2), (1) and (8).
* `causalCond μ Y X y x`, `causalCondDelayed μ X Y x y`: the causal conditionings
  `P(y^n ‖ x^n) = ∏_i P(y_i | x^i, y^{i-1})` and `P(x^n ‖ y^{n-1}) = ∏_i P(x_i | x^{i-1}, y^{i-1})`.

## Main statements

* `DirectedInfo.condMutualInfoSum_nonneg`, `DirectedInfo.mutualInfoSum_nonneg`: nonnegativity.
* `DirectedInfo.mutualInfoSum_prod`, `DirectedInfo.condMutualInfoSum_prod`,
  `DirectedInfo.mutualInfoSum_eq_sum_condMutualInfoSum`: chain rules.
* `DirectedInfo.mutualInfo_eq_ofReal_mutualInfoSum`: agreement with Statlib's `mutualInfo`, which
  is therefore finite (`DirectedInfo.mutualInfo_ne_top`).
* `mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo`: the **conservation law**
  `I(X^n; Y^n) = I(X^n → Y^n) + I(0 ∗ Y^{n-1} → X^n)`.
* `directedInfo_le_mutualInfoSum`, `directedInfo_eq_mutualInfoSum_of_isWithoutFeedback`:
  `I(X^n → Y^n) ≤ I(X^n; Y^n)`, with equality without feedback.
* `directedInfo_le_sum_mutualInfoSum_of_isMemoryless`: for a DMC, `I(X^n → Y^n) ≤ ∑ I(X_i; Y_i)`
  (the inequality of Massey's Theorem 2; its equality condition is not formalized).
* `mutualInfoSum_le_directedInfo_of_isCausal`: in a causal system, `I(U; Y^n) ≤ I(X^n → Y^n)`.
* `measure_preimage_eq_causalCondDelayed_mul_causalCond`:
  `P(x^n, y^n) = P(x^n ‖ y^{n-1}) P(y^n ‖ x^n)`.
* `cond_eq_causalCond_of_isWithoutFeedback`: without feedback, `P(y^n | x^n) = P(y^n ‖ x^n)`.
* `directedInfo_eq_sum_log_causalCond`: `I(X^n → Y^n) = E[log (P(Y^n ‖ X^n) / P(Y^n))]`.
* `directedInfo_eq_klDivSum`: `I(X^n → Y^n) = ∑_{x,y} P(x, y) log (P(x, y) / q(x, y))` with
  `q(x, y) = P(x^n ‖ y^{n-1}) P(y^n)` (see the implementation notes on the normalization of `q`).

## Paper results and their Lean names

* Massey (1990), (7) → `directedInfo`; (1) → `IsMemoryless`; (2) → `IsWithoutFeedback`;
  (8) → `IsCausal`; (3) → `measure_preimage_eq_causalCondDelayed_mul_causalCond`;
  (4) → `cond_eq_causalCond_of_isWithoutFeedback`.
* Massey (1990), Theorem 1 → `directedInfo_le_mutualInfoSum` and
  `directedInfo_eq_mutualInfoSum_of_isWithoutFeedback`; for a joint law with Statlib's mutual
  information, `directedInfo_le_toReal_mutualInfo` and
  `directedInfo_eq_toReal_mutualInfo_of_isWithoutFeedback`.
* Massey (1990), Theorem 2 → `directedInfo_le_sum_mutualInfoSum_of_isMemoryless` (the inequality
  only) and the identity `directedInfo_eq_sum_sub_of_isMemoryless`.
* Massey (1990), Theorem 3 → `mutualInfoSum_le_directedInfo_of_isCausal`.
* Massey–Massey (2005), conservation law → `mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo`
  and, for a joint law, `mutualInfo_eq_ofReal_directedInfo_add_ofReal_delayedDirectedInfo` and
  `toReal_mutualInfo_eq_directedInfo_add_delayedDirectedInfo`.
* Kramer (1998), causal conditioning → `causalCond`, `causalCondDelayed`,
  `directedInfo_eq_sum_log_causalCond`, `directedInfo_eq_klDivSum`.

## Implementation notes

* Indices start at `0`: the paper's `X_i` and `X^i = (X_1, …, X_i)` are `X (i - 1)` and
  `past X i`, so the term of `directedInfo` at `i : Fin n` is
  `I(past X (i + 1); Y i | past Y i)`, the paper's `I(X^{i+1}; Y_{i+1} | Y^i)`.
* Entropies are negative sums over the sample space, `H(f) = -∑_ω μ{ω} log P(f = f ω)`. They
  only depend on the partition generated by the random variable (`DirectedInfo.entropy_congr`),
  so the chain rules and the conservation law are telescoping identities between entropies of
  pasts. On the support
  of `μ` all level sets have positive probability (`DirectedInfo.probEq_pos`), so the junk value
  `log 0 = 0` never enters; `DirectedInfo.entropy_eq_neg_sum` recovers `-∑_a P(a) log P(a)`.
* Conditional probabilities are Mathlib's `μ[t | s]`. The conditions `IsWithoutFeedback`,
  `IsMemoryless` and `IsCausal` quantify only over conditioning events of positive probability,
  where the paper's conditional probabilities are defined.
* The definitions are meant for a sample space with measurable singletons
  (`MeasurableSingletonClass Ω`), which every theorem relating them to probabilities assumes; for a
  coarser σ-algebra, `μ {ω}` and `μ (f ⁻¹' {a})` are outer measures and the sums are junk values.
  The algebraic identities (chain rules, conservation law) hold for every probability measure,
  without requiring measurable singletons; they need the normalization `μ univ = 1` (for a
  one-point sample space of mass `2`, `n = 1` and constant `X`, `Y`, `mutualInfoSum` is
  `-2 log 2` while both directed informations vanish).
* Theorem 1 is derived from the conservation law and the nonnegativity of conditional mutual
  information rather than by Massey's monotonicity argument.
* With Mathlib's convention `μ[t | s] = 0` when `μ s = 0`, `causalCondDelayed` vanishes on
  histories of probability zero, so `q(x, y) = P(x^n ‖ y^{n-1}) P(y^n)` in
  `directedInfo_eq_klDivSum` is only sub-normalized: for `n = 2`, `X₁` uniform on `{0, 1}`,
  `Y₁ = X₁` and `X₂ = Y₂ = 0`, `∑ q = 1/2`. On the support of `P_{X^n Y^n}` every conditioning
  event has positive probability, so `q` agrees there with the version built from any choice of
  conditional probabilities (in particular a normalized one), and `klDivSum` only evaluates `q`
  there. The normalization of such a version is not formalized.
* Theorem numbers refer to the ETH-archive preprint of Massey (1990), where
  `I(X^N → Y^N) ≤ I(X^N; Y^N)` (with equality without feedback) is Theorem 1, Theorem 2 is the
  bound for a discrete memoryless channel and Theorem 3 the bound for causal systems.
* The Massey–Massey (2005) proceedings paper was not openly accessible; the conservation law is
  formalized in its standard form `I(X^N; Y^N) = I(X^N → Y^N) + I(0 ∗ Y^{N-1} → X^N)`, as quoted
  in H. Permuter, T. Weissman, A. Goldsmith, *Finite state channels with time-invariant
  deterministic feedback*, [arXiv:cs/0608070](https://arxiv.org/abs/cs/0608070), Lemma 7 with
  `Z = Y`.

## Not formalized

* The equality condition of Massey (1990), Theorem 2 ("if and only if `Y_1, …, Y_N` are
  statistically independent"); `directedInfo_eq_sum_sub_of_isMemoryless` gives the exact gap
  `∑_i I(Y^{i-1}; Y_i)`, but `I = 0 ⇔` independence is not proved here.
* Massey (1990), eq. (5), `P(y^N | x^N) = ∏_n P(y_n | x_n)` for a discrete memoryless channel
  used without feedback (eq. (4) is `cond_eq_causalCond_of_isWithoutFeedback`).
* Agreement of `condMutualInfoSum` with Statlib's `condMutualInfo`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

namespace InformationTheory.DirectedInfo

private lemma eq_iff_rangeFactorization_eq {Ω α : Type*} (u : Ω → α) (ω ω' : Ω) :
    u ω' = u ω ↔ Set.rangeFactorization u ω' = Set.rangeFactorization u ω := by
  simp [Set.rangeFactorization, Subtype.ext_iff]

variable {Ω α β γ δ α' β' γ' : Type*} [MeasurableSpace Ω]

section Definitions

variable (μ : Measure Ω)

/-- The probability `P(f = f ω)` of the level set of the random variable `f` through `ω`.
The definitions of this file are meaningful when singletons are measurable
(`MeasurableSingletonClass Ω`); otherwise `μ.real` returns outer measures. -/
noncomputable def probEq (f : Ω → α) (ω : Ω) : ℝ :=
  μ.real (f ⁻¹' {f ω})

variable [Fintype Ω]

/-- The Shannon entropy `H(f) = -∑_ω μ{ω} log P(f = f ω)` (in nats) of a random variable `f` on a
finite probability space; grouping the sample points by the value of `f`, this is the familiar
`-∑_a P(f = a) log P(f = a)`. -/
noncomputable def entropy (f : Ω → α) : ℝ :=
  -∑ ω, μ.real {ω} * log (probEq μ f ω)

/-- The mutual information `I(f; g) = ∑_ω μ{ω} log (P(f, g) / (P(f) P(g)))` (in nats) of two random
variables on a finite probability space, the expectation of the information density. -/
noncomputable def mutualInfoSum (f : Ω → α) (g : Ω → β) : ℝ :=
  ∑ ω, μ.real {ω} *
    log (probEq μ (fun ω ↦ (f ω, g ω)) ω / (probEq μ f ω * probEq μ g ω))

/-- The conditional mutual information
`I(f; g | h) = ∑_ω μ{ω} log (P(f, g, h) P(h) / (P(f, h) P(g, h)))` (in nats) of three random
variables on a finite probability space. -/
noncomputable def condMutualInfoSum (f : Ω → α) (g : Ω → β) (h : Ω → γ) : ℝ :=
  ∑ ω, μ.real {ω} * log (probEq μ (fun ω ↦ (f ω, g ω, h ω)) ω * probEq μ h ω /
    (probEq μ (fun ω ↦ (f ω, h ω)) ω * probEq μ (fun ω ↦ (g ω, h ω)) ω))

end Definitions

variable {μ : Measure Ω}

section Partition

/-- The probability of a level set only depends on the level set. -/
lemma probEq_congr {f : Ω → α} {g : Ω → β} {ω : Ω} (h : ∀ ω', f ω' = f ω ↔ g ω' = g ω) :
    probEq μ f ω = probEq μ g ω := by
  unfold probEq
  congr 1
  ext ω'
  exact h ω'

variable [Fintype Ω]

/-- Two random variables generating the same partition of the sample space have the same
entropy. -/
lemma entropy_congr {f : Ω → α} {g : Ω → β} (h : ∀ ω ω', f ω' = f ω ↔ g ω' = g ω) :
    entropy μ f = entropy μ g := by
  simp_rw [entropy, probEq_congr (h _)]

/-- The conditional mutual information only depends on the partitions generated by the three
random variables. -/
lemma condMutualInfoSum_congr {f : Ω → α} {g : Ω → β} {h : Ω → γ} {f' : Ω → α'} {g' : Ω → β'}
    {h' : Ω → γ'} (hf : ∀ ω ω', f ω' = f ω ↔ f' ω' = f' ω)
    (hg : ∀ ω ω', g ω' = g ω ↔ g' ω' = g' ω) (hh : ∀ ω ω', h ω' = h ω ↔ h' ω' = h' ω) :
    condMutualInfoSum μ f g h = condMutualInfoSum μ f' g' h' := by
  unfold condMutualInfoSum
  refine sum_congr rfl fun ω _ ↦ ?_
  rw [probEq_congr (f := fun ω ↦ (f ω, g ω, h ω)) (g := fun ω ↦ (f' ω, g' ω, h' ω)) fun ω' ↦ by
      simp only [Prod.mk.injEq, hf ω ω', hg ω ω', hh ω ω'],
    probEq_congr (f := h) (hh ω),
    probEq_congr (f := fun ω ↦ (f ω, h ω)) (g := fun ω ↦ (f' ω, h' ω)) fun ω' ↦ by
      simp only [Prod.mk.injEq, hf ω ω', hh ω ω'],
    probEq_congr (f := fun ω ↦ (g ω, h ω)) (g := fun ω ↦ (g' ω, h' ω)) fun ω' ↦ by
      simp only [Prod.mk.injEq, hg ω ω', hh ω ω']]

/-- The entropy of a constant random variable is zero. -/
lemma entropy_const [IsProbabilityMeasure μ] (a : α) : entropy μ (fun _ ↦ a) = 0 := by
  simp [entropy, probEq]

end Partition

section Positivity

variable [IsFiniteMeasure μ]

/-- A sample point has probability at most that of its level set. -/
lemma measureReal_singleton_le_probEq (f : Ω → α) (ω : Ω) : μ.real {ω} ≤ probEq μ f ω :=
  measureReal_mono (by simp)

/-- On the support of `μ`, level sets have positive probability: the junk value `log 0 = 0` never
enters the sums defining entropies and mutual informations. -/
lemma probEq_pos {ω : Ω} (hω : μ.real {ω} ≠ 0) (f : Ω → α) : 0 < probEq μ f ω :=
  (measureReal_nonneg.lt_of_ne (Ne.symm hω)).trans_le (measureReal_singleton_le_probEq f ω)

end Positivity

section Formulas

variable [Fintype Ω] [IsFiniteMeasure μ]

/-- `I(f; g) = H(f) + H(g) - H(f, g)`. -/
theorem mutualInfoSum_eq_entropy (f : Ω → α) (g : Ω → β) :
    mutualInfoSum μ f g = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω)) := by
  have key (ω : Ω) : μ.real {ω} *
      log (probEq μ (fun ω ↦ (f ω, g ω)) ω / (probEq μ f ω * probEq μ g ω)) =
      μ.real {ω} * log (probEq μ (fun ω ↦ (f ω, g ω)) ω) - μ.real {ω} * log (probEq μ f ω) -
        μ.real {ω} * log (probEq μ g ω) := by
    rcases eq_or_ne (μ.real {ω}) 0 with h0 | h0
    · simp [h0]
    rw [log_div (probEq_pos h0 _).ne' (mul_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne',
      log_mul (probEq_pos h0 _).ne' (probEq_pos h0 _).ne']
    ring
  simp only [mutualInfoSum, entropy, key, sum_sub_distrib]
  ring

/-- `I(f; g | h) = H(f, h) + H(g, h) - H(f, g, h) - H(h)`. -/
theorem condMutualInfoSum_eq_entropy (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    condMutualInfoSum μ f g h = entropy μ (fun ω ↦ (f ω, h ω)) + entropy μ (fun ω ↦ (g ω, h ω)) -
      entropy μ (fun ω ↦ (f ω, g ω, h ω)) - entropy μ h := by
  have key (ω : Ω) : μ.real {ω} * log (probEq μ (fun ω ↦ (f ω, g ω, h ω)) ω * probEq μ h ω /
      (probEq μ (fun ω ↦ (f ω, h ω)) ω * probEq μ (fun ω ↦ (g ω, h ω)) ω)) =
      μ.real {ω} * log (probEq μ (fun ω ↦ (f ω, g ω, h ω)) ω) +
        μ.real {ω} * log (probEq μ h ω) -
        μ.real {ω} * log (probEq μ (fun ω ↦ (f ω, h ω)) ω) -
        μ.real {ω} * log (probEq μ (fun ω ↦ (g ω, h ω)) ω) := by
    rcases eq_or_ne (μ.real {ω}) 0 with h0 | h0
    · simp [h0]
    rw [log_div (mul_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne'
      (mul_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne',
      log_mul (probEq_pos h0 _).ne' (probEq_pos h0 _).ne',
      log_mul (probEq_pos h0 _).ne' (probEq_pos h0 _).ne']
    ring
  simp only [condMutualInfoSum, entropy, key, sum_sub_distrib, sum_add_distrib]
  ring

end Formulas

section Sums

variable [Fintype Ω] [MeasurableSingletonClass Ω] [IsFiniteMeasure μ]

/-- The probability of a fiber is the sum of its point masses. -/
lemma measureReal_preimage_singleton_eq_sum [DecidableEq α] (f : Ω → α) (a : α) :
    μ.real (f ⁻¹' {a}) = ∑ ω, if f ω = a then μ.real {ω} else 0 := by
  rw [← sum_filter, sum_measureReal_singleton]
  congr 1
  ext
  simp

/-- Grouping the sample points by the value of a random variable. -/
lemma sum_measureReal_singleton_mul [Fintype α] (f : Ω → α) (φ : α → ℝ) :
    ∑ ω, μ.real {ω} * φ (f ω) = ∑ a, μ.real (f ⁻¹' {a}) * φ a := by
  classical
  simp_rw [measureReal_preimage_singleton_eq_sum, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

/-- The entropy is `H(f) = -∑_a P(f = a) log P(f = a)`. -/
theorem entropy_eq_neg_sum [Fintype α] (f : Ω → α) :
    entropy μ f = -∑ a, μ.real (f ⁻¹' {a}) * log (μ.real (f ⁻¹' {a})) := by
  rw [entropy, ← sum_measureReal_singleton_mul f fun a ↦ log (μ.real (f ⁻¹' {a}))]
  rfl

omit [Fintype Ω] in
/-- Marginalization: `∑_a P(f = a, h = c) = P(h = c)`. -/
lemma sum_measureReal_preimage_prod [Finite Ω] [Fintype α] (f : Ω → α) (h : Ω → γ) (c : γ) :
    ∑ a, μ.real ((fun ω ↦ (f ω, h ω)) ⁻¹' {(a, c)}) = μ.real (h ⁻¹' {c}) := by
  classical
  have := Fintype.ofFinite Ω
  simp_rw [measureReal_preimage_singleton_eq_sum, Prod.mk.injEq]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ ↦ ?_
  by_cases hc : h ω = c <;> simp [hc]

omit [Fintype Ω] in
/-- The fibers of a random variable partition the sample space. -/
lemma sum_measureReal_preimage [Finite Ω] [Fintype α] (f : Ω → α) :
    ∑ a, μ.real (f ⁻¹' {a}) = μ.real (Set.univ : Set Ω) := by
  rw [sum_measureReal_preimage_singleton _ fun _ _ ↦ .of_discrete]
  simp

end Sums

section Nonneg

variable [Fintype Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ]

private lemma condMutualInfoSum_nonneg_of_finite [Finite α] [Finite β] [Finite γ]
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) : 0 ≤ condMutualInfoSum μ f g h := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  set k : Ω → α × β × γ := fun ω ↦ (f ω, g ω, h ω)
  set A : α × γ → ℝ := fun t ↦ μ.real ((fun ω ↦ (f ω, h ω)) ⁻¹' {t})
  set B : β × γ → ℝ := fun t ↦ μ.real ((fun ω ↦ (g ω, h ω)) ⁻¹' {t})
  set C : γ → ℝ := fun c ↦ μ.real (h ⁻¹' {c})
  set K : α × β × γ → ℝ := fun t ↦ μ.real (k ⁻¹' {t})
  set φ : α × β × γ → ℝ := fun t ↦ A (t.1, t.2.2) * B (t.2.1, t.2.2) / (K t * C t.2.2)
  -- Termwise, `log x ≥ 1 - x⁻¹`.
  have h1 (ω : Ω) : μ.real {ω} * (1 - φ (k ω)) ≤ μ.real {ω} *
      log (probEq μ k ω * probEq μ h ω /
        (probEq μ (fun ω ↦ (f ω, h ω)) ω * probEq μ (fun ω ↦ (g ω, h ω)) ω)) := by
    rcases eq_or_ne (μ.real {ω}) 0 with h0 | h0
    · simp [h0]
    refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
    have hx := div_pos (mul_pos (probEq_pos h0 k) (probEq_pos h0 h))
      (mul_pos (probEq_pos h0 (fun ω ↦ (f ω, h ω))) (probEq_pos h0 (fun ω ↦ (g ω, h ω))))
    convert one_sub_inv_le_log_of_pos hx using 2
    rw [inv_div]
    rfl
  -- The sum of `μ{ω} φ (k ω)` is at most one.
  have hC (c : γ) : ∑ a, A (a, c) = C c := sum_measureReal_preimage_prod f h c
  have hC' (c : γ) : ∑ b, B (b, c) = C c := sum_measureReal_preimage_prod g h c
  have h2 : ∑ ω, μ.real {ω} * φ (k ω) ≤ 1 := by
    rw [sum_measureReal_singleton_mul k φ]
    calc ∑ t, K t * φ t ≤ ∑ t : α × β × γ, A (t.1, t.2.2) * B (t.2.1, t.2.2) / C t.2.2 := by
          refine sum_le_sum fun t _ ↦ ?_
          have hAB : 0 ≤ A (t.1, t.2.2) * B (t.2.1, t.2.2) / C t.2.2 := by positivity
          rcases eq_or_ne (K t) 0 with hK | hK
          · simpa [hK] using hAB
          · simp only [φ]
            rw [← mul_div_assoc, mul_div_mul_left _ _ hK]
      _ = ∑ c, (∑ a, A (a, c)) * (∑ b, B (b, c)) / C c := by
          simp_rw [Fintype.sum_prod_type, sum_mul_sum, sum_div]
          exact (sum_congr rfl fun a _ ↦ sum_comm).trans sum_comm
      _ = ∑ c, C c := by
          refine sum_congr rfl fun c _ ↦ ?_
          rw [hC, hC']
          rcases eq_or_ne (C c) 0 with h0 | h0
          · simp [h0]
          · field_simp
      _ = 1 := by simp [C, sum_measureReal_preimage]
  calc 0 ≤ 1 - ∑ ω, μ.real {ω} * φ (k ω) := by linarith
    _ = ∑ ω, μ.real {ω} * (1 - φ (k ω)) := by
        simp [mul_sub, sum_sub_distrib]
    _ ≤ condMutualInfoSum μ f g h := sum_le_sum fun ω _ ↦ h1 ω

/-- **Nonnegativity of conditional mutual information**: `0 ≤ I(f; g | h)`. -/
theorem condMutualInfoSum_nonneg (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    0 ≤ condMutualInfoSum μ f g h := by
  rw [condMutualInfoSum_congr (eq_iff_rangeFactorization_eq f) (eq_iff_rangeFactorization_eq g)
    (eq_iff_rangeFactorization_eq h)]
  exact condMutualInfoSum_nonneg_of_finite _ _ _

omit [MeasurableSingletonClass Ω] in
/-- The mutual information is the conditional mutual information given a constant. -/
lemma mutualInfoSum_eq_condMutualInfoSum_const (f : Ω → α) (g : Ω → β) (c : γ) :
    mutualInfoSum μ f g = condMutualInfoSum μ f g (fun _ ↦ c) := by
  rw [mutualInfoSum_eq_entropy, condMutualInfoSum_eq_entropy, entropy_const, sub_zero,
    entropy_congr (f := fun ω ↦ (f ω, c)) (g := f) (by simp),
    entropy_congr (f := fun ω ↦ (g ω, c)) (g := g) (by simp),
    entropy_congr (f := fun ω ↦ (f ω, g ω, c)) (g := fun ω ↦ (f ω, g ω)) (by simp)]

/-- **Nonnegativity of mutual information**: `0 ≤ I(f; g)`. -/
theorem mutualInfoSum_nonneg (f : Ω → α) (g : Ω → β) : 0 ≤ mutualInfoSum μ f g := by
  rw [mutualInfoSum_eq_condMutualInfoSum_const f g ()]
  exact condMutualInfoSum_nonneg _ _ _

end Nonneg

section ChainRule

variable [Fintype Ω] [IsFiniteMeasure μ]

/-- **Chain rule** for mutual information: `I(f; g, h) = I(f; h) + I(f; g | h)`. -/
theorem mutualInfoSum_prod (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    mutualInfoSum μ f (fun ω ↦ (g ω, h ω)) = mutualInfoSum μ f h + condMutualInfoSum μ f g h := by
  rw [mutualInfoSum_eq_entropy, mutualInfoSum_eq_entropy, condMutualInfoSum_eq_entropy]
  ring

/-- **Chain rule** for conditional mutual information:
`I(u, f; g | h) = I(f; g | h) + I(u; g | f, h)`. -/
theorem condMutualInfoSum_prod (u : Ω → δ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    condMutualInfoSum μ (fun ω ↦ (u ω, f ω)) g h =
      condMutualInfoSum μ f g h + condMutualInfoSum μ u g (fun ω ↦ (f ω, h ω)) := by
  simp only [condMutualInfoSum_eq_entropy]
  rw [entropy_congr (f := fun ω ↦ ((u ω, f ω), h ω)) (g := fun ω ↦ (u ω, f ω, h ω))
      fun _ _ ↦ by simp only [Prod.mk.injEq]; tauto,
    entropy_congr (f := fun ω ↦ (g ω, f ω, h ω)) (g := fun ω ↦ (f ω, g ω, h ω))
      fun _ _ ↦ by simp only [Prod.mk.injEq]; tauto,
    entropy_congr (f := fun ω ↦ ((u ω, f ω), g ω, h ω)) (g := fun ω ↦ (u ω, g ω, f ω, h ω))
      fun _ _ ↦ by simp only [Prod.mk.injEq]; tauto]
  ring

end ChainRule

section Past

variable {n : ℕ}

/-- The truncation `y^k = (y₀, …, y_{k-1})` of a sequence `y : Fin n → β` to its first `k ≤ n`
terms. -/
def trunc (y : Fin n → β) (k : ℕ) (hk : k ≤ n) : Fin k → β :=
  fun j ↦ y (Fin.castLE hk j)

/-- The past `Y^k = (Y₀, …, Y_{k-1})` of the first `k ≤ n` terms of a sequence of random variables
`Y : Fin n → Ω → β` (indices start at `0`). -/
def past (Y : Fin n → Ω → β) (k : ℕ) (hk : k ≤ n) (ω : Ω) : Fin k → β :=
  trunc (fun j ↦ Y j ω) k hk

/-- `y'^{i+1} = y^{i+1}` iff `y'_i = y_i` and `y'^i = y^i`. -/
lemma trunc_succ_eq_iff (y y' : Fin n → β) (i : Fin n) :
    trunc y' (i + 1) i.isLt = trunc y (i + 1) i.isLt ↔
      y' i = y i ∧ trunc y' i i.isLt.le = trunc y i i.isLt.le := by
  have : Fin.castLE i.isLt (Fin.last i) = i := Fin.ext (by simp)
  simp only [trunc, funext_iff, Fin.forall_fin_succ', Fin.castLE_castSucc, this]
  exact and_comm

omit [MeasurableSpace Ω] in
/-- The past of a sequence of random variables at `ω` is the truncation of its sample path. -/
lemma past_eq_trunc (Y : Fin n → Ω → β) (k : ℕ) (hk : k ≤ n) (ω : Ω) :
    past Y k hk ω = trunc (fun j ↦ Y j ω) k hk := rfl

omit [MeasurableSpace Ω] in
/-- `Y^{i+1}` takes the same value at two sample points iff `Y_i` and `Y^i` do. -/
lemma past_succ_eq_iff (Y : Fin n → Ω → β) (i : Fin n) (ω ω' : Ω) :
    past Y (i + 1) i.isLt ω' = past Y (i + 1) i.isLt ω ↔
      Y i ω' = Y i ω ∧ past Y i i.isLt.le ω' = past Y i i.isLt.le ω :=
  trunc_succ_eq_iff (fun j ↦ Y j ω) (fun j ↦ Y j ω') i

/-- Telescoping along the pasts of a sequence. -/
lemma sum_sub_past (F : (k : ℕ) → k ≤ n → ℝ) :
    ∑ i : Fin n, (F (i + 1) i.isLt - F i i.isLt.le) = F n le_rfl - F 0 (Nat.zero_le n) := by
  let G : ℕ → ℝ := fun k ↦ if hk : k ≤ n then F k hk else 0
  have hG (k : ℕ) (hk : k ≤ n) : F k hk = G k := by simp [G, hk]
  simp_rw [hG]
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ G (i + 1) - G i) n).trans (sum_range_sub G n)

omit [MeasurableSpace Ω] in
/-- The full past `Y^n` is the whole sequence. -/
lemma past_self (Y : Fin n → Ω → β) : past Y n le_rfl = fun ω j ↦ Y j ω := rfl

end Past

section SeqChainRule

variable [Fintype Ω] [IsProbabilityMeasure μ] {n : ℕ}

/-- A random variable with values in a subsingleton has zero entropy. -/
lemma entropy_of_subsingleton [Subsingleton α] (f : Ω → α) : entropy μ f = 0 := by
  rw [entropy_congr (g := fun _ ↦ ()) fun _ _ ↦ iff_of_true (Subsingleton.elim _ _) rfl,
    entropy_const]

omit [IsProbabilityMeasure μ] in
/-- Adjoining the empty past `Y^0` does not change the entropy. -/
lemma entropy_prod_past_zero (f : Ω → α) (Y : Fin n → Ω → β) (h : 0 ≤ n) :
    entropy μ (fun ω ↦ (f ω, past Y 0 h ω)) = entropy μ f :=
  entropy_congr fun ω ω' ↦ by
    simp only [Prod.mk.injEq, Subsingleton.elim (past Y 0 h ω') (past Y 0 h ω), and_true]

/-- **Chain rule** for mutual information along a sequence:
`I(f; Y^n) = ∑_i I(f; Y_i | Y^{i-1})`. -/
theorem mutualInfoSum_eq_sum_condMutualInfoSum (f : Ω → α) (Y : Fin n → Ω → β) :
    mutualInfoSum μ f (fun ω j ↦ Y j ω) =
      ∑ i : Fin n, condMutualInfoSum μ f (Y i) (past Y i i.isLt.le) := by
  have hterm (i : Fin n) : condMutualInfoSum μ f (Y i) (past Y i i.isLt.le) =
      (entropy μ (past Y (i + 1) i.isLt) - entropy μ (past Y i i.isLt.le)) -
      (entropy μ (fun ω ↦ (f ω, past Y (i + 1) i.isLt ω)) -
        entropy μ (fun ω ↦ (f ω, past Y i i.isLt.le ω))) := by
    rw [condMutualInfoSum_eq_entropy,
      entropy_congr (f := fun ω ↦ (Y i ω, past Y i i.isLt.le ω)) (g := past Y (i + 1) i.isLt)
        fun ω ω' ↦ by rw [past_succ_eq_iff, Prod.mk.injEq],
      entropy_congr (f := fun ω ↦ (f ω, Y i ω, past Y i i.isLt.le ω))
        (g := fun ω ↦ (f ω, past Y (i + 1) i.isLt ω))
        fun ω ω' ↦ by rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, past_succ_eq_iff]]
    ring
  have h1 := sum_sub_past fun k hk ↦ entropy μ (past Y k hk)
  have h2 := sum_sub_past fun k hk ↦ entropy μ (fun ω ↦ (f ω, past Y k hk ω))
  rw [sum_congr rfl fun i _ ↦ hterm i, sum_sub_distrib, h1, h2, mutualInfoSum_eq_entropy,
    entropy_of_subsingleton (past Y 0 _), entropy_prod_past_zero, past_self]
  ring

end SeqChainRule

section CondIndep

variable [Fintype Ω] [MeasurableSingletonClass Ω] [IsFiniteMeasure μ]

omit [MeasurableSingletonClass Ω] in
/-- If `P(f, g, h) P(h) = P(f, h) P(g, h)` on the support of `μ`, then `I(f; g | h) = 0`. -/
lemma condMutualInfoSum_eq_zero_of_forall_mul_eq {f : Ω → α} {g : Ω → β} {h : Ω → γ}
    (hfgh : ∀ ω, μ.real {ω} ≠ 0 → probEq μ (fun ω ↦ (f ω, g ω, h ω)) ω * probEq μ h ω =
      probEq μ (fun ω ↦ (f ω, h ω)) ω * probEq μ (fun ω ↦ (g ω, h ω)) ω) :
    condMutualInfoSum μ f g h = 0 := by
  refine sum_eq_zero fun ω _ ↦ ?_
  rcases eq_or_ne (μ.real {ω}) 0 with h0 | h0
  · simp [h0]
  rw [hfgh ω h0, div_self (mul_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne', log_one, mul_zero]

/-- **Conditional independence gives zero conditional mutual information**: if
`P(g = b | f = a, h = c) = P(g = b | h = c)` whenever `P(f = a, h = c) > 0`, then
`I(f; g | h) = 0`. -/
lemma condMutualInfoSum_eq_zero_of_cond_eq {f : Ω → α} {g : Ω → β} {h : Ω → γ}
    (hfgh : ∀ a b c, μ (f ⁻¹' {a} ∩ h ⁻¹' {c}) ≠ 0 →
      μ[g ⁻¹' {b} | f ⁻¹' {a} ∩ h ⁻¹' {c}] = μ[g ⁻¹' {b} | h ⁻¹' {c}]) :
    condMutualInfoSum μ f g h = 0 := by
  refine condMutualInfoSum_eq_zero_of_forall_mul_eq fun ω hω ↦ ?_
  set T := f ⁻¹' {f ω} ∩ h ⁻¹' {h ω}
  set T' := h ⁻¹' {h ω}
  set S := g ⁻¹' {g ω}
  have hne {U : Set Ω} (hU : ω ∈ U) : μ.real U ≠ 0 :=
    ((measureReal_nonneg.lt_of_ne (Ne.symm hω)).trans_le
      (measureReal_mono (Set.singleton_subset_iff.2 hU))).ne'
  have hT : μ.real T ≠ 0 := hne (by simp [T])
  have hT' : μ.real T' ≠ 0 := hne (by simp [T'])
  have key := congrArg ENNReal.toReal
    (hfgh (f ω) (g ω) (h ω) fun h0 ↦ hT (by simp [T, measureReal_def, h0]))
  simp only [cond_apply .of_discrete, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← measureReal_def] at key
  have e1 : probEq μ (fun ω ↦ (f ω, g ω, h ω)) ω = μ.real (T ∩ S) := by
    unfold probEq
    congr 1
    ext
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff, T, S]
    tauto
  have e2 : probEq μ (fun ω ↦ (f ω, h ω)) ω = μ.real T := by
    unfold probEq
    congr 1
    ext
    simp [T]
  have e3 : probEq μ (fun ω ↦ (g ω, h ω)) ω = μ.real (T' ∩ S) := by
    unfold probEq
    congr 1
    ext
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff, T', S]
    tauto
  change (μ.real T)⁻¹ * μ.real (T ∩ S) = (μ.real T')⁻¹ * μ.real (T' ∩ S) at key
  rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hT hT'] at key
  rw [e1, e2, e3, mul_comm (μ.real T)]
  exact key

omit [Fintype Ω] [MeasurableSingletonClass Ω] [IsFiniteMeasure μ] [MeasurableSpace Ω] in
/-- The level set of a pair of random variables is the intersection of their level sets. -/
lemma preimage_prodMk_singleton (f : Ω → α) (g : Ω → β) (t : α × β) :
    (fun ω ↦ (f ω, g ω)) ⁻¹' {t} = f ⁻¹' {t.1} ∩ g ⁻¹' {t.2} := by
  ext
  simp [Prod.ext_iff]

end CondIndep

end InformationTheory.DirectedInfo

namespace InformationTheory

open DirectedInfo

variable {Ω 𝓧 𝓨 𝓤 : Type*} [MeasurableSpace Ω] [Fintype Ω] {n : ℕ}

section Definitions

variable (μ : Measure Ω)

/-- Massey's **directed information** `I(X^n → Y^n) = ∑_{i=1}^n I(X^i; Y_i | Y^{i-1})` from a
sequence of random variables `X = (X₀, …, X_{n-1})` to `Y = (Y₀, …, Y_{n-1})`. With indices
starting at `0`, the `i`-th term is `I(X₀, …, X_i; Y_i | Y₀, …, Y_{i-1})`. -/
noncomputable def directedInfo (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) : ℝ :=
  ∑ i : Fin n, condMutualInfoSum μ (past X (i + 1) i.isLt) (Y i) (past Y i i.isLt.le)

/-- The directed information `I(0 ∗ Y^{n-1} → X^n) = ∑_{i=1}^n I(Y^{i-1}; X_i | X^{i-1})` from the
delayed sequence `0 ∗ Y^{n-1} = (0, Y₀, …, Y_{n-2})` to `X = (X₀, …, X_{n-1})`. With indices
starting at `0`, the `i`-th term is `I(Y₀, …, Y_{i-1}; X_i | X₀, …, X_{i-1})`. -/
noncomputable def delayedDirectedInfo (Y : Fin n → Ω → 𝓨) (X : Fin n → Ω → 𝓧) : ℝ :=
  ∑ i : Fin n, condMutualInfoSum μ (past Y i i.isLt.le) (X i) (past X i i.isLt.le)

end Definitions

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Directed information is nonnegative. -/
theorem directedInfo_nonneg [MeasurableSingletonClass Ω] (X : Fin n → Ω → 𝓧)
    (Y : Fin n → Ω → 𝓨) : 0 ≤ directedInfo μ X Y :=
  sum_nonneg fun _ _ ↦ condMutualInfoSum_nonneg _ _ _

/-- The delayed directed information is nonnegative. -/
theorem delayedDirectedInfo_nonneg [MeasurableSingletonClass Ω] (Y : Fin n → Ω → 𝓨)
    (X : Fin n → Ω → 𝓧) : 0 ≤ delayedDirectedInfo μ Y X :=
  sum_nonneg fun _ _ ↦ condMutualInfoSum_nonneg _ _ _

/-- **Conservation law of mutual and directed information** (Massey–Massey 2005):
`I(X^n; Y^n) = I(X^n → Y^n) + I(0 ∗ Y^{n-1} → X^n)`. -/
theorem mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo (X : Fin n → Ω → 𝓧)
    (Y : Fin n → Ω → 𝓨) :
    mutualInfoSum μ (fun ω j ↦ X j ω) (fun ω j ↦ Y j ω) =
      directedInfo μ X Y + delayedDirectedInfo μ Y X := by
  have hterm (i : Fin n) :
      condMutualInfoSum μ (past X (i + 1) i.isLt) (Y i) (past Y i i.isLt.le) +
        condMutualInfoSum μ (past Y i i.isLt.le) (X i) (past X i i.isLt.le) =
      (entropy μ (past Y (i + 1) i.isLt) - entropy μ (past Y i i.isLt.le)) +
        (entropy μ (past X (i + 1) i.isLt) - entropy μ (past X i i.isLt.le)) -
        (entropy μ (fun ω ↦ (past X (i + 1) i.isLt ω, past Y (i + 1) i.isLt ω)) -
          entropy μ (fun ω ↦ (past X i i.isLt.le ω, past Y i i.isLt.le ω))) := by
    rw [condMutualInfoSum_eq_entropy, condMutualInfoSum_eq_entropy,
      entropy_congr (f := fun ω ↦ (Y i ω, past Y i i.isLt.le ω)) (g := past Y (i + 1) i.isLt)
        fun ω ω' ↦ by simp only [Prod.mk.injEq, past_succ_eq_iff],
      entropy_congr (f := fun ω ↦ (past X (i + 1) i.isLt ω, Y i ω, past Y i i.isLt.le ω))
        (g := fun ω ↦ (past X (i + 1) i.isLt ω, past Y (i + 1) i.isLt ω))
        fun ω ω' ↦ by simp only [Prod.mk.injEq, past_succ_eq_iff],
      entropy_congr (f := fun ω ↦ (past Y i i.isLt.le ω, past X i i.isLt.le ω))
        (g := fun ω ↦ (past X i i.isLt.le ω, past Y i i.isLt.le ω))
        fun ω ω' ↦ by rw [Prod.mk.injEq, Prod.mk.injEq, and_comm],
      entropy_congr (f := fun ω ↦ (X i ω, past X i i.isLt.le ω)) (g := past X (i + 1) i.isLt)
        fun ω ω' ↦ by simp only [Prod.mk.injEq, past_succ_eq_iff],
      entropy_congr (f := fun ω ↦ (past Y i i.isLt.le ω, X i ω, past X i i.isLt.le ω))
        (g := fun ω ↦ (past X (i + 1) i.isLt ω, past Y i i.isLt.le ω))
        fun ω ω' ↦ by simp only [Prod.mk.injEq, past_succ_eq_iff]; tauto]
    ring
  have h1 := sum_sub_past fun k hk ↦ entropy μ (past Y k hk)
  have h2 := sum_sub_past fun k hk ↦ entropy μ (past X k hk)
  have h3 := sum_sub_past fun k hk ↦ entropy μ (fun ω ↦ (past X k hk ω, past Y k hk ω))
  rw [directedInfo, delayedDirectedInfo, ← sum_add_distrib, sum_congr rfl fun i _ ↦ hterm i,
    sum_sub_distrib, sum_add_distrib, h1, h2, h3, mutualInfoSum_eq_entropy,
    entropy_of_subsingleton (past Y 0 _), entropy_of_subsingleton (past X 0 _),
    entropy_of_subsingleton (fun ω ↦ (past X 0 _ ω, past Y 0 _ ω)), past_self, past_self]
  ring

section Massey

variable [MeasurableSingletonClass Ω]

/-- **Massey (1990), Theorem 1, inequality**: `I(X^n → Y^n) ≤ I(X^n; Y^n)`. -/
theorem directedInfo_le_mutualInfoSum (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) :
    directedInfo μ X Y ≤ mutualInfoSum μ (fun ω j ↦ X j ω) (fun ω j ↦ Y j ω) := by
  rw [mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo]
  linarith [delayedDirectedInfo_nonneg (μ := μ) Y X]

variable (μ) in
/-- Massey's condition (2) for a channel with input `X` and output `Y` to be **used without
feedback**: `P(x_i | x^{i-1}, y^{i-1}) = P(x_i | x^{i-1})` for every time `i`, all `x^i` and all
`y^{i-1}` with `P(x^{i-1}, y^{i-1}) > 0` (the conditional probabilities being defined only
there). -/
def IsWithoutFeedback (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) : Prop :=
  ∀ (i : Fin n) (x : Fin i → 𝓧) (y : Fin i → 𝓨) (a : 𝓧),
    μ (past X i i.isLt.le ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y}) ≠ 0 →
      μ[X i ⁻¹' {a} | past X i i.isLt.le ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y}] =
        μ[X i ⁻¹' {a} | past X i i.isLt.le ⁻¹' {x}]

/-- Without feedback, no information flows from the delayed output to the input:
`I(0 ∗ Y^{n-1} → X^n) = 0`. -/
theorem delayedDirectedInfo_eq_zero_of_isWithoutFeedback {X : Fin n → Ω → 𝓧}
    {Y : Fin n → Ω → 𝓨} (h : IsWithoutFeedback μ X Y) : delayedDirectedInfo μ Y X = 0 := by
  refine sum_eq_zero fun i _ ↦ condMutualInfoSum_eq_zero_of_cond_eq fun y a x hne ↦ ?_
  rw [Set.inter_comm] at hne ⊢
  exact h i x y a hne

/-- **Massey (1990), Theorem 1, equality case**: if the channel is used without feedback, then
`I(X^n → Y^n) = I(X^n; Y^n)`. -/
theorem directedInfo_eq_mutualInfoSum_of_isWithoutFeedback {X : Fin n → Ω → 𝓧}
    {Y : Fin n → Ω → 𝓨} (h : IsWithoutFeedback μ X Y) :
    directedInfo μ X Y = mutualInfoSum μ (fun ω j ↦ X j ω) (fun ω j ↦ Y j ω) := by
  rw [mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo,
    delayedDirectedInfo_eq_zero_of_isWithoutFeedback h, add_zero]

variable (μ) in
/-- Massey's condition (8) for a **causal system**: given the current and past channel inputs
`x^i` and the past channel outputs `y^{i-1}`, the channel output `Y_i` is conditionally
independent of the source output `U`, i.e. `P(y_i | x^i, y^{i-1}, u) = P(y_i | x^i, y^{i-1})`
whenever `P(x^i, y^{i-1}, u) > 0`. -/
def IsCausal (U : Ω → 𝓤) (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) : Prop :=
  ∀ (i : Fin n) (u : 𝓤) (x : Fin (i + 1) → 𝓧) (y : Fin i → 𝓨) (b : 𝓨),
    μ (U ⁻¹' {u} ∩ (past X (i + 1) i.isLt ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y})) ≠ 0 →
      μ[Y i ⁻¹' {b} | U ⁻¹' {u} ∩ (past X (i + 1) i.isLt ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y})] =
        μ[Y i ⁻¹' {b} | past X (i + 1) i.isLt ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y}]

/-- **Massey (1990), Theorem 3**: in a causal system, the information that the channel output
sequence gives about the source output is at most the directed information from the channel
input to the channel output, `I(U; Y^n) ≤ I(X^n → Y^n)`. Since the sample space is finite, the
source output `U` (Massey's `U^K`) is finite-valued here, whereas the paper allows any discrete
source output. -/
theorem mutualInfoSum_le_directedInfo_of_isCausal {U : Ω → 𝓤} {X : Fin n → Ω → 𝓧}
    {Y : Fin n → Ω → 𝓨} (h : IsCausal μ U X Y) :
    mutualInfoSum μ U (fun ω j ↦ Y j ω) ≤ directedInfo μ X Y := by
  rw [mutualInfoSum_eq_sum_condMutualInfoSum, directedInfo]
  refine sum_le_sum fun i _ ↦ ?_
  set Xi := past X (i + 1) i.isLt
  set Yi := past Y i i.isLt.le
  have h1 := condMutualInfoSum_prod (μ := μ) U Xi (Y i) Yi
  have h2 := condMutualInfoSum_prod (μ := μ) Xi U (Y i) Yi
  have h3 : condMutualInfoSum μ (fun ω ↦ (U ω, Xi ω)) (Y i) Yi =
      condMutualInfoSum μ (fun ω ↦ (Xi ω, U ω)) (Y i) Yi :=
    condMutualInfoSum_congr (fun _ _ ↦ by simp only [Prod.mk.injEq]; tauto)
      (fun _ _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl
  have h4 : condMutualInfoSum μ U (Y i) (fun ω ↦ (Xi ω, Yi ω)) = 0 := by
    refine condMutualInfoSum_eq_zero_of_cond_eq fun u b xy hne ↦ ?_
    rw [preimage_prodMk_singleton] at hne ⊢
    exact h i u xy.1 xy.2 b hne
  have h5 := condMutualInfoSum_nonneg (μ := μ) Xi (Y i) (fun ω ↦ (U ω, Yi ω))
  linarith

variable (μ) in
/-- Massey's condition (1) for a **discrete memoryless channel**:
`P(y_i | x^i, y^{i-1}) = P(y_i | x_i)` for every time `i`, all `x^i = (x^{i-1}, x_i)`, `y^{i-1}`
with `P(x^i, y^{i-1}) > 0`, and all `y_i`. -/
def IsMemoryless (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) : Prop :=
  ∀ (i : Fin n) (x : Fin i → 𝓧) (y : Fin i → 𝓨) (a : 𝓧) (b : 𝓨),
    μ ((past X i i.isLt.le ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y}) ∩ X i ⁻¹' {a}) ≠ 0 →
      μ[Y i ⁻¹' {b} | (past X i i.isLt.le ⁻¹' {x} ∩ past Y i i.isLt.le ⁻¹' {y}) ∩ X i ⁻¹' {a}] =
        μ[Y i ⁻¹' {b} | X i ⁻¹' {a}]

/-- Under memorylessness, `I(X^n → Y^n) = ∑_i (I(X_i; Y_i) - I(Y^{i-1}; Y_i))`; this is the
identity `I(X^n → Y^n) = H(Y^n) - ∑_i H(Y_i | X_i)` in the proof of Massey (1990), Theorem 2,
written with mutual informations. -/
theorem directedInfo_eq_sum_sub_of_isMemoryless {X : Fin n → Ω → 𝓧} {Y : Fin n → Ω → 𝓨}
    (h : IsMemoryless μ X Y) :
    directedInfo μ X Y = ∑ i : Fin n,
      (mutualInfoSum μ (X i) (Y i) - mutualInfoSum μ (past Y i i.isLt.le) (Y i)) := by
  refine sum_congr rfl fun i _ ↦ ?_
  set Xi := past X i i.isLt.le
  set Yi := past Y i i.isLt.le
  -- Memorylessness: `I(X^{i-1}, Y^{i-1}; Y_i | X_i) = 0`.
  have h0 : condMutualInfoSum μ (fun ω ↦ (Xi ω, Yi ω)) (Y i) (X i) = 0 := by
    refine condMutualInfoSum_eq_zero_of_cond_eq fun xy b a hne ↦ ?_
    rw [preimage_prodMk_singleton] at hne ⊢
    exact h i xy.1 xy.2 a b hne
  rw [condMutualInfoSum_eq_entropy] at h0 ⊢
  rw [mutualInfoSum_eq_entropy, mutualInfoSum_eq_entropy]
  rw [entropy_congr (f := fun ω ↦ ((Xi ω, Yi ω), X i ω))
      (g := fun ω ↦ (past X (i + 1) i.isLt ω, Yi ω))
      fun ω ω' ↦ by simp only [Prod.mk.injEq, past_succ_eq_iff, Xi, Yi]; tauto,
    entropy_congr (f := fun ω ↦ ((Xi ω, Yi ω), Y i ω, X i ω))
      (g := fun ω ↦ (past X (i + 1) i.isLt ω, Y i ω, Yi ω))
      fun ω ω' ↦ by simp only [Prod.mk.injEq, past_succ_eq_iff, Xi, Yi]; tauto,
    entropy_congr (f := fun ω ↦ (Y i ω, X i ω)) (g := fun ω ↦ (X i ω, Y i ω))
      fun ω ω' ↦ by simp only [Prod.mk.injEq]; tauto] at h0
  rw [entropy_congr (f := fun ω ↦ (Yi ω, Y i ω)) (g := fun ω ↦ (Y i ω, Yi ω))
      fun ω ω' ↦ by simp only [Prod.mk.injEq]; tauto]
  linarith

/-- **Massey (1990), Theorem 2, inequality**: for a discrete memoryless channel (possibly used
with feedback), `I(X^n → Y^n) ≤ ∑_i I(X_i; Y_i)`. -/
theorem directedInfo_le_sum_mutualInfoSum_of_isMemoryless {X : Fin n → Ω → 𝓧}
    {Y : Fin n → Ω → 𝓨} (h : IsMemoryless μ X Y) :
    directedInfo μ X Y ≤ ∑ i : Fin n, mutualInfoSum μ (X i) (Y i) := by
  rw [directedInfo_eq_sum_sub_of_isMemoryless h]
  exact sum_le_sum fun i _ ↦ sub_le_self _ (mutualInfoSum_nonneg _ _)

end Massey

section CausalConditioning

/-! ### Causal conditioning -/

variable [MeasurableSingletonClass Ω]

variable (μ) in
/-- The **causal conditioning** `P(y^n ‖ x^n) = ∏_{i=1}^n P(y_i | x^i, y^{i-1})` (Kramer; Massey
(1990), right-hand side of (4)), evaluated at the sequences `y` and `x`. -/
noncomputable def causalCond (Y : Fin n → Ω → 𝓨) (X : Fin n → Ω → 𝓧) (y : Fin n → 𝓨)
    (x : Fin n → 𝓧) : ℝ≥0∞ :=
  ∏ i : Fin n, μ[Y i ⁻¹' {y i} | past X (i + 1) i.isLt ⁻¹' {trunc x (i + 1) i.isLt} ∩
    past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le}]

variable (μ) in
/-- The **delayed causal conditioning** `P(x^n ‖ y^{n-1}) = ∏_{i=1}^n P(x_i | x^{i-1}, y^{i-1})`
(Kramer; Massey–Massey (2005)), evaluated at the sequences `x` and `y`. -/
noncomputable def causalCondDelayed (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) (x : Fin n → 𝓧)
    (y : Fin n → 𝓨) : ℝ≥0∞ :=
  ∏ i : Fin n, μ[X i ⁻¹' {x i} | past X i i.isLt.le ⁻¹' {trunc x i i.isLt.le} ∩
    past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le}]

omit [Fintype Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ] in
private lemma prod_range_inv_mul (e : ℕ → ℝ≥0∞) (he0 : e 0 = 1) (he : ∀ k, e (k + 1) ≤ e k)
    (htop : ∀ k, e k ≠ ∞) (m : ℕ) : ∏ k ∈ range m, (e k)⁻¹ * e (k + 1) = e m := by
  induction m with
  | zero => simp [he0]
  | succ m ih =>
    rw [prod_range_succ, ih, ENNReal.mul_inv_cancel_left'
      (fun h0 ↦ le_antisymm (h0 ▸ he m) bot_le) fun h ↦ absurd h (htop m)]

omit [Fintype Ω] in
/-- **Factorization of the joint law by causal conditioning** (Massey (1990), eq. (3)):
`P(x^n, y^n) = ∏_i P(x_i | x^{i-1}, y^{i-1}) P(y_i | x^i, y^{i-1}) = P(x^n ‖ y^{n-1}) P(y^n ‖ x^n)`.
With Mathlib's convention `P(· | B) = 0` when `P(B) = 0`, it holds at every pair of sequences. -/
theorem measure_preimage_eq_causalCondDelayed_mul_causalCond [Finite Ω] (X : Fin n → Ω → 𝓧)
    (Y : Fin n → Ω → 𝓨) (x : Fin n → 𝓧) (y : Fin n → 𝓨) :
    μ ((fun ω j ↦ X j ω) ⁻¹' {x} ∩ (fun ω j ↦ Y j ω) ⁻¹' {y}) =
      causalCondDelayed μ X Y x y * causalCond μ Y X y x := by
  let E (k : ℕ) (hk : k ≤ n) : Set Ω :=
    past X k hk ⁻¹' {trunc x k hk} ∩ past Y k hk ⁻¹' {trunc y k hk}
  let e : ℕ → ℝ≥0∞ := fun k ↦ if hk : k ≤ n then μ (E k hk) else 0
  have heE (k : ℕ) (hk : k ≤ n) : e k = μ (E k hk) := by simp [e, hk]
  have hF (i : Fin n) : past X (i + 1) i.isLt ⁻¹' {trunc x (i + 1) i.isLt} ∩
      past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le} = E i i.isLt.le ∩ X i ⁻¹' {x i} := by
    ext ω
    simp only [E, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, past_eq_trunc,
      trunc_succ_eq_iff]
    tauto
  have hE (i : Fin n) : E i i.isLt.le ∩ X i ⁻¹' {x i} ∩ Y i ⁻¹' {y i} = E (i + 1) i.isLt := by
    ext ω
    simp only [E, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, past_eq_trunc,
      trunc_succ_eq_iff]
    tauto
  have hfactor (i : Fin n) : μ[X i ⁻¹' {x i} | E i i.isLt.le] *
      μ[Y i ⁻¹' {y i} | past X (i + 1) i.isLt ⁻¹' {trunc x (i + 1) i.isLt} ∩
        past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le}] = (e i)⁻¹ * e (i + 1) := by
    rw [hF, cond_apply .of_discrete, cond_apply .of_discrete, hE, heE i i.isLt.le,
      heE (i + 1) i.isLt, mul_assoc, ENNReal.mul_inv_cancel_left'
        (fun h0 ↦ measure_mono_null (hE i ▸ Set.inter_subset_left) h0)
        fun h ↦ absurd h (measure_ne_top _ _)]
  have he0 : e 0 = 1 := by
    rw [heE 0 (Nat.zero_le n)]
    convert measure_univ (μ := μ)
    ext ω
    simp [E, Subsingleton.elim (past X 0 _ ω) (trunc x 0 _),
      Subsingleton.elim (past Y 0 _ ω) (trunc y 0 _)]
  have he (k : ℕ) : e (k + 1) ≤ e k := by
    by_cases hk : k + 1 ≤ n
    · rw [heE (k + 1) hk, heE k (Nat.le_of_succ_le hk), ← hE ⟨k, hk⟩]
      exact measure_mono (Set.inter_subset_left.trans Set.inter_subset_left)
    · simp [e, hk]
  have htop (k : ℕ) : e k ≠ ∞ := by
    by_cases hk : k ≤ n
    · rw [heE k hk]
      exact measure_ne_top _ _
    · simp [e, hk]
  rw [causalCondDelayed, causalCond, ← prod_mul_distrib]
  simp_rw [show ∀ i : Fin n, past X i i.isLt.le ⁻¹' {trunc x i i.isLt.le} ∩
    past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le} = E i i.isLt.le from fun _ ↦ rfl, hfactor]
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ (e i)⁻¹ * e (i + 1)), prod_range_inv_mul e he0 he htop,
    heE n le_rfl]
  rfl

omit [Fintype Ω] in
/-- Chain rule of conditional probabilities for one sequence: `∏_i P(x_i | x^{i-1}) = P(x^n)`. -/
private lemma prod_cond_past_eq [Finite Ω] (X : Fin n → Ω → 𝓧) (x : Fin n → 𝓧) :
    ∏ i : Fin n, μ[X i ⁻¹' {x i} | past X i i.isLt.le ⁻¹' {trunc x i i.isLt.le}] =
      μ ((fun ω j ↦ X j ω) ⁻¹' {x}) := by
  let E (k : ℕ) (hk : k ≤ n) : Set Ω := past X k hk ⁻¹' {trunc x k hk}
  let e : ℕ → ℝ≥0∞ := fun k ↦ if hk : k ≤ n then μ (E k hk) else 0
  have heE (k : ℕ) (hk : k ≤ n) : e k = μ (E k hk) := by simp [e, hk]
  have hE (i : Fin n) : E i i.isLt.le ∩ X i ⁻¹' {x i} = E (i + 1) i.isLt := by
    ext ω
    simp only [E, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, past_eq_trunc,
      trunc_succ_eq_iff]
    tauto
  have hfactor (i : Fin n) : μ[X i ⁻¹' {x i} | E i i.isLt.le] = (e i)⁻¹ * e (i + 1) := by
    rw [cond_apply .of_discrete, hE, heE i i.isLt.le, heE (i + 1) i.isLt]
  have he0 : e 0 = 1 := by
    rw [heE 0 (Nat.zero_le n)]
    convert measure_univ (μ := μ)
    ext ω
    simp [E, Subsingleton.elim (past X 0 _ ω) (trunc x 0 _)]
  have he (k : ℕ) : e (k + 1) ≤ e k := by
    by_cases hk : k + 1 ≤ n
    · rw [heE (k + 1) hk, heE k (Nat.le_of_succ_le hk), ← hE ⟨k, hk⟩]
      exact measure_mono Set.inter_subset_left
    · simp [e, hk]
  have htop (k : ℕ) : e k ≠ ∞ := by
    by_cases hk : k ≤ n
    · rw [heE k hk]
      exact measure_ne_top _ _
    · simp [e, hk]
  simp_rw [show ∀ i : Fin n, past X i i.isLt.le ⁻¹' {trunc x i i.isLt.le} = E i i.isLt.le
    from fun _ ↦ rfl, hfactor]
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ (e i)⁻¹ * e (i + 1)), prod_range_inv_mul e he0 he htop,
    heE n le_rfl]
  rfl

omit [Fintype Ω] in
/-- Without feedback, the joint law factors as `P(x^n, y^n) = P(x^n) P(y^n ‖ x^n)`. -/
theorem measure_preimage_eq_mul_causalCond_of_isWithoutFeedback [Finite Ω]
    {X : Fin n → Ω → 𝓧} {Y : Fin n → Ω → 𝓨} (h : IsWithoutFeedback μ X Y) (x : Fin n → 𝓧)
    (y : Fin n → 𝓨) :
    μ ((fun ω j ↦ X j ω) ⁻¹' {x} ∩ (fun ω j ↦ Y j ω) ⁻¹' {y}) =
      μ ((fun ω j ↦ X j ω) ⁻¹' {x}) * causalCond μ Y X y x := by
  rw [measure_preimage_eq_causalCondDelayed_mul_causalCond]
  rcases eq_or_ne (causalCond μ Y X y x) 0 with hC | hC
  · rw [hC, mul_zero, mul_zero]
  congr 1
  rw [causalCondDelayed, ← prod_cond_past_eq X x]
  refine prod_congr rfl fun i _ ↦ ?_
  -- Every history `(x^i, y^i)` has positive probability, since `P(y^n ‖ x^n) ≠ 0`.
  have hF : μ (past X (i + 1) i.isLt ⁻¹' {trunc x (i + 1) i.isLt} ∩
      past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le}) ≠ 0 := fun h0 ↦
    hC (prod_eq_zero (mem_univ i) (by simp [cond_eq_zero_of_meas_eq_zero h0]))
  have hsub : past X (i + 1) i.isLt ⁻¹' {trunc x (i + 1) i.isLt} ∩
      past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le} ⊆
      past X i i.isLt.le ⁻¹' {trunc x i i.isLt.le} ∩
        past Y i i.isLt.le ⁻¹' {trunc y i i.isLt.le} := by
    intro ω hω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, past_eq_trunc,
      trunc_succ_eq_iff] at hω ⊢
    tauto
  exact h i _ _ (x i) fun h0 ↦ hF (measure_mono_null hsub h0)

omit [Fintype Ω] in
/-- **Massey (1990), eq. (4)**: if the channel is used without feedback, then
`P(y^n | x^n) = ∏_i P(y_i | x^i, y^{i-1}) = P(y^n ‖ x^n)` for every input sequence `x^n` with
`P(x^n) > 0`. -/
theorem cond_eq_causalCond_of_isWithoutFeedback [Finite Ω] {X : Fin n → Ω → 𝓧}
    {Y : Fin n → Ω → 𝓨} (h : IsWithoutFeedback μ X Y) (x : Fin n → 𝓧) (y : Fin n → 𝓨)
    (hx : μ ((fun ω j ↦ X j ω) ⁻¹' {x}) ≠ 0) :
    μ[(fun ω j ↦ Y j ω) ⁻¹' {y} | (fun ω j ↦ X j ω) ⁻¹' {x}] = causalCond μ Y X y x := by
  rw [cond_apply .of_discrete, measure_preimage_eq_mul_causalCond_of_isWithoutFeedback h,
    ENNReal.inv_mul_cancel_left hx (measure_ne_top _ _)]

omit [Fintype Ω] [IsProbabilityMeasure μ] in
private lemma toReal_cond_preimage_eq [Finite Ω] (X : Fin n → Ω → 𝓧)
    (Y : Fin n → Ω → 𝓨) (i : Fin n) (ω : Ω) :
    (μ[Y i ⁻¹' {Y i ω} | past X (i + 1) i.isLt ⁻¹' {trunc (fun j ↦ X j ω) (i + 1) i.isLt} ∩
      past Y i i.isLt.le ⁻¹' {trunc (fun j ↦ Y j ω) i i.isLt.le}]).toReal =
      probEq μ (fun ω ↦ (past X (i + 1) i.isLt ω, Y i ω, past Y i i.isLt.le ω)) ω /
        probEq μ (fun ω ↦ (past X (i + 1) i.isLt ω, past Y i i.isLt.le ω)) ω := by
  rw [cond_apply .of_discrete, ENNReal.toReal_mul, ENNReal.toReal_inv, inv_mul_eq_div]
  simp only [← measureReal_def, probEq]
  congr 2
  · ext ω'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      past_eq_trunc]
    tauto
  · rw [preimage_prodMk_singleton]
    rfl

/-- **Directed information through causal conditioning** (Kramer; Massey–Massey (2005)):
`I(X^n → Y^n) = E[log (P(Y^n ‖ X^n) / P(Y^n))]`. -/
theorem directedInfo_eq_sum_log_causalCond (X : Fin n → Ω → 𝓧) (Y : Fin n → Ω → 𝓨) :
    directedInfo μ X Y = ∑ ω, μ.real {ω} *
      log ((causalCond μ Y X (fun j ↦ Y j ω) (fun j ↦ X j ω)).toReal /
        probEq μ (fun ω j ↦ Y j ω) ω) := by
  rw [directedInfo]
  unfold condMutualInfoSum
  rw [sum_comm]
  refine sum_congr rfl fun ω _ ↦ ?_
  rw [← mul_sum]
  rcases eq_or_ne (μ.real {ω}) 0 with h0 | h0
  · simp [h0]
  congr 1
  -- The causal conditioning, factor by factor.
  have hc : (causalCond μ Y X (fun j ↦ Y j ω) (fun j ↦ X j ω)).toReal =
      ∏ i : Fin n, probEq μ (fun ω ↦ (past X (i + 1) i.isLt ω, Y i ω, past Y i i.isLt.le ω)) ω /
        probEq μ (fun ω ↦ (past X (i + 1) i.isLt ω, past Y i i.isLt.le ω)) ω := by
    rw [causalCond, ENNReal.toReal_prod]
    exact prod_congr rfl fun i _ ↦ toReal_cond_preimage_eq X Y i ω
  have hc_pos : 0 < (causalCond μ Y X (fun j ↦ Y j ω) (fun j ↦ X j ω)).toReal := by
    rw [hc]
    exact prod_pos fun i _ ↦ div_pos (probEq_pos h0 _) (probEq_pos h0 _)
  have hcausal : log (causalCond μ Y X (fun j ↦ Y j ω) (fun j ↦ X j ω)).toReal =
      ∑ i : Fin n, (log (probEq μ (fun ω ↦ (past X (i + 1) i.isLt ω, Y i ω,
        past Y i i.isLt.le ω)) ω) -
        log (probEq μ (fun ω ↦ (past X (i + 1) i.isLt ω, past Y i i.isLt.le ω)) ω)) := by
    rw [hc, log_prod]
    · exact sum_congr rfl fun i _ ↦ log_div (probEq_pos h0 _).ne' (probEq_pos h0 _).ne'
    · exact fun i _ ↦ (div_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne'
  -- The output law, by telescoping.
  have hout : log (probEq μ (fun ω j ↦ Y j ω) ω) = ∑ i : Fin n,
      (log (probEq μ (fun ω ↦ (Y i ω, past Y i i.isLt.le ω)) ω) -
        log (probEq μ (past Y i i.isLt.le) ω)) := by
    have h := sum_sub_past fun k hk ↦ log (probEq μ (past Y k hk) ω)
    have h0' : probEq μ (past Y 0 (Nat.zero_le n)) ω = 1 := by
      rw [probEq_congr (g := fun _ ↦ ()) fun _ ↦ iff_of_true (Subsingleton.elim _ _) rfl]
      simp [probEq]
    rw [h0', log_one, sub_zero, past_self] at h
    rw [← h]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [probEq_congr (f := fun ω ↦ (Y i ω, past Y i i.isLt.le ω)) (g := past Y (i + 1) i.isLt)
      fun ω' ↦ by rw [past_succ_eq_iff, Prod.mk.injEq]]
  rw [log_div hc_pos.ne' (probEq_pos h0 _).ne', hcausal, hout, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [log_div (mul_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne'
      (mul_pos (probEq_pos h0 _) (probEq_pos h0 _)).ne',
    log_mul (probEq_pos h0 _).ne' (probEq_pos h0 _).ne',
    log_mul (probEq_pos h0 _).ne' (probEq_pos h0 _).ne']
  ring

end CausalConditioning

section Statlib

/-! ### Agreement with Statlib's mutual information -/

variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [Fintype Ω] [IsProbabilityMeasure μ] in
/-- On finite alphabets, Statlib's mutual information `mutualInfo ρ = KL(ρ, ρ₁ × ρ₂)` of a joint
law `ρ` of `(X, Y)` is the finite-sum mutual information `mutualInfoSum ρ Prod.fst Prod.snd`. -/
theorem DirectedInfo.mutualInfo_eq_ofReal_mutualInfoSum (ρ : Measure (α × β))
    [IsProbabilityMeasure ρ] :
    mutualInfo ρ = ENNReal.ofReal (mutualInfoSum ρ Prod.fst Prod.snd) := by
  have hprod (z : α × β) : (ρ.fst.prod ρ.snd) {z} = ρ.fst {z.1} * ρ.snd {z.2} := by
    rw [← Measure.prod_prod, Set.singleton_prod_singleton]
  have hfst (z : α × β) : ρ.fst {z.1} = ρ (Prod.fst ⁻¹' {z.1}) := Measure.fst_apply .of_discrete
  have hsnd (z : α × β) : ρ.snd {z.2} = ρ (Prod.snd ⁻¹' {z.2}) := Measure.snd_apply .of_discrete
  have hac : ρ ≪ ρ.fst.prod ρ.snd := fun s hs ↦ by
    rw [measure_eq_zero_iff_ae_notMem, ae_iff_of_countable] at hs ⊢
    intro z hz hzs
    refine hs z (fun hν ↦ hz ?_) hzs
    rw [hprod, hfst, hsnd, mul_eq_zero] at hν
    rcases hν with hν | hν <;> exact measure_mono_null (by simp) hν
  have hsum : klDivSum (fun z ↦ ρ.real {z}) (fun z ↦ (ρ.fst.prod ρ.snd).real {z}) =
      mutualInfoSum ρ Prod.fst Prod.snd := by
    refine sum_congr rfl fun z _ ↦ ?_
    simp only [probEq, measureReal_def, hprod, hfst, hsnd, ENNReal.toReal_mul]
    rfl
  rw [mutualInfo, klDiv_eq_ofReal_klDivSum hac, hsum]

omit [Fintype Ω] [IsProbabilityMeasure μ] [Fintype α] [Fintype β] in
/-- On finite alphabets, Statlib's mutual information of a joint law is finite. -/
theorem DirectedInfo.mutualInfo_ne_top [Finite α] [Finite β] (ρ : Measure (α × β))
    [IsProbabilityMeasure ρ] : mutualInfo ρ ≠ ∞ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [DirectedInfo.mutualInfo_eq_ofReal_mutualInfoSum]
  exact ENNReal.ofReal_ne_top

omit [Fintype Ω] [IsProbabilityMeasure μ] in
/-- Real-valued form of `DirectedInfo.mutualInfo_eq_ofReal_mutualInfoSum`. -/
theorem DirectedInfo.toReal_mutualInfo_eq_mutualInfoSum (ρ : Measure (α × β))
    [IsProbabilityMeasure ρ] :
    (mutualInfo ρ).toReal = mutualInfoSum ρ Prod.fst Prod.snd := by
  rw [DirectedInfo.mutualInfo_eq_ofReal_mutualInfoSum,
    ENNReal.toReal_ofReal (mutualInfoSum_nonneg _ _)]


end Statlib

section Canonical

/-! ### The joint law of `(X^n, Y^n)` -/

variable [Fintype 𝓧] [Fintype 𝓨] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
  [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓨]
  (ρ : Measure ((Fin n → 𝓧) × (Fin n → 𝓨))) [IsProbabilityMeasure ρ]

/-- **Conservation law of mutual and directed information** (Massey–Massey 2005) for a joint law
`ρ` of `(X^n, Y^n)`, with Statlib's mutual information `I(X^n; Y^n) = KL(ρ, ρ₁ × ρ₂)`:
`I(X^n; Y^n) = I(X^n → Y^n) + I(0 ∗ Y^{n-1} → X^n)`. -/
theorem toReal_mutualInfo_eq_directedInfo_add_delayedDirectedInfo :
    (mutualInfo ρ).toReal = directedInfo ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) +
      delayedDirectedInfo ρ (fun i z ↦ z.2 i) (fun i z ↦ z.1 i) := by
  rw [toReal_mutualInfo_eq_mutualInfoSum]
  exact mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo _ _

/-- **Conservation law of mutual and directed information** (Massey–Massey 2005) for a joint law
`ρ` of `(X^n, Y^n)`, in `ℝ≥0∞` with Statlib's mutual information:
`I(X^n; Y^n) = I(X^n → Y^n) + I(0 ∗ Y^{n-1} → X^n)`. -/
theorem mutualInfo_eq_ofReal_directedInfo_add_ofReal_delayedDirectedInfo :
    mutualInfo ρ = ENNReal.ofReal (directedInfo ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i)) +
      ENNReal.ofReal (delayedDirectedInfo ρ (fun i z ↦ z.2 i) (fun i z ↦ z.1 i)) := by
  rw [DirectedInfo.mutualInfo_eq_ofReal_mutualInfoSum,
    ← ENNReal.ofReal_add (directedInfo_nonneg _ _) (delayedDirectedInfo_nonneg _ _)]
  exact congrArg ENNReal.ofReal (mutualInfoSum_eq_directedInfo_add_delayedDirectedInfo _ _)

/-- **Massey (1990), Theorem 1, inequality**, for a joint law `ρ` of `(X^n, Y^n)` and Statlib's
mutual information: `I(X^n → Y^n) ≤ I(X^n; Y^n)`. -/
theorem directedInfo_le_toReal_mutualInfo :
    directedInfo ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) ≤ (mutualInfo ρ).toReal := by
  rw [toReal_mutualInfo_eq_mutualInfoSum]
  exact directedInfo_le_mutualInfoSum _ _

/-- **Massey (1990), Theorem 1, equality case**, for a joint law `ρ` of `(X^n, Y^n)` and
Statlib's mutual information: without feedback, `I(X^n → Y^n) = I(X^n; Y^n)`. -/
theorem directedInfo_eq_toReal_mutualInfo_of_isWithoutFeedback
    (h : IsWithoutFeedback ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i)) :
    directedInfo ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) = (mutualInfo ρ).toReal := by
  rw [toReal_mutualInfo_eq_mutualInfoSum]
  exact directedInfo_eq_mutualInfoSum_of_isWithoutFeedback h

/-- **Directed information as a Kullback–Leibler sum** (Kramer; Massey–Massey (2005)): for a joint
law `ρ` of `(X^n, Y^n)`, `I(X^n → Y^n) = ∑_{x, y} P(x, y) log (P(x, y) / q(x, y))` with
`q(x, y) = P(x^n ‖ y^{n-1}) P(y^n)`, written as the finite sum `klDivSum`.

With Mathlib's convention `μ[t | s] = 0` for `μ s = 0`, this `q` vanishes on histories of
probability zero and is only sub-normalized in general; it agrees on the support of `ρ` (the only
points where `klDivSum` evaluates it) with the `q` built from any version of the conditional
probabilities. The normalization of such a version is not formalized. -/
theorem directedInfo_eq_klDivSum :
    directedInfo ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) =
      klDivSum (fun z ↦ ρ.real {z}) fun z ↦
        (causalCondDelayed ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) z.1 z.2).toReal *
          ρ.snd.real {z.2} := by
  rw [directedInfo_eq_sum_log_causalCond, klDivSum]
  refine sum_congr rfl fun z _ ↦ ?_
  rcases eq_or_ne (ρ.real {z}) 0 with h0 | h0
  · simp [h0]
  have hfac := measure_preimage_eq_causalCondDelayed_mul_causalCond (μ := ρ) (fun i z ↦ z.1 i)
    (fun i z ↦ z.2 i) z.1 z.2
  have hset : (fun (ω : (Fin n → 𝓧) × (Fin n → 𝓨)) (j : Fin n) ↦ ω.1 j) ⁻¹' {z.1} ∩
      (fun (ω : (Fin n → 𝓧) × (Fin n → 𝓨)) (j : Fin n) ↦ ω.2 j) ⁻¹' {z.2} = {z} := by
    ext ω
    simp [Prod.ext_iff]
  rw [hset] at hfac
  have hreal : ρ.real {z} =
      (causalCondDelayed ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) z.1 z.2).toReal *
        (causalCond ρ (fun i z ↦ z.2 i) (fun i z ↦ z.1 i) z.2 z.1).toReal := by
    rw [measureReal_def, hfac, ENNReal.toReal_mul]
  have hD : (causalCondDelayed ρ (fun i z ↦ z.1 i) (fun i z ↦ z.2 i) z.1 z.2).toReal ≠ 0 :=
    fun h ↦ h0 (by rw [hreal, h, zero_mul])
  have hY : probEq ρ (fun ω j ↦ ω.2 j) z = ρ.snd.real {z.2} := by
    rw [probEq, measureReal_def, measureReal_def, Measure.snd_apply .of_discrete]
  rw [hY, hreal, mul_div_mul_left _ _ hD]

end Canonical

end InformationTheory
