/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.MaximalLeakage.MutualInfo
public import InfoLeakage.MaximalLeakage.Operational
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.UniformOn

/-!
# Vulnerability, min-entropy leakage and one-try attacks

This file formalizes two founding papers of quantitative information flow (QIF), for a secret
`X ∼ μ` (the prior `π`) on a finite alphabet and a channel `κ : Kernel α β` (the channel matrix
`C[x, y] = κ x {y}`) with finite output alphabet:

* G. Smith, *On the Foundations of Quantitative Information Flow*, FoSSaCS 2009, LNCS 5504,
  pp. 288–302 (not on arXiv);
* C. Braun, K. Chatzikokolakis, C. Palamidessi, *Quantitative Notions of Leakage for One-try
  Attacks*, MFPS 2009, ENTCS 249, pp. 75–91 (HAL inria-00424852; not on arXiv).

Smith measures the threat that an adversary guesses the secret in one try by its
**vulnerability** `V(X) = max_x P[X = x]`, and leakage by the **min-entropy leakage**
`H∞(X) - H∞(X | Y) = log (V(X | Y) / V(X))`. Braun et al. call `V(X)` and `V(X | Y)` the a priori
and a posteriori probabilities of a right guess `PR_i(π)` and `PR_o(π)`, and compare the
multiplicative leakage `PR_o / PR_i` with the additive leakage `PR_o - PR_i`.

## Main definitions

* `vulnerability μ`, `minEntropy μ`: `V(X)` and `H∞(X)` (Smith, Definitions 1 and 2).
* `condVulnerability ρ`, `condMinEntropy ρ`: `V(X | Y)` and `H∞(X | Y)` of a joint law `ρ` of
  `(X, Y)`, through conditional probabilities (Smith, Definitions 3 and 4).
* `minEntropyLeakage μ κ`: Smith's "information leaked" `H∞(X) - H∞(X | Y)`.
* `postVulnerability μ κ`: `V(π, C) = ∑_y max_x π[x] C[x, y]`, Braun et al.'s `PR_o(π)`.
* `multLeakage`, `maxMultLeakage`: `L×(π) = PR_o(π) / PR_i(π)` and `ML× = max_π L×(π)` (Braun et
  al., Definition 4.3).
* `addLeakage`, `maxAddLeakage`: `L+(π) = PR_o(π) - PR_i(π)` and `ML+ = max_π L+(π)` (Braun et
  al., Definition 4.4).

## Main statements

* `condVulnerability_compProd`: Smith's Bayes computation `V(X | Y) = ∑_y max_x C[x, y] π[x]`.
* `minEntropyLeakage_deterministic_uniformOn`: **Smith, Theorem 1**: a deterministic channel `f`
  leaks `log |f(H)|` from a uniform secret.
* `isGreatest_mutualInfo_deterministic`: **Smith, Theorem 2**: this leakage is the Shannon
  capacity `max_π I(H; L)` of the deterministic channel.
* `condVulnerability_voteTally`, `minEntropyLeakage_voteTally`: Smith's election example.
* `maxMultLeakage_eq`: **Braun et al., Proposition 5.1**: `ML× = L×(π_u) = ∑_y max_x C[x, y]`.
* `maxLeakage_eq_log_maxMultLeakage`, `multLeakage_le_maxLeakageSum`: link with the maximal
  leakage `maxLeakage` of Issa, Wagner and Kamath: at any full-support prior it equals the
  min-capacity `log ML×`, and it bounds `L×(π)` at every prior.
* `postVulnerability_add_smul_le`: **Braun et al., Proposition 6.4**: `PR_o` is convex.
* `exists_isGreatest_addLeakage_uniformOn`, `exists_maxAddLeakage_eq`: **Braun et al.,
  Corollary 6.5**: `ML+` is attained on a corner point, the uniform prior on a nonempty set.
* `addLeakage_uniformOn`: the additive leakage of a corner point, `(∑_y max_{x ∈ S} C[x, y] - 1)
  / |S|`.
* `addLeakage_le_addLeakage_iff`: **Braun et al., Proposition 7.1**: on a fixed prior the
  additive and multiplicative leakages order channels in the same way.

## Paper-to-Lean map

* Smith, Definitions 1–4: `vulnerability`, `minEntropy`, `condVulnerability`, `condMinEntropy`;
  "information leaked": `minEntropyLeakage` (`minEntropyLeakage_eq_log`).
* Smith, Section 5, computation of `V(H | L)`: `condVulnerability_compProd`; deterministic and
  uniform cases: `postVulnerability_deterministic`, `postVulnerability_deterministic_uniformOn`.
* Smith, Theorem 1: `minEntropyLeakage_deterministic_uniformOn`.
* Smith, Theorem 2: `isGreatest_mutualInfo_deterministic`.
* Smith, election example: `condVulnerability_voteTally`, `minEntropyLeakage_voteTally`.
* Braun et al., Definitions 4.1–4.4: `vulnerability`, `postVulnerability`, `multLeakage`,
  `maxMultLeakage`, `addLeakage`, `maxAddLeakage`.
* Braun et al., Proposition 5.1: `maxMultLeakage_eq` (with `multLeakage_uniformOn_univ`).
* Braun et al., Proposition 6.4: `postVulnerability_add_smul_le`.
* Braun et al., Corollary 6.5: `exists_isGreatest_addLeakage_uniformOn`,
  `exists_maxAddLeakage_eq`.
* Braun et al., Proposition 7.1: `addLeakage_le_addLeakage_iff`.

Not formalized: the Shannon-entropy examples of Smith's Section 4, the general Propositions 6.1
and 6.2 of Braun et al. on convexly generated functions (Corollary 6.5 is proved directly), and
the numerical Examples 3.1, 6.7, 6.9, 7.2 and 7.3 of Braun et al.

## Implementation notes

Logarithms are natural (nats); the papers use bits, which rescales every leakage by `log 2`.
Probabilities are kept in `ℝ≥0∞`, and min-entropies and leakages are real numbers. Smith assumes
every secret has positive probability and every output is possible; we do not need these
assumptions, and Theorem 1 is stated with the number `|f(H)|` of possible outputs.

Corollary 6.5 is not proved through the corner-point machinery of Braun et al. (their
Propositions 6.1–6.4), but by an induction on the support of the prior
(`sum_iSup_mul_le_of_forall_finset`): the prior is the corner point on its support, weighted by
its smallest positive value, plus a vector with smaller support.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {κ : Kernel α β}

section Definitions

/-- The **vulnerability** `V(X) = max_x P[X = x]` of `X ∼ μ`: the probability that an adversary
guesses `X` correctly in one try (Definition 1 of Smith). -/
noncomputable def vulnerability (μ : Measure α) : ℝ≥0∞ :=
  ⨆ x, μ {x}

/-- The **min-entropy** `H∞(X) = log (1 / V(X))` of `X ∼ μ`, in nats (Definition 2 of Smith). -/
noncomputable def minEntropy (μ : Measure α) : ℝ :=
  -Real.log (vulnerability μ).toReal

/-- The **conditional vulnerability** `V(X | Y) = ∑_y P[Y = y] max_x P[X = x | Y = y]` of jointly
distributed `(X, Y) ∼ ρ` (Definition 3 of Smith). -/
noncomputable def condVulnerability [Fintype β] (ρ : Measure (α × β)) : ℝ≥0∞ :=
  ∑ y, ρ (Prod.snd ⁻¹' {y}) * ⨆ x, ρ[Prod.fst ⁻¹' {x} | Prod.snd ⁻¹' {y}]

/-- The **conditional min-entropy** `H∞(X | Y) = log (1 / V(X | Y))`, in nats (Definition 4 of
Smith). -/
noncomputable def condMinEntropy [Fintype β] (ρ : Measure (α × β)) : ℝ :=
  -Real.log (condVulnerability ρ).toReal

/-- The **min-entropy leakage** `H∞(X) - H∞(X | Y)` from `X ∼ μ` to the output `Y` of the channel
`κ` (Smith's "information leaked"), in nats. -/
noncomputable def minEntropyLeakage [Fintype β] (μ : Measure α) (κ : Kernel α β) : ℝ :=
  minEntropy μ - condMinEntropy (μ ⊗ₘ κ)

/-- The **posterior vulnerability** `V(π, C) = ∑_y max_x π[x] C[x, y]` of a prior `μ` through the
channel `κ`. It is the a posteriori probability of a right guess `PR_o(π)` of Braun,
Chatzikokolakis and Palamidessi (their Definition 4.2), and `condVulnerability_compProd` shows
that it equals Smith's `V(X | Y)`. -/
noncomputable def postVulnerability [Fintype β] (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  ∑ y, ⨆ x, κ x {y} * μ {x}

end Definitions

section Smith

variable [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- Smith's computation of the conditional vulnerability by Bayes' theorem:
`V(H | L) = ∑_ℓ max_h P[L = ℓ | H = h] P[H = h]`. -/
theorem condVulnerability_compProd [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    condVulnerability (μ ⊗ₘ κ) = postVulnerability μ κ := by
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have hy : MeasurableSet (Prod.snd ⁻¹' {y} : Set (α × β)) :=
    measurable_snd (measurableSet_singleton y)
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun x ↦ ?_
  rw [mul_comm, cond_mul_eq_inter hy]
  have h : Prod.snd ⁻¹' {y} ∩ Prod.fst ⁻¹' {x} = ({x} ×ˢ {y} : Set (α × β)) := by
    ext ⟨a, b⟩
    simp [and_comm]
  rw [h, Measure.compProd_apply_prod (measurableSet_singleton x) (measurableSet_singleton y),
    Measure.restrict_singleton]
  simp [mul_comm]

end Smith

section Bounds

variable [Fintype β]

omit [Fintype β] in
lemma vulnerability_le_measure_univ (μ : Measure α) : vulnerability μ ≤ μ Set.univ :=
  iSup_le fun _ ↦ measure_mono (Set.subset_univ _)

omit [Fintype β] in
lemma vulnerability_ne_top (μ : Measure α) [IsFiniteMeasure μ] : vulnerability μ ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top μ _) (vulnerability_le_measure_univ μ)

omit [Fintype β] in
lemma vulnerability_ne_zero [Finite α] [MeasurableSingletonClass α] (μ : Measure α)
    [IsProbabilityMeasure μ] : vulnerability μ ≠ 0 := by
  have := Fintype.ofFinite α
  intro h
  have h0 (x : α) : μ {x} = 0 := le_antisymm (h ▸ le_iSup (fun x ↦ μ {x}) x) zero_le
  have := measure_univ (μ := μ)
  rw [← Finset.coe_univ, ← sum_measure_singleton] at this
  simp [h0] at this

/-- Observing the output of a channel cannot decrease the probability of a right guess:
`V(π) ≤ V(π, C)`. -/
lemma vulnerability_le_postVulnerability [MeasurableSingletonClass β] [IsMarkovKernel κ] :
    vulnerability μ ≤ postVulnerability μ κ := by
  refine iSup_le fun x ↦ ?_
  calc μ {x} = ∑ y, κ x {y} * μ {x} := by
        rw [← Finset.sum_mul, sum_measure_singleton]
        simp
    _ ≤ postVulnerability μ κ :=
        Finset.sum_le_sum fun y _ ↦ le_iSup (fun x ↦ κ x {y} * μ {x}) x

/-- The posterior vulnerability is at most the total mass of the prior. -/
lemma postVulnerability_le_measure_univ [Finite α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsMarkovKernel κ] :
    postVulnerability μ κ ≤ μ Set.univ := by
  have := Fintype.ofFinite α
  calc postVulnerability μ κ ≤ ∑ y, ∑ x, κ x {y} * μ {x} :=
        Finset.sum_le_sum fun y _ ↦ iSup_le fun x ↦
          Finset.single_le_sum (f := fun x ↦ κ x {y} * μ {x}) (fun _ _ ↦ zero_le)
            (Finset.mem_univ x)
    _ = ∑ x, μ {x} := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [← Finset.sum_mul, sum_measure_singleton]
        simp
    _ = μ Set.univ := by rw [sum_measure_singleton, Finset.coe_univ]

lemma postVulnerability_ne_top [Finite α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    postVulnerability μ κ ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top μ _) postVulnerability_le_measure_univ

/-- The min-entropy leakage is the logarithm of the ratio of the posterior and prior
vulnerabilities, `H∞(X) - H∞(X | Y) = log (V(X | Y) / V(X))`. -/
theorem minEntropyLeakage_eq_log [Finite α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    minEntropyLeakage μ κ =
      Real.log ((postVulnerability μ κ).toReal / (vulnerability μ).toReal) := by
  have hV : (vulnerability μ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨vulnerability_ne_zero μ, vulnerability_ne_top μ⟩
  have hP : (postVulnerability μ κ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨fun h ↦ vulnerability_ne_zero μ
      (le_antisymm (h ▸ vulnerability_le_postVulnerability) zero_le), postVulnerability_ne_top⟩
  rw [minEntropyLeakage, condMinEntropy, condVulnerability_compProd, minEntropy,
    Real.log_div hP hV]
  ring

end Bounds

section Deterministic

variable [Fintype β] [MeasurableSingletonClass β]

/-- For a deterministic channel `f`, the posterior vulnerability is the sum over the outputs `ℓ`
of the largest prior probability in the equivalence class `f⁻¹(ℓ)` (Section 5 of Smith). -/
lemma postVulnerability_deterministic {f : α → β} (hf : Measurable f) :
    postVulnerability μ (Kernel.deterministic f hf) = ∑ y, ⨆ (x) (_ : f x = y), μ {x} := by
  refine Finset.sum_congr rfl fun y _ ↦ iSup_congr fun x ↦ ?_
  rw [Kernel.deterministic_apply' hf x (measurableSet_singleton y)]
  by_cases h : f x = y <;> simp [h]

variable [Fintype α] [MeasurableSingletonClass α]

omit [Fintype β] [MeasurableSingletonClass β] in
lemma uniformOn_univ_apply_singleton (x : α) :
    uniformOn (Set.univ : Set α) {x} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOn_univ]

omit [Fintype β] [MeasurableSingletonClass β] in
lemma vulnerability_uniformOn_univ [Nonempty α] :
    vulnerability (uniformOn (Set.univ : Set α)) = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [vulnerability, uniformOn_univ_apply_singleton]

/-- For a deterministic channel `f` and a uniform prior, `V(H | L) = |f(H)| / |H|`, where
`|f(H)|` is the number of possible outputs (Section 5 of Smith). -/
lemma postVulnerability_deterministic_uniformOn [DecidableEq β] {f : α → β}
    (hf : Measurable f) :
    postVulnerability (uniformOn Set.univ) (Kernel.deterministic f hf) =
      (Finset.univ.image f).card / Fintype.card α := by
  set c := (Fintype.card α : ℝ≥0∞)⁻¹
  have h (y : β) : (⨆ (x) (_ : f x = y), uniformOn (Set.univ : Set α) {x}) =
      if y ∈ Finset.univ.image f then c else 0 := by
    simp_rw [uniformOn_univ_apply_singleton]
    split_ifs with hy
    · obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hy
      exact le_antisymm (iSup₂_le fun _ _ ↦ le_rfl) (le_iSup₂_of_le x hx le_rfl)
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hy
      simp [hy]
  rw [postVulnerability_deterministic, Finset.sum_congr rfl fun y _ ↦ h y,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Theorem 1 of Smith**: if the channel is deterministic and the secret is uniformly
distributed, the min-entropy leakage is `log |L|`, the logarithm of the number of possible
outputs. -/
theorem minEntropyLeakage_deterministic_uniformOn [Nonempty α] [DecidableEq β] {f : α → β}
    (hf : Measurable f) :
    minEntropyLeakage (uniformOn Set.univ) (Kernel.deterministic f hf) =
      Real.log (Finset.univ.image f).card := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hR : ((Finset.univ.image f).card : ℝ) ≠ 0 := by
    simp [Finset.univ_nonempty.image f |>.card_pos.ne']
  rw [minEntropyLeakage, condMinEntropy, condVulnerability_compProd,
    postVulnerability_deterministic_uniformOn, minEntropy, vulnerability_uniformOn_univ]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_natCast, Real.log_inv,
    Real.log_div hR hα]
  ring

end Deterministic

section Election

/-- The tally `|{i | v i}|` of the votes `v : Fin k → Bool` of `k` voters. -/
def voteTally (k : ℕ) (v : Fin k → Bool) : Fin (k + 1) :=
  ⟨(Finset.univ.filter fun i ↦ v i = true).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

lemma voteTally_surjective (k : ℕ) : Function.Surjective (voteTally k) := by
  intro j
  refine ⟨fun i ↦ decide ((i : ℕ) < j), Fin.ext ?_⟩
  simp [voteTally, Fin.card_filter_val_lt, Nat.lt_succ_iff.1 j.isLt]

/-- Smith's election example: `k` voters vote independently and uniformly for one of two
candidates, and the tally is revealed. Then `V(H | L) = (k + 1) / 2 ^ k`. -/
theorem condVulnerability_voteTally (k : ℕ) :
    condVulnerability (uniformOn Set.univ ⊗ₘ
      Kernel.deterministic (voteTally k) (measurable_of_finite _)) = (k + 1) / 2 ^ k := by
  rw [condVulnerability_compProd, postVulnerability_deterministic_uniformOn,
    Finset.image_univ_of_surjective (voteTally_surjective k)]
  simp

/-- Smith's election example: revealing the tally of `k` uniform binary votes leaks
`log (k + 1)`. -/
theorem minEntropyLeakage_voteTally (k : ℕ) :
    minEntropyLeakage (uniformOn Set.univ)
      (Kernel.deterministic (voteTally k) (measurable_of_finite _)) = Real.log (k + 1) := by
  rw [minEntropyLeakage_deterministic_uniformOn,
    Finset.image_univ_of_surjective (voteTally_surjective k)]
  simp

end Election

section Capacity

/-! ### Theorem 2 of Smith: capacity of a deterministic channel -/

variable [Finite β] [MeasurableSingletonClass β]

/-- The Kullback-Leibler divergence of a Dirac mass: `KL(δ_y ‖ ν) = log (1 / ν {y})`. -/
lemma klDiv_dirac (ν : Measure β) [IsProbabilityMeasure ν] {y : β} (hy : ν {y} ≠ 0) :
    klDiv (Measure.dirac y) ν = ENNReal.ofReal (-Real.log (ν {y}).toReal) := by
  have hac : Measure.dirac y ≪ ν := fun s hs ↦ by
    rw [Measure.dirac_apply]
    by_cases h : y ∈ s
    · exact absurd (measure_mono_null (Set.singleton_subset_iff.2 h) hs) hy
    · simp [h]
  have h_int : Integrable (llr (Measure.dirac y) ν) (Measure.dirac y) := .of_finite
  have hrn : (Measure.dirac y).rnDeriv ν y = (ν {y})⁻¹ := by
    refine ENNReal.eq_inv_of_mul_eq_one_left ?_
    have h := Measure.setLIntegral_rnDeriv hac (s := {y})
    rw [lintegral_singleton] at h
    simpa using h
  rw [klDiv_of_ac_of_integrable hac h_int, integral_dirac, llr, hrn]
  simp [Measure.real, Real.log_inv]

/-- The mutual information as the average divergence of the rows of the channel from the output
law: `I(X; Y) = E_{X}[KL(P_{Y|X} ‖ P_Y)]`. -/
lemma mutualInfo_compProd_eq_lintegral [Countable α]
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    mutualInfo (μ ⊗ₘ κ) = ∫⁻ x, klDiv (κ x) (κ ∘ₘ μ) ∂μ := by
  rw [mutualInfo_compProd_eq_condKL, condKL_eq_lintegral]
  simp


variable [MeasurableSingletonClass α]

omit [Finite β] [MeasurableSingletonClass α] in
lemma maxLeakageSum_deterministic_le [Fintype α] [Fintype β] [DecidableEq β] {f : α → β}
    (hf : Measurable f) :
    maxLeakageSum μ (Kernel.deterministic f hf) ≤ (Finset.univ.image f).card := by
  calc maxLeakageSum μ (Kernel.deterministic f hf)
      ≤ ∑ y, if y ∈ Finset.univ.image f then (1 : ℝ≥0∞) else 0 := by
        refine Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ ?_
        rw [Kernel.deterministic_apply' hf x (measurableSet_singleton y)]
        by_cases h : f x = y
        · subst h
          simp
        · simp [h]
    _ = (Finset.univ.image f).card := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

omit [MeasurableSingletonClass α] in
/-- For a deterministic channel, the mutual information is at most `log |f(H)|` for every prior. -/
lemma toReal_mutualInfo_deterministic_le [Fintype α] [DecidableEq β] [IsProbabilityMeasure μ]
    {f : α → β} (hf : Measurable f) :
    (mutualInfo (μ ⊗ₘ Kernel.deterministic f hf)).toReal ≤
      Real.log (Finset.univ.image f).card := by
  have := Fintype.ofFinite β
  obtain ⟨x, hx⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  refine toReal_mutualInfo_compProd_le_maxLeakage.trans ?_
  refine Real.log_le_log (zero_lt_one.trans_le (one_le_toReal_maxLeakageSum hx)) ?_
  simpa using ENNReal.toReal_mono (by simp) (maxLeakageSum_deterministic_le (μ := μ) hf)

/-- For a deterministic channel, some prior (the uniform distribution on one representative of
each possible output) has mutual information `log |f(H)|`. -/
lemma exists_toReal_mutualInfo_deterministic_eq [Fintype α] [Nonempty α] [DecidableEq β]
    {f : α → β} (hf : Measurable f) :
    ∃ μ : Measure α, IsProbabilityMeasure μ ∧
      (mutualInfo (μ ⊗ₘ Kernel.deterministic f hf)).toReal =
        Real.log (Finset.univ.image f).card := by
  classical
  have := Fintype.ofFinite β
  set R := Finset.univ.image f
  set s := Function.invFun f
  set S := R.image s
  have hs (y : β) (hy : y ∈ R) : f (s y) = y := by
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hy
    exact Function.invFun_eq ⟨x, hx⟩
  have hSR : S.card = R.card :=
    Finset.card_image_of_injOn fun y hy y' hy' h ↦ by
      rw [← hs y hy, ← hs y' hy']
      exact congrArg f h
  have hSne : S.Nonempty := (Finset.univ_nonempty.image f).image s
  have hS0 : (S.card : ℝ≥0∞) ≠ 0 := by simp [hSne.ne_empty]
  set μ := uniformOn (S : Set α)
  have hμ := isProbabilityMeasure_uniformOn S.finite_toSet (by simpa using hSne)
  have hμx (x : α) : μ {x} = if x ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0 := by
    simp only [μ]
    rw [← Finset.coe_singleton, uniformOn_apply_finset]
    split_ifs with hx
    · simp [Finset.inter_singleton_of_mem hx]
    · simp [Finset.inter_singleton_of_notMem hx]
  -- The output law is uniform on `f(H)`.
  have hfS (x : α) (hx : x ∈ S) (x' : α) (hx' : x' ∈ S) (h : f x' = f x) : x' = x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hx'
    rw [hs y hy, hs y' hy'] at h
    rw [h]
  have hPY (x : α) (hx : x ∈ S) :
      (Kernel.deterministic f hf ∘ₘ μ) {f x} = (S.card : ℝ≥0∞)⁻¹ := by
    rw [comp_apply_singleton, Finset.sum_eq_single x]
    · simp [Kernel.deterministic_apply' hf x (measurableSet_singleton _), hμx, hx]
    · intro x' _ hx'
      rw [Kernel.deterministic_apply' hf x' (measurableSet_singleton _), hμx]
      by_cases h : f x' = f x
      · simp [show x' ∉ S from fun h' ↦ hx' (hfS x hx x' h' h)]
      · simp [h]
    · simp
  refine ⟨μ, hμ, ?_⟩
  rw [mutualInfo_compProd_eq_lintegral, lintegral_fintype]
  have hterm (x : α) : klDiv (Kernel.deterministic f hf x) (Kernel.deterministic f hf ∘ₘ μ) *
      μ {x} = if x ∈ S then ENNReal.ofReal (Real.log S.card) * (S.card : ℝ≥0∞)⁻¹ else 0 := by
    by_cases hx : x ∈ S
    · rw [Kernel.deterministic_apply, klDiv_dirac _ (by rw [hPY x hx]; simp), hPY x hx, hμx]
      simp [hx, Real.log_inv]
    · simp [hμx, hx]
  rw [Finset.sum_congr rfl fun x _ ↦ hterm x, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_comm, mul_assoc, ENNReal.inv_mul_cancel hS0 (by simp),
    mul_one, ENNReal.toReal_ofReal (Real.log_natCast_nonneg _), hSR]

omit [Finite β] in
/-- **Theorem 2 of Smith**: for a deterministic channel and a uniformly distributed secret, the
min-entropy leakage `log |L|` equals the (Shannon) channel capacity `max_π I(H; L)`: it is the
largest mutual information over all priors. -/
theorem isGreatest_mutualInfo_deterministic [Finite α] [Nonempty α] [Fintype β]
    {f : α → β} (hf : Measurable f) :
    IsGreatest {r | ∃ μ : Measure α, IsProbabilityMeasure μ ∧
        (mutualInfo (μ ⊗ₘ Kernel.deterministic f hf)).toReal = r}
      (minEntropyLeakage (uniformOn Set.univ) (Kernel.deterministic f hf)) := by
  classical
  have := Fintype.ofFinite α
  rw [minEntropyLeakage_deterministic_uniformOn]
  obtain ⟨μ, hμ, h⟩ := exists_toReal_mutualInfo_deterministic_eq hf
  refine ⟨⟨μ, hμ, h⟩, ?_⟩
  rintro r ⟨ν, hν, rfl⟩
  exact toReal_mutualInfo_deterministic_le hf

end Capacity

section OneTry

/-! ### Multiplicative and additive leakage

Braun, Chatzikokolakis and Palamidessi compare two ways of measuring how much a channel
increases the probability of a right guess: the ratio and the difference of `PR_o(π)` and
`PR_i(π)`. -/

variable [Fintype β]

/-- The **multiplicative leakage** `L×(π) = PR_o(π) / PR_i(π)` (Definition 4.3 of Braun et al.),
the exponential of the min-entropy leakage (`minEntropyLeakage_eq_log`). -/
noncomputable def multLeakage (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  postVulnerability μ κ / vulnerability μ

/-- The worst-case multiplicative leakage `ML× = max_π L×(π)` over all priors (Braun et al.),
the exponential of the min-capacity. -/
noncomputable def maxMultLeakage (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (μ : Measure α) (_ : IsProbabilityMeasure μ), multLeakage μ κ

/-- The **additive leakage** `L+(π) = PR_o(π) - PR_i(π)` (Definition 4.4 of Braun et al.). -/
noncomputable def addLeakage (μ : Measure α) (κ : Kernel α β) : ℝ :=
  (postVulnerability μ κ).toReal - (vulnerability μ).toReal

/-- The worst-case additive leakage `ML+ = max_π L+(π)` over all priors (Braun et al.).
`exists_isGreatest_addLeakage_uniformOn` shows that the maximum is attained. -/
noncomputable def maxAddLeakage (κ : Kernel α β) : ℝ :=
  sSup {r | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ addLeakage μ κ = r}

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- The multiplicative leakage is at most the maximal leakage of Issa, Wagner and Kamath:
`L×(π) ≤ ∑_y max_{x ∈ supp π} C[x, y]`. -/
lemma multLeakage_le_maxLeakageSum : multLeakage μ κ ≤ maxLeakageSum μ κ := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [maxLeakageSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun y _ ↦ iSup_le fun x ↦ ?_
  exact (mul_le_iSup_mul x y).trans (mul_le_mul_right (le_iSup (fun x ↦ μ {x}) x) _)

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma maxLeakageSum_le_sum_iSup : maxLeakageSum μ κ ≤ ∑ y, ⨆ x, κ x {y} :=
  Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ le_iSup (fun x ↦ κ x {y}) x

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- For a prior of full support, the maximal leakage sum is the sum of the column maxima. -/
lemma maxLeakageSum_eq_sum_iSup (hμ : ∀ x, μ {x} ≠ 0) :
    maxLeakageSum μ κ = ∑ y, ⨆ x, κ x {y} := by
  simp [maxLeakageSum, hμ]

omit [MeasurableSingletonClass β] in
/-- The multiplicative leakage of the uniform prior is the sum of the column maxima of the
channel matrix. -/
lemma multLeakage_uniformOn_univ [Nonempty α] :
    multLeakage (uniformOn Set.univ) κ = ∑ y, ⨆ x, κ x {y} := by
  have := Fintype.ofFinite α
  have h0 : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have ht : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
  rw [multLeakage, postVulnerability, vulnerability_uniformOn_univ]
  simp_rw [uniformOn_univ_apply_singleton, ← ENNReal.iSup_mul, ← Finset.sum_mul]
  exact ENNReal.mul_div_cancel_right h0 ht

omit [MeasurableSingletonClass β] in
/-- **Proposition 5.1 of Braun, Chatzikokolakis and Palamidessi**: the worst-case multiplicative
leakage is attained on the uniform prior and equals the sum of the column maxima of the channel
matrix, `ML× = L×(π_u) = ∑_y max_x C[x, y]`. -/
theorem maxMultLeakage_eq [Nonempty α] :
    maxMultLeakage κ = ∑ y, ⨆ x, κ x {y} ∧
      maxMultLeakage κ = multLeakage (uniformOn Set.univ) κ := by
  have h : maxMultLeakage κ = ∑ y, ⨆ x, κ x {y} :=
    le_antisymm
      (iSup₂_le fun _ _ ↦ multLeakage_le_maxLeakageSum.trans maxLeakageSum_le_sum_iSup)
      (le_iSup₂_of_le (uniformOn Set.univ) inferInstance multLeakage_uniformOn_univ.ge)
  exact ⟨h, h.trans multLeakage_uniformOn_univ.symm⟩

omit [MeasurableSingletonClass β] in
/-- The maximal leakage of Issa, Wagner and Kamath at any prior of full support equals the
min-capacity `log ML×` of Braun et al. and Smith. -/
theorem maxLeakage_eq_log_maxMultLeakage [Nonempty α] (hμ : ∀ x, μ {x} ≠ 0) :
    maxLeakage μ κ = Real.log (maxMultLeakage κ).toReal := by
  rw [maxLeakage, maxLeakageSum_eq_sum_iSup hμ, maxMultLeakage_eq.1]

/-- The min-entropy leakage is the logarithm of the multiplicative leakage. -/
lemma minEntropyLeakage_eq_log_multLeakage [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    minEntropyLeakage μ κ = Real.log (multLeakage μ κ).toReal := by
  rw [minEntropyLeakage_eq_log, multLeakage, ENNReal.toReal_div]

/-- **Proposition 7.1 of Braun, Chatzikokolakis and Palamidessi**: on a fixed prior, two channels
(programs, possibly with different output alphabets) are ordered in the same way by the additive
and by the multiplicative leakage. -/
theorem addLeakage_le_addLeakage_iff {β' : Type*} {mβ' : MeasurableSpace β'} [Fintype β']
    [MeasurableSingletonClass β'] [IsProbabilityMeasure μ] (κ' : Kernel α β')
    [IsMarkovKernel κ] [IsMarkovKernel κ'] :
    addLeakage μ κ ≤ addLeakage μ κ' ↔ multLeakage μ κ ≤ multLeakage μ κ' := by
  rw [addLeakage, addLeakage, sub_le_sub_iff_right, multLeakage, multLeakage, div_eq_mul_inv,
    div_eq_mul_inv, ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 (vulnerability_ne_top μ))
      (ENNReal.inv_ne_top.2 (vulnerability_ne_zero μ)),
    ENNReal.toReal_le_toReal postVulnerability_ne_top postVulnerability_ne_top]

end OneTry

section CornerPoints

/-! ### The worst case of the additive leakage

Braun et al. show that `PR_o` is convex (Proposition 6.4) and that `PR_i` is convexly generated by
its corner points, the uniform distributions on nonempty subsets of the secrets (their
Proposition 6.2, from Chatzikokolakis–Palamidessi–Panangaden). By their Proposition 6.1, the
additive leakage `PR_o - PR_i` therefore attains its maximum on a corner point (Corollary 6.5).
We prove Corollary 6.5 directly, by peeling off from the prior `π` the corner point on its
support, weighted by the smallest positive value of `π`, and inducting on the size of the
support (`sum_iSup_mul_le_of_forall_finset`). -/

variable [Fintype β]

lemma postVulnerability_add_le (μ ν : Measure α) :
    postVulnerability (μ + ν) κ ≤ postVulnerability μ κ + postVulnerability ν κ := by
  rw [postVulnerability, postVulnerability, postVulnerability, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ ↦ iSup_le fun x ↦ ?_
  rw [add_apply, mul_add]
  exact add_le_add (le_iSup (fun x ↦ κ x {y} * μ {x}) x) (le_iSup (fun x ↦ κ x {y} * ν {x}) x)

lemma postVulnerability_smul (c : ℝ≥0∞) (μ : Measure α) :
    postVulnerability (c • μ) κ = c * postVulnerability μ κ := by
  simp_rw [postVulnerability, Finset.mul_sum, ENNReal.mul_iSup, smul_apply, smul_eq_mul,
    mul_left_comm]

/-- **Proposition 6.4 of Braun, Chatzikokolakis and Palamidessi**: the a posteriori probability of
a right guess `PR_o` is a convex function of the prior (it is even sublinear). -/
theorem postVulnerability_add_smul_le (μ ν : Measure α) (a b : ℝ≥0∞) :
    postVulnerability (a • μ + b • ν) κ ≤ a * postVulnerability μ κ + b * postVulnerability ν κ :=
  (postVulnerability_add_le _ _).trans_eq (by rw [postVulnerability_smul, postVulnerability_smul])

/-- The induction behind Corollary 6.5 of Braun et al.: if every corner point (the uniform
distribution on a nonempty `S`) satisfies `∑_y max_{x ∈ S} C[x, y] ≤ 1 + L |S|`, then every
nonnegative vector `p` satisfies `∑_y max_x C[x, y] p(x) ≤ max_x p(x) + L ∑_x p(x)`. -/
lemma sum_iSup_mul_le_of_forall_finset [Fintype α] (C : α → β → ℝ≥0∞) (L : ℝ≥0∞)
    (hL : ∀ S : Finset α, S.Nonempty → ∑ y, ⨆ x ∈ S, C x y ≤ 1 + L * S.card) (p : α → ℝ≥0∞) :
    ∑ y, ⨆ x, C x y * p x ≤ (⨆ x, p x) + L * ∑ x, p x := by
  classical
  induction h : (Finset.univ.filter fun x ↦ p x ≠ 0).card using Nat.strong_induction_on
    generalizing p with
  | _ n ih =>
  set S := Finset.univ.filter fun x ↦ p x ≠ 0 with hS
  have hpn (x : α) (hx : x ∉ S) : p x = 0 := by simpa [S] using hx
  rcases S.eq_empty_or_nonempty with hSe | hSn
  · have hp0 (x : α) : p x = 0 := hpn x (by simp [hSe])
    simp [hp0]
  obtain ⟨x₀, hx₀S, hx₀⟩ := S.exists_min_image p hSn
  set m := p x₀
  set p' : α → ℝ≥0∞ := fun x ↦ p x - m
  have hpS (x : α) (hx : x ∈ S) : p x = m + p' x := (add_tsub_cancel_of_le (hx₀ x hx)).symm
  have hp'n (x : α) (hx : x ∉ S) : p' x = 0 := by simp [p', hpn x hx]
  have hlt : (Finset.univ.filter fun x ↦ p' x ≠ 0).card < n := by
    rw [← h]
    refine Finset.card_lt_card ⟨fun x hx ↦ ?_, fun hsub ↦ ?_⟩
    · rw [Finset.mem_filter] at hx
      by_contra hxS
      exact hx.2 (hp'n x hxS)
    · simpa [p', m] using hsub hx₀S
  have ih' := ih _ hlt p' rfl
  have ha (y : β) : ⨆ x, C x y * p x ≤ m * (⨆ x ∈ S, C x y) + ⨆ x, C x y * p' x := by
    refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ S
    · rw [hpS x hx, mul_add, mul_comm (C x y) m]
      exact add_le_add (mul_le_mul_right (le_iSup₂ (f := fun x _ ↦ C x y) x hx) m)
        (le_iSup (fun x ↦ C x y * p' x) x)
    · simp [hpn x hx]
  have hc : m + ⨆ x, p' x ≤ ⨆ x, p x := by
    have : Nonempty α := ⟨x₀⟩
    rw [ENNReal.add_iSup]
    refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ S
    · rw [← hpS x hx]
      exact le_iSup p x
    · rw [hp'n x hx, add_zero]
      exact le_iSup p x₀
  have hd : ∑ x, p x = m * S.card + ∑ x, p' x := by
    have hsplit (x : α) : p x = (if x ∈ S then m else 0) + p' x := by
      by_cases hx : x ∈ S
      · simp [hx, hpS x hx]
      · simp [hx, hpn x hx, hp'n x hx]
    rw [Finset.sum_congr rfl fun x _ ↦ hsplit x, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ y, ⨆ x, C x y * p x
      ≤ ∑ y, (m * (⨆ x ∈ S, C x y) + ⨆ x, C x y * p' x) := Finset.sum_le_sum fun y _ ↦ ha y
    _ = m * (∑ y, ⨆ x ∈ S, C x y) + ∑ y, ⨆ x, C x y * p' x := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ m * (1 + L * S.card) + ((⨆ x, p' x) + L * ∑ x, p' x) :=
        add_le_add (mul_le_mul_right (hL S hSn) m) ih'
    _ = (m + ⨆ x, p' x) + L * (m * S.card + ∑ x, p' x) := by ring
    _ ≤ (⨆ x, p x) + L * ∑ x, p x := by
        rw [hd]
        exact add_le_add_left hc _

variable [MeasurableSingletonClass α] {S : Finset α}

lemma uniformOn_finset_apply_singleton [DecidableEq α] (S : Finset α) (x : α) :
    uniformOn (S : Set α) {x} = if x ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  split_ifs with hx
  · simp [Finset.inter_singleton_of_mem hx]
  · simp [Finset.inter_singleton_of_notMem hx]

lemma vulnerability_uniformOn (hS : S.Nonempty) :
    vulnerability (uniformOn (S : Set α)) = (S.card : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hS
  simp_rw [vulnerability, uniformOn_finset_apply_singleton]
  refine le_antisymm (iSup_le fun x ↦ ?_) (le_iSup_of_le x₀ (by simp [hx₀]))
  split_ifs <;> simp

lemma postVulnerability_uniformOn (S : Finset α) :
    postVulnerability (uniformOn (S : Set α)) κ =
      (∑ y, ⨆ x ∈ S, κ x {y}) * (S.card : ℝ≥0∞)⁻¹ := by
  classical
  have h (x : α) (y : β) : κ x {y} * uniformOn (S : Set α) {x} =
      ⨆ (_ : x ∈ S), κ x {y} * (S.card : ℝ≥0∞)⁻¹ := by
    by_cases hx : x ∈ S <;> simp [uniformOn_finset_apply_singleton, hx]
  simp_rw [postVulnerability, h, Finset.sum_mul, ENNReal.iSup_mul]

omit [MeasurableSingletonClass α] in
lemma one_le_sum_biSup [MeasurableSingletonClass β] [IsMarkovKernel κ] (hS : S.Nonempty) :
    1 ≤ ∑ y, ⨆ x ∈ S, κ x {y} := by
  obtain ⟨x, hx⟩ := hS
  calc (1 : ℝ≥0∞) = ∑ y, κ x {y} := by simp [sum_measure_singleton (μ := κ x)]
    _ ≤ ∑ y, ⨆ x ∈ S, κ x {y} :=
        Finset.sum_le_sum fun y _ ↦ le_iSup₂ (f := fun x (_ : x ∈ S) ↦ κ x {y}) x hx

omit [MeasurableSingletonClass α] in
lemma sum_biSup_le_card [IsMarkovKernel κ] (S : Finset α) :
    ∑ y, ⨆ x ∈ S, κ x {y} ≤ Fintype.card β :=
  (Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ prob_le_one).trans_eq (by simp)

/-- The additive leakage of the corner point `π_S`, the uniform prior on a nonempty set `S` of
secrets: `L+(π_S) = (∑_y max_{x ∈ S} C[x, y] - 1) / |S|` (as computed in the examples of Braun et
al., and equation (8) of Alvim et al., CSF 2014). -/
theorem addLeakage_uniformOn (hS : S.Nonempty) :
    addLeakage (uniformOn (S : Set α)) κ = ((∑ y, ⨆ x ∈ S, κ x {y}).toReal - 1) / S.card := by
  rw [addLeakage, postVulnerability_uniformOn, vulnerability_uniformOn hS]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  ring

/-- **Corollary 6.5 of Braun, Chatzikokolakis and Palamidessi**: the worst-case additive leakage
`ML+` is attained on a corner point, the uniform prior on some nonempty set `S` of secrets. -/
theorem exists_isGreatest_addLeakage_uniformOn [Finite α] [Nonempty α]
    [MeasurableSingletonClass β] [IsMarkovKernel κ] :
    ∃ S : Finset α, S.Nonempty ∧
      IsGreatest {r | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ addLeakage μ κ = r}
        (addLeakage (uniformOn (S : Set α)) κ) := by
  classical
  have := Fintype.ofFinite α
  set σ : Finset α → ℝ≥0∞ := fun S ↦ ∑ y, ⨆ x ∈ S, κ x {y}
  set f : Finset α → ℝ≥0∞ := fun S ↦ (σ S - 1) / S.card
  set T := Finset.univ.filter fun S : Finset α ↦ S.Nonempty
  obtain ⟨S₀, hS₀T, hmax⟩ :=
    T.exists_max_image f ⟨Finset.univ, by simp [T, Finset.univ_nonempty]⟩
  have hS₀ : S₀.Nonempty := (Finset.mem_filter.1 hS₀T).2
  have hσ (S : Finset α) : σ S ≠ ∞ := ne_top_of_le_ne_top (by simp) (sum_biSup_le_card S)
  have hcard {S : Finset α} (hS : S.Nonempty) : (S.card : ℝ≥0∞) ≠ 0 := by simp [hS.ne_empty]
  have hL : ∀ S : Finset α, S.Nonempty → σ S ≤ 1 + f S₀ * S.card := fun S hS ↦ by
    have h1 : f S ≤ f S₀ := hmax S (by simp [T, hS])
    rw [ENNReal.div_le_iff (hcard hS) (by simp)] at h1
    exact tsub_le_iff_left.1 h1
  have hLtop : f S₀ ≠ ∞ := ENNReal.div_ne_top (by simpa using hσ S₀) (hcard hS₀)
  have hval : addLeakage (uniformOn (S₀ : Set α)) κ = (f S₀).toReal := by
    rw [addLeakage_uniformOn hS₀, ENNReal.toReal_div, ENNReal.toReal_sub_of_le
      (one_le_sum_biSup hS₀) (hσ S₀)]
    simp
  have := isProbabilityMeasure_uniformOn (S₀.finite_toSet) (by simpa using hS₀)
  refine ⟨S₀, hS₀, ⟨uniformOn (S₀ : Set α), this, rfl⟩, ?_⟩
  rintro r ⟨μ, hμ, rfl⟩
  have key := sum_iSup_mul_le_of_forall_finset (fun x y ↦ κ x {y}) (f S₀) hL (fun x ↦ μ {x})
  rw [sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one] at key
  rw [hval, addLeakage, sub_le_iff_le_add, ← ENNReal.toReal_add hLtop (vulnerability_ne_top μ)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hLtop, vulnerability_ne_top μ⟩)
    (key.trans_eq (add_comm _ _))

/-- **Corollary 6.5 of Braun et al.**, value form: `ML+ = L+(π_S)` for some corner point `π_S`. -/
theorem exists_maxAddLeakage_eq [Finite α] [Nonempty α] [MeasurableSingletonClass β]
    [IsMarkovKernel κ] :
    ∃ S : Finset α, S.Nonempty ∧ maxAddLeakage κ = addLeakage (uniformOn (S : Set α)) κ := by
  obtain ⟨S, hS, h⟩ := exists_isGreatest_addLeakage_uniformOn (κ := κ)
  exact ⟨S, hS, h.csSup_eq⟩

end CornerPoints

end InformationTheory
