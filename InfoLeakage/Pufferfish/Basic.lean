/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability

/-!
# Pufferfish privacy

This file formalizes the Pufferfish framework of D. Kifer and A. Machanavajjhala, *Pufferfish: A
framework for mathematical privacy definitions*, ACM Trans. Database Syst. 39(1), Article 3, 2014
(doi:10.1145/2514689; conference version: *A rigorous and customizable framework for privacy*,
PODS 2012). There is no arXiv version; result numbers follow the authors' version of the journal
paper and its online appendix.

A Pufferfish privacy definition is specified by potential secrets `S` (events on the unknown
database `Data`), discriminative pairs `Spairs ⊆ S × S` (secrets an attacker must not be able to
tell apart) and data evolution scenarios `D` (a set of priors `θ` on databases, one per attacker).
A mechanism `M` satisfies `ε-PufferFish(S, Spairs, D)` if for every pair `(sᵢ, sⱼ)` and every
`θ ∈ D` giving both secrets positive probability, the output laws of `M(Data)` given `sᵢ` and
given `sⱼ` are within a factor `e^ε` of each other.

**Setting.** Mechanisms are kernels `M : Kernel 𝒟 Y`, priors are measures on `𝒟`, secrets are
sets `Set 𝒟`, and `P(M(Data) ∈ · | s, θ)` is `M ∘ₘ θ[|s]`. The general results hold for arbitrary
measurable spaces; the Bayesian semantics are stated for a discrete database space and a countable
output space. For the results about records (Sections 3.2 and 6), a database is a function
`D : H → R` from a finite population `H` to record slots, where a distinguished value `o : R`
means "no record" (`¬σᵢ`) and `D i = t ≠ o` means "the record of `hᵢ` is in the data with value
`t`" (`σ_(i,t)`); the paper's tuple domain `T` is `R \ {o}` (e.g. `R = Option T`, `o = none`).

## Main definitions

* `IsPufferfish M Spairs Θ ε`: `ε-PufferFish(S, Spairs, D)` (Definition 3.4).
* `Pufferfish.noAssumptionPairs o`: the discriminative pairs of equation (4).
* `Pufferfish.AddRemoveAdj o`: databases differing in the presence of one tuple (Definition 6.1);
  `ε`-differential privacy is `IsEpsDP M (Pufferfish.AddRemoveAdj o) ε`.
* `Pufferfish.dpSecrets o`, `Pufferfish.dpPairs o`: the secrets and pairs of equations (6)–(7).
* `Pufferfish.indepPriors H R`: the evolution scenarios `D*` of equation (8) (independent records).
* `Pufferfish.mixKernel p M₁ M₂`: the mechanism `M_p` of Axiom 5.2.
* `Pufferfish.CondRestInvariant o θ`: the conditional-probability property of Lemma D.1.

## Main statements (paper result → Lean name)

* Definition 3.4, equations (1)–(2) pointwise: `isPufferfish_iff_forall_singleton`.
* Section 3.1 (Bayesian semantics: Pufferfish bounds the odds ratio by `e^{±ε}`): per constraint
  `Pufferfish.comp_cond_le_iff_posterior`; for the whole definition `isPufferfish_iff_posterior`
  (cross-multiplied odds); quotient form `IsPufferfish.oddsRatio_mem_Icc`.
* Theorem 3.1 (no assumptions = no-free-lunch privacy): `isPufferfish_noAssumptionPairs_iff`,
  pointwise `isPufferfish_noAssumptionPairs_iff_forall_singleton`; its two directions for general
  `S`, `Spairs`, `D`: `isPufferfish_of_forall_le_smul`, `IsPufferfish.le_smul_of_separating`.
* Theorem 5.1 (transformation invariance and convexity): `IsPufferfish.comp` (deterministic case
  `IsPufferfish.map`), `IsPufferfish.mix` (for `M_p`) and `IsPufferfish.convexComb` (for any
  kernel with the mixture's rows).
* Theorem 6.1 (`ε`-DP is `ε-PufferFish(S, Spairs, D*)`): `isPufferfish_indepPriors_iff_isEpsDP`.
* Lemma D.1: direction "every `θ ∈ D*` has the property",
  `Pufferfish.condRestInvariant_of_mem_indepPriors` (via
  `Pufferfish.map_cond_eq_cond_of_mem_indepPriors`); converse when `P(¬σⱼ | θ) ≠ 0` for all `j`,
  `Pufferfish.mem_indepPriors_of_condRestInvariant`; the converse fails without that assumption,
  `Pufferfish.correlatedPrior_condRestInvariant` with
  `Pufferfish.correlatedPrior_notMem_indepPriors`.
  Equation (8) parametrization: `Pufferfish.eq_absent_add_present`.
* Theorem 6.2: false as stated, `Pufferfish.exists_not_subset_indepPriors_isPufferfish_iff`;
  corrected statement (a prior `θ ∉ D*` with `P(¬σⱼ | θ) ≠ 0` for all `j`):
  `Pufferfish.exists_isEpsDP_not_isPufferfish_of_notMem`, built from the argument of Appendix D,
  `Pufferfish.exists_isEpsDP_not_isPufferfish`.

## Implementation notes

* `IsPufferfish` is stated for events of the output space, which on a countable output space with
  measurable singletons is exactly the paper's pointwise condition
  (`isPufferfish_iff_forall_singleton`).
* The odds-ratio semantics of Section 3.1 divide by posterior probabilities `P(sⱼ | ω, θ)`, which
  may vanish; the equivalence is proved in cross-multiplied form, and the quotient form is derived
  under the hypothesis that the posterior odds are defined.
* `IsPufferfish` places no restriction on the priors; the results that depend on them assume
  finite (mostly probability) measures, since `θ[|s] = 0` when `θ s = ∞`.
* The paper assumes `ε > 0`. Theorem 6.1 and Theorem 5.1 hold for every real `ε`, Theorem 3.1
  for `ε ≥ 0`; the corrected Theorem 6.2 needs `ε > 0`.

## Notes on the paper

* **Theorem 6.2 is false as stated** (Section 6.1, p. 13, proof in Appendix D). It claims that for
  every `D_other ⊄ D*`, `ε`-differential privacy is not equivalent to
  `ε-PufferFish(S, Spairs, D_other)`. Take two individuals, at least two tuple values, and add to
  `D*` the prior under which both records are always present and perfectly correlated
  (`Pufferfish.correlatedPrior`). It is not in `D*`, but it gives `P(¬σᵢ) = 0` for every `i`, so by
  Definition 3.4 it imposes no constraint, and by Theorem 6.1 the enlarged definition is still
  equivalent to `ε`-DP (`Pufferfish.exists_not_subset_indepPriors_isPufferfish_iff`). The proof
  fails in the converse direction of Lemma D.1: Step 3 handles priors with `P(¬σⱼ | θ) = 0` by
  "taking the limit as `P(¬σⱼ) → 0`", but such priors satisfy the conditional-probability property
  vacuously without being in `D*` (`Pufferfish.correlatedPrior_condRestInvariant`), so the
  converse of Lemma D.1 is false. It holds when every `P(¬σⱼ | θ)` is positive (Step 2 of the
  paper's proof, `Pufferfish.mem_indepPriors_of_condRestInvariant`), and the argument of
  Appendix D then proves Theorem 6.2 for such priors
  (`Pufferfish.exists_isEpsDP_not_isPufferfish_of_notMem`).
* Lemma D.1 (Appendix D, p. App–4): the displayed property reads
  `P(Data = D ∪ {r_j = t_j} | σ_(i,t))`; the indices should be `rᵢ = t` (and `D` should range over
  databases without a record of `hᵢ`).
* Proof of Theorem 3.1 (Appendix A): in Case 2 the first line `P(M(Data) = r | s, θ)` should read
  `= ω`; in Case 1, "the randomness in `M1`" should read `M`.
* Proof of Theorem 5.1 (Appendix B, Step 1): "for any `(sᵢ, sⱼ) ∈ S`" should read `∈ Spairs`.
* Proof of Theorem 6.2 (Appendix D, Step 1): the last display ends with `∈ [e^{-ε}, ε]`, which
  should read `[e^{-ε}, e^ε]`.

## Not formalized

* `ε`-indistinguishability (Section 6.2), hedging privacy (Section 7), continuous attributes and
  aggregates (Section 8), composition (Section 9) and constraints / prior releases (Section 10).
* Results of Kifer–Machanavajjhala, *No free lunch in data privacy*, SIGMOD 2011, beyond the
  equivalence of no-free-lunch privacy with Pufferfish without assumptions (Theorem 3.1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace InformationTheory

variable {𝒟 Y Z : Type*} {m𝒟 : MeasurableSpace 𝒟} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z}

/-! ### The definition -/

/-- **`ε`-Pufferfish privacy** `ε-PufferFish(S, Spairs, D)` (Definition 3.4 of
Kifer–Machanavajjhala). The potential secrets are events `s : Set 𝒟` on the database `Data`, the
discriminative pairs form a set `Spairs` of pairs of secrets (the set `S` of potential secrets only
serves as the domain of `Spairs` and does not enter the condition), and the data evolution
scenarios form a set `Θ` of priors `θ` on databases. The mechanism `M` satisfies the definition if,
for every discriminative pair `(sᵢ, sⱼ)` and every prior `θ ∈ Θ` with `θ sᵢ ≠ 0` and `θ sⱼ ≠ 0`,
the output law `M ∘ₘ θ[|sᵢ]` of `M(Data)` given `sᵢ` (under `θ`) and the output law given `sⱼ`
are within a factor `e^ε` of each other, in both directions (equations (1) and (2)).

The condition is stated for events of the output space; on a countable output space with
measurable singletons it is exactly the pointwise condition of the paper,
`P(M(Data) = ω | sᵢ, θ) ≤ e^ε P(M(Data) = ω | sⱼ, θ)`, see `isPufferfish_iff_forall_singleton`.
The priors are meant to be probability measures. Since `θ[|s]` is normalized, any nonzero
finite measure gives the same condition as its normalization; infinite measures misbehave
(`θ[|s] = 0` when `θ s = ∞`, which produces spurious constraints), and every result below that
depends on the priors assumes them finite. -/
def IsPufferfish (M : Kernel 𝒟 Y) (Spairs : Set (Set 𝒟 × Set 𝒟)) (Θ : Set (Measure 𝒟))
    (ε : ℝ) : Prop :=
  ∀ ⦃s s' : Set 𝒟⦄, (s, s') ∈ Spairs → ∀ θ ∈ Θ, θ s ≠ 0 → θ s' ≠ 0 →
    M ∘ₘ θ[|s] ≤ ENNReal.ofReal (exp ε) • (M ∘ₘ θ[|s']) ∧
      M ∘ₘ θ[|s'] ≤ ENNReal.ofReal (exp ε) • (M ∘ₘ θ[|s])

namespace Pufferfish

/-- On a countable space with measurable singletons, `μ ≤ c • ν` can be checked on points. -/
lemma le_smul_iff_forall_singleton [Countable Y] [MeasurableSingletonClass Y] {μ ν : Measure Y}
    {c : ℝ≥0∞} : μ ≤ c • ν ↔ ∀ y, μ {y} ≤ c * ν {y} := by
  refine ⟨fun h y ↦ by simpa using h {y}, fun h ↦ Measure.le_iff.2 fun E hE ↦ ?_⟩
  rw [smul_apply, smul_eq_mul, ← μ.tsum_indicator_apply_singleton E hE,
    ← ν.tsum_indicator_apply_singleton E hE, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y ↦ ?_
  by_cases hyE : y ∈ E <;> simp [hyE, h]

/-- Composition with a kernel is monotone in the measure. -/
lemma comp_mono {μ ν : Measure Y} (h : μ ≤ ν) (A : Kernel Y Z) : A ∘ₘ μ ≤ A ∘ₘ ν :=
  Measure.le_iff.2 fun E hE ↦ by
    rw [Measure.bind_apply hE A.aemeasurable, Measure.bind_apply hE A.aemeasurable]
    exact lintegral_mono' h le_rfl

/-- If `κ x ≤ c • η x` for every `x`, then `κ ∘ₘ μ ≤ c • (η ∘ₘ μ)`. -/
lemma comp_le_smul_comp {κ η : Kernel 𝒟 Y} {c : ℝ≥0∞} (h : ∀ x, κ x ≤ c • η x)
    (μ : Measure 𝒟) : κ ∘ₘ μ ≤ c • (η ∘ₘ μ) :=
  Measure.le_iff.2 fun E hE ↦ by
    rw [smul_apply, smul_eq_mul, Measure.bind_apply hE κ.aemeasurable,
      Measure.bind_apply hE η.aemeasurable, ← lintegral_const_mul _ (η.measurable_coe hE)]
    exact lintegral_mono fun x ↦ by simpa using h x E

end Pufferfish

variable {M M₁ M₂ : Kernel 𝒟 Y} {Spairs : Set (Set 𝒟 × Set 𝒟)} {Θ : Set (Measure 𝒟)} {ε : ℝ}

/-- On a countable output space with measurable singletons, `IsPufferfish` is literally
equations (1) and (2) of Definition 3.4: `P(M(Data) = ω | sᵢ, θ) ≤ e^ε P(M(Data) = ω | sⱼ, θ)` and
`P(M(Data) = ω | sⱼ, θ) ≤ e^ε P(M(Data) = ω | sᵢ, θ)` for every output `ω`. -/
theorem isPufferfish_iff_forall_singleton [Countable Y] [MeasurableSingletonClass Y] :
    IsPufferfish M Spairs Θ ε ↔ ∀ ⦃s s' : Set 𝒟⦄, (s, s') ∈ Spairs → ∀ θ ∈ Θ, θ s ≠ 0 →
      θ s' ≠ 0 → ∀ ω : Y, (M ∘ₘ θ[|s]) {ω} ≤ ENNReal.ofReal (exp ε) * (M ∘ₘ θ[|s']) {ω} ∧
        (M ∘ₘ θ[|s']) {ω} ≤ ENNReal.ofReal (exp ε) * (M ∘ₘ θ[|s]) {ω} := by
  simp only [IsPufferfish, Pufferfish.le_smul_iff_forall_singleton, ← forall_and]

/-- `ε-PufferFish` is monotone in `ε`. -/
lemma IsPufferfish.mono {ε' : ℝ} (h : IsPufferfish M Spairs Θ ε) (hε : ε ≤ ε') :
    IsPufferfish M Spairs Θ ε' := by
  have hc (ν : Measure Y) : ENNReal.ofReal (exp ε) • ν ≤ ENNReal.ofReal (exp ε') • ν :=
    Measure.le_iff.2 fun E _ ↦ by simp only [smul_apply, smul_eq_mul]; gcongr
  intro s s' hp θ hθ hs hs'
  obtain ⟨h₁, h₂⟩ := h hp θ hθ hs hs'
  exact ⟨h₁.trans (hc _), h₂.trans (hc _)⟩

/-- `ε-PufferFish` is antitone in the discriminative pairs and in the evolution scenarios: fewer
secrets to protect or fewer attackers give a weaker definition. -/
lemma IsPufferfish.anti {Spairs' : Set (Set 𝒟 × Set 𝒟)} {Θ' : Set (Measure 𝒟)}
    (h : IsPufferfish M Spairs Θ ε) (hS : Spairs' ⊆ Spairs) (hΘ : Θ' ⊆ Θ) :
    IsPufferfish M Spairs' Θ' ε := fun _ _ hp θ hθ ↦ h (hS hp) θ (hΘ hθ)

/-- A prior that gives probability zero to one side of every discriminative pair imposes no
constraint. -/
lemma isPufferfish_insert_iff {θ₀ : Measure 𝒟}
    (h₀ : ∀ ⦃s s' : Set 𝒟⦄, (s, s') ∈ Spairs → θ₀ s = 0 ∨ θ₀ s' = 0) :
    IsPufferfish M Spairs (insert θ₀ Θ) ε ↔ IsPufferfish M Spairs Θ ε := by
  refine ⟨fun h ↦ h.anti subset_rfl (subset_insert _ _), fun h s s' hp θ hθ hs hs' ↦ ?_⟩
  rcases hθ with rfl | hθ
  · exact ((h₀ hp).elim hs hs').elim
  · exact h hp θ hθ hs hs'

/-! ### Theorem 5.1: transformation invariance and convexity -/

/-- **Transformation invariance** (Axiom 5.1; first half of Theorem 5.1 of
Kifer–Machanavajjhala): post-processing the output of an `ε-PufferFish(S, Spairs, D)` mechanism
by any randomized algorithm `A`, with randomness independent of that of `M` (a kernel), preserves
`ε-PufferFish(S, Spairs, D)`. -/
theorem IsPufferfish.comp (h : IsPufferfish M Spairs Θ ε) (A : Kernel Y Z) :
    IsPufferfish (A ∘ₖ M) Spairs Θ ε := by
  intro s s' hp θ hθ hs hs'
  obtain ⟨h₁, h₂⟩ := h hp θ hθ hs hs'
  simp only [← Measure.comp_assoc]
  exact ⟨(Pufferfish.comp_mono h₁ A).trans_eq (Measure.comp_smul _),
    (Pufferfish.comp_mono h₂ A).trans_eq (Measure.comp_smul _)⟩

/-- Deterministic post-processing preserves `ε-PufferFish` (special case of
`IsPufferfish.comp`). -/
theorem IsPufferfish.map (h : IsPufferfish M Spairs Θ ε) {f : Y → Z} (hf : Measurable f) :
    IsPufferfish (M.map f) Spairs Θ ε := by
  rw [← Kernel.deterministic_comp_eq_map hf]
  exact h.comp _

/-- **Convexity** (Axiom 5.2; second half of Theorem 5.1 of Kifer–Machanavajjhala): if `M₁` and
`M₂` satisfy `ε-PufferFish(S, Spairs, D)`, then so does every mechanism `M` with
`M(D) = p M₁(D) + q M₂(D)` for all databases `D`. With `q = 1 - p` and `p ∈ [0, 1]` this is the
algorithm `M_p` that runs `M₁` with probability `p` and `M₂` with probability `1 - p`; the
statement holds for arbitrary weights. -/
theorem IsPufferfish.convexComb (h₁ : IsPufferfish M₁ Spairs Θ ε) (h₂ : IsPufferfish M₂ Spairs Θ ε)
    (p q : ℝ≥0∞) (hM : ∀ D, M D = p • M₁ D + q • M₂ D) : IsPufferfish M Spairs Θ ε := by
  have key (μ : Measure 𝒟) : M ∘ₘ μ = p • (M₁ ∘ₘ μ) + q • (M₂ ∘ₘ μ) := by
    ext E hE
    simp only [Measure.bind_apply hE M.aemeasurable, Measure.bind_apply hE M₁.aemeasurable,
      Measure.bind_apply hE M₂.aemeasurable, hM, add_apply, smul_apply, smul_eq_mul]
    rw [lintegral_add_left ((M₁.measurable_coe hE).const_mul p), lintegral_const_mul _
      (M₁.measurable_coe hE), lintegral_const_mul _ (M₂.measurable_coe hE)]
  have step {μ ν : Measure 𝒟} (hμ₁ : M₁ ∘ₘ μ ≤ ENNReal.ofReal (exp ε) • (M₁ ∘ₘ ν))
      (hμ₂ : M₂ ∘ₘ μ ≤ ENNReal.ofReal (exp ε) • (M₂ ∘ₘ ν)) :
      M ∘ₘ μ ≤ ENNReal.ofReal (exp ε) • (M ∘ₘ ν) := Measure.le_iff.2 fun E hE ↦ by
    have e₁ := Measure.le_iff.1 hμ₁ E hE
    have e₂ := Measure.le_iff.1 hμ₂ E hE
    simp only [key, add_apply, smul_apply, smul_eq_mul] at e₁ e₂ ⊢
    calc p * (M₁ ∘ₘ μ) E + q * (M₂ ∘ₘ μ) E
        ≤ p * (ENNReal.ofReal (exp ε) * (M₁ ∘ₘ ν) E) +
          q * (ENNReal.ofReal (exp ε) * (M₂ ∘ₘ ν) E) := by gcongr
      _ = _ := by ring
  intro s s' hp θ hθ hs hs'
  obtain ⟨a₁, b₁⟩ := h₁ hp θ hθ hs hs'
  obtain ⟨a₂, b₂⟩ := h₂ hp θ hθ hs hs'
  exact ⟨step a₁ a₂, step b₁ b₂⟩

/-- The mechanism `M_p` of Axiom 5.2: run `M₁` with probability `p` and `M₂` with probability
`1 - p`, i.e. `M_p(D) = p M₁(D) + (1 - p) M₂(D)`. -/
noncomputable def Pufferfish.mixKernel (p : ℝ≥0∞) (M₁ M₂ : Kernel 𝒟 Y) : Kernel 𝒟 Y where
  toFun D := p • M₁ D + (1 - p) • M₂ D
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [add_apply, smul_apply, smul_eq_mul]
    exact ((M₁.measurable_coe hs).const_mul p).add ((M₂.measurable_coe hs).const_mul _)

lemma Pufferfish.mixKernel_apply (p : ℝ≥0∞) (M₁ M₂ : Kernel 𝒟 Y) (D : 𝒟) :
    Pufferfish.mixKernel p M₁ M₂ D = p • M₁ D + (1 - p) • M₂ D := rfl

/-- For `p ≤ 1`, the mixture of two Markov kernels is a Markov kernel. -/
lemma Pufferfish.isMarkovKernel_mixKernel {p : ℝ≥0∞} (hp : p ≤ 1) [IsMarkovKernel M₁]
    [IsMarkovKernel M₂] : IsMarkovKernel (Pufferfish.mixKernel p M₁ M₂) :=
  ⟨fun D ↦ ⟨by simp [Pufferfish.mixKernel_apply, add_tsub_cancel_of_le hp]⟩⟩

/-- **Convexity** (second half of Theorem 5.1 of Kifer–Machanavajjhala) for the mechanism `M_p`
that runs `M₁` with probability `p` and `M₂` with probability `1 - p`. -/
theorem IsPufferfish.mix (h₁ : IsPufferfish M₁ Spairs Θ ε) (h₂ : IsPufferfish M₂ Spairs Θ ε)
    (p : ℝ≥0∞) : IsPufferfish (Pufferfish.mixKernel p M₁ M₂) Spairs Θ ε :=
  h₁.convexComb h₂ p (1 - p) fun _ ↦ rfl

/-! ### Section 3.1: Bayesian (odds-ratio) semantics -/

/-- The joint law of `(Data, M(Data))` under the prior `θ` puts mass
`θ(s) · P(M(Data) ∈ E | s, θ)` on `{Data ∈ s, M(Data) ∈ E}`. -/
lemma Pufferfish.compProd_snd_inter_fst {θ : Measure 𝒟} [SFinite θ] [IsSFiniteKernel M]
    {s : Set 𝒟} (hs : MeasurableSet s) (hθs : θ s ≠ 0) (hθs' : θ s ≠ ∞) {E : Set Y}
    (hE : MeasurableSet E) :
    (θ ⊗ₘ M) (Prod.snd ⁻¹' E ∩ Prod.fst ⁻¹' s) = θ s * (M ∘ₘ θ[|s]) E := by
  have : Prod.snd ⁻¹' E ∩ Prod.fst ⁻¹' s = s ×ˢ E := by ext; simp [and_comm]
  rw [this, Measure.compProd_apply_prod hs hE, ProbabilityTheory.cond, Measure.comp_smul,
    smul_apply, smul_eq_mul, Measure.bind_apply hE M.aemeasurable, ← mul_assoc,
    ENNReal.mul_inv_cancel hθs hθs', one_mul]

/-- **Bayesian semantics of one Pufferfish constraint** (Section 3.1 of Kifer–Machanavajjhala,
"a simple calculation shows ..."). For a prior `θ` with `θ s ≠ 0 ≠ θ s'` and an output event `E`,
`P(M(Data) ∈ E | s, θ) ≤ c · P(M(Data) ∈ E | s', θ)` holds if and only if the posterior odds of
`s` to `s'` after observing `M(Data) ∈ E` are at most `c` times the prior odds:
`P(s | M(Data) ∈ E, θ) · P(s' | θ) ≤ c · P(s' | M(Data) ∈ E, θ) · P(s | θ)`. The posterior is the
conditional probability under the joint law `θ ⊗ₘ M` of `(Data, M(Data))`. The odds are written
in cross-multiplied form, which is meaningful even when the posterior probabilities vanish; see
`IsPufferfish.oddsRatio_mem_Icc` for the quotient form. -/
theorem Pufferfish.comp_cond_le_iff_posterior {θ : Measure 𝒟} [IsFiniteMeasure θ]
    [IsFiniteKernel M] {s s' : Set 𝒟} (hs : MeasurableSet s) (hs' : MeasurableSet s')
    (hθs : θ s ≠ 0) (hθs' : θ s' ≠ 0) {E : Set Y} (hE : MeasurableSet E) (c : ℝ≥0∞) :
    (M ∘ₘ θ[|s]) E ≤ c * (M ∘ₘ θ[|s']) E ↔
      (θ ⊗ₘ M)[Prod.fst ⁻¹' s | Prod.snd ⁻¹' E] * θ s' ≤
        c * ((θ ⊗ₘ M)[Prod.fst ⁻¹' s' | Prod.snd ⁻¹' E] * θ s) := by
  have hE' : MeasurableSet (Prod.snd ⁻¹' E : Set (𝒟 × Y)) := measurable_snd hE
  rw [cond_apply hE', cond_apply hE', compProd_snd_inter_fst hs hθs (measure_ne_top _ _) hE,
    compProd_snd_inter_fst hs' hθs' (measure_ne_top _ _) hE]
  set P := (θ ⊗ₘ M) (Prod.snd ⁻¹' E)
  set A := (M ∘ₘ θ[|s]) E
  set B := (M ∘ₘ θ[|s']) E
  by_cases hP : P = 0
  · have hA : θ s * A = 0 := le_zero_iff.1 <| hP ▸
      (compProd_snd_inter_fst hs hθs (measure_ne_top _ _) hE (M := M)).symm.le.trans
        (measure_mono inter_subset_left)
    have hB : θ s' * B = 0 := le_zero_iff.1 <| hP ▸
      (compProd_snd_inter_fst hs' hθs' (measure_ne_top _ _) hE (M := M)).symm.le.trans
        (measure_mono inter_subset_left)
    rw [mul_eq_zero, or_iff_right hθs] at hA
    rw [mul_eq_zero, or_iff_right hθs'] at hB
    simp [hA, hB]
  · have hP' : P ≠ ∞ := measure_ne_top _ _
    have hK : P⁻¹ * θ s * θ s' ≠ 0 := by simp [hθs, hθs', hP']
    have hK' : P⁻¹ * θ s * θ s' ≠ ∞ := by
      simp [hP, hθs, hθs', measure_ne_top, ENNReal.mul_eq_top]
    rw [show P⁻¹ * (θ s * A) * θ s' = (P⁻¹ * θ s * θ s') * A by ring,
      show c * (P⁻¹ * (θ s' * B) * θ s) = (P⁻¹ * θ s * θ s') * (c * B) by ring,
      ENNReal.mul_le_mul_iff_right hK hK']

/-- **Bayesian semantics of Pufferfish** (Section 3.1 of Kifer–Machanavajjhala): on a discrete
database space and a countable output space, `M` satisfies `ε-PufferFish(S, Spairs, D)` if and
only if for every discriminative pair `(sᵢ, sⱼ)`, every attacker `θ ∈ D` with `θ sᵢ ≠ 0 ≠ θ sⱼ`
and every output `ω`, the odds ratio of `sᵢ` to `sⱼ` (posterior odds after seeing `M(Data) = ω`,
divided by the prior odds) lies in `[e^{-ε}, e^ε]`. The odds ratio bound is written in
cross-multiplied form, `P(sᵢ | ω) P(sⱼ) ≤ e^ε P(sⱼ | ω) P(sᵢ)` and symmetrically, which avoids
dividing by posterior probabilities that may vanish; `IsPufferfish.oddsRatio_mem_Icc` gives the
quotient form. -/
theorem isPufferfish_iff_posterior [DiscreteMeasurableSpace 𝒟] [Countable Y]
    [MeasurableSingletonClass Y] [IsFiniteKernel M] (hΘ : ∀ θ ∈ Θ, IsFiniteMeasure θ) :
    IsPufferfish M Spairs Θ ε ↔ ∀ ⦃s s' : Set 𝒟⦄, (s, s') ∈ Spairs → ∀ θ ∈ Θ, θ s ≠ 0 →
      θ s' ≠ 0 → ∀ ω : Y,
        (θ ⊗ₘ M)[Prod.fst ⁻¹' s | Prod.snd ⁻¹' {ω}] * θ s' ≤
          ENNReal.ofReal (exp ε) * ((θ ⊗ₘ M)[Prod.fst ⁻¹' s' | Prod.snd ⁻¹' {ω}] * θ s) ∧
        (θ ⊗ₘ M)[Prod.fst ⁻¹' s' | Prod.snd ⁻¹' {ω}] * θ s ≤
          ENNReal.ofReal (exp ε) * ((θ ⊗ₘ M)[Prod.fst ⁻¹' s | Prod.snd ⁻¹' {ω}] * θ s') := by
  rw [isPufferfish_iff_forall_singleton]
  refine forall₂_congr fun s s' ↦ forall_congr' fun _ ↦ forall₂_congr fun θ hθ ↦
    forall₂_congr fun hs hs' ↦ forall_congr' fun ω ↦ ?_
  have := hΘ θ hθ
  rw [Pufferfish.comp_cond_le_iff_posterior (.of_discrete) (.of_discrete) hs hs'
      (measurableSet_singleton ω),
    Pufferfish.comp_cond_le_iff_posterior (.of_discrete) (.of_discrete) hs' hs
      (measurableSet_singleton ω)]

/-- **Odds-ratio semantics** (Section 3.1 of Kifer–Machanavajjhala), quotient form: if `M`
satisfies `ε-PufferFish(S, Spairs, D)`, then for every discriminative pair `(sᵢ, sⱼ)`, every
attacker `θ ∈ D` with `θ sᵢ ≠ 0 ≠ θ sⱼ` and every output `ω` after which the posterior odds of
`sᵢ` to `sⱼ` are defined (`P(sⱼ | M(Data) = ω, θ) ≠ 0`), the odds ratio
`(P(sᵢ | ω, θ) / P(sⱼ | ω, θ)) / (P(sᵢ | θ) / P(sⱼ | θ))` lies in `[e^{-ε}, e^ε]`: an attacker who
thinks `sᵢ` is `α` times as likely as `sⱼ` thinks it at least `e^{-ε} α` and at most `e^ε α` times
as likely after seeing `ω`. -/
theorem IsPufferfish.oddsRatio_mem_Icc [DiscreteMeasurableSpace 𝒟] [Countable Y]
    [MeasurableSingletonClass Y] [IsFiniteKernel M] (h : IsPufferfish M Spairs Θ ε)
    {s s' : Set 𝒟} (hp : (s, s') ∈ Spairs) {θ : Measure 𝒟} (hθ : θ ∈ Θ) [IsFiniteMeasure θ]
    (hs : θ s ≠ 0) (hs' : θ s' ≠ 0) {ω : Y}
    (hω : (θ ⊗ₘ M)[Prod.fst ⁻¹' s' | Prod.snd ⁻¹' {ω}] ≠ 0) :
    ((θ ⊗ₘ M)[|Prod.snd ⁻¹' {ω}]).real (Prod.fst ⁻¹' s) /
        ((θ ⊗ₘ M)[|Prod.snd ⁻¹' {ω}]).real (Prod.fst ⁻¹' s') / (θ.real s / θ.real s') ∈
      Icc (exp (-ε)) (exp ε) := by
  obtain ⟨h₁, h₂⟩ := (isPufferfish_iff_forall_singleton.1 h) hp θ hθ hs hs' ω
  rw [Pufferfish.comp_cond_le_iff_posterior .of_discrete .of_discrete hs hs'
    (measurableSet_singleton ω)] at h₁
  rw [Pufferfish.comp_cond_le_iff_posterior .of_discrete .of_discrete hs' hs
    (measurableSet_singleton ω)] at h₂
  set a := (θ ⊗ₘ M)[Prod.fst ⁻¹' s | Prod.snd ⁻¹' {ω}]
  set b := (θ ⊗ₘ M)[Prod.fst ⁻¹' s' | Prod.snd ⁻¹' {ω}]
  have ha : a ≠ ∞ := measure_ne_top _ _
  have hb : b ≠ ∞ := measure_ne_top _ _
  have hc : ENNReal.ofReal (exp ε) ≠ ∞ := ENNReal.ofReal_ne_top
  have r₁ := ENNReal.toReal_mono (by finiteness) h₁
  have r₂ := ENNReal.toReal_mono (by finiteness) h₂
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos ε).le] at r₁ r₂
  simp only [measureReal_def]
  have hb' : 0 < b.toReal := ENNReal.toReal_pos hω hb
  have hu : 0 < (θ s).toReal := ENNReal.toReal_pos hs (measure_ne_top _ _)
  have hv : 0 < (θ s').toReal := ENNReal.toReal_pos hs' (measure_ne_top _ _)
  rw [div_div_div_eq, mul_comm b.toReal]
  have hbu : 0 < (θ s).toReal * b.toReal := mul_pos hu hb'
  constructor
  · rw [le_div_iff₀ hbu, exp_neg, inv_mul_le_iff₀ (exp_pos ε)]
    linarith
  · rw [div_le_iff₀ hbu]
    linarith

/-! ### Theorem 3.1: Pufferfish without assumptions -/

/-- If every two databases have output laws within a factor `e^ε` (the "no-free-lunch privacy"
of Kifer–Machanavajjhala, SIGMOD 2011), then `M` satisfies `ε-PufferFish(S, Spairs, D)` for
**every** choice of secrets, discriminative pairs and (finite) priors. This is the "if" direction
of Theorem 3.1 of Kifer–Machanavajjhala (Case 2 of its proof, Appendix A), which uses no property
of `S`, `Spairs` or `D`. -/
theorem isPufferfish_of_forall_le_smul (h : ∀ D D', M D ≤ ENNReal.ofReal (exp ε) • M D')
    (hΘ : ∀ θ ∈ Θ, IsFiniteMeasure θ) : IsPufferfish M Spairs Θ ε := by
  set c := ENNReal.ofReal (exp ε)
  have key (μ ν : Measure 𝒟) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
      M ∘ₘ μ ≤ c • (M ∘ₘ ν) := by
    have h' (D : 𝒟) : M D ≤ c • Kernel.const 𝒟 (M ∘ₘ ν) D := Measure.le_iff.2 fun E hE ↦ by
      rw [Kernel.const_apply, smul_apply, smul_eq_mul, Measure.bind_apply hE M.aemeasurable,
        ← lintegral_const_mul _ (M.measurable_coe hE)]
      calc M D E = ∫⁻ _, M D E ∂ν := by simp
        _ ≤ ∫⁻ D', c * M D' E ∂ν := lintegral_mono fun D' ↦ by simpa using h D D' E
    simpa using Pufferfish.comp_le_smul_comp h' μ
  intro s s' _ θ hθ hs hs'
  have := hΘ θ hθ
  have := cond_isProbabilityMeasure hs
  have := cond_isProbabilityMeasure hs'
  exact ⟨key _ _, key _ _⟩

/-- The prior `θ = ½ δ_{D₁} + ½ δ_{D₂}` used in the proof of Theorem 3.1, conditioned on a
secret true of `D₁` but not of `D₂`, is the point mass at `D₁`. -/
lemma Pufferfish.cond_half_dirac_add_dirac [MeasurableSingletonClass 𝒟] {D₁ D₂ : 𝒟} {s : Set 𝒟}
    (h₁ : D₁ ∈ s) (h₂ : D₂ ∉ s) :
    ((2⁻¹ : ℝ≥0∞) • (Measure.dirac D₁ + Measure.dirac D₂))[|s] = Measure.dirac D₁ := by
  classical
  have hs : ((2⁻¹ : ℝ≥0∞) • (Measure.dirac D₁ + Measure.dirac D₂)) s = 2⁻¹ := by
    simp [Measure.dirac_apply, h₁, h₂]
  rw [ProbabilityTheory.cond, hs, Measure.restrict_smul, Measure.restrict_add,
    restrict_dirac, restrict_dirac]
  simp only [h₁, h₂, ↓reduceIte, add_zero, smul_smul, inv_inv,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_smul]

/-- If `M` satisfies `ε-PufferFish(S, Spairs, D)` with `ε ≥ 0`, where `D` contains every prior
`½ δ_{D₁} + ½ δ_{D₂}` and any two distinct databases are told apart by some discriminative pair
(one secret is true of `D₁` only, the other of `D₂` only), then the output laws of any two
databases are within a factor `e^ε`. This is the "only if" direction of Theorem 3.1 of
Kifer–Machanavajjhala (Case 1 of its proof, Appendix A), stated for general `S`, `Spairs`,
`D`. -/
theorem IsPufferfish.le_smul_of_separating [MeasurableSingletonClass 𝒟]
    (h : IsPufferfish M Spairs Θ ε) (hε : 0 ≤ ε)
    (hΘ : ∀ D₁ D₂ : 𝒟, (2⁻¹ : ℝ≥0∞) • (Measure.dirac D₁ + Measure.dirac D₂) ∈ Θ)
    (hsep : ∀ D₁ D₂ : 𝒟, D₁ ≠ D₂ → ∃ s s', ((s, s') ∈ Spairs ∨ (s', s) ∈ Spairs) ∧
      D₁ ∈ s ∧ D₂ ∉ s ∧ D₂ ∈ s' ∧ D₁ ∉ s') (D₁ D₂ : 𝒟) :
    M D₁ ≤ ENNReal.ofReal (exp ε) • M D₂ := by
  rcases eq_or_ne D₁ D₂ with rfl | hne
  · refine Measure.le_iff.2 fun E _ ↦ ?_
    rw [smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left (zero_le) (by simpa using one_le_exp hε)
  obtain ⟨s, s', hp, h₁, h₂, h₂', h₁'⟩ := hsep D₁ D₂ hne
  set θ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac D₁ + Measure.dirac D₂)
  have hθs : θ s ≠ 0 := by simp [θ, Measure.dirac_apply, h₁]
  have hθs' : θ s' ≠ 0 := by simp [θ, Measure.dirac_apply, h₂']
  have e₁ : M ∘ₘ θ[|s] = M D₁ := by
    rw [Pufferfish.cond_half_dirac_add_dirac h₁ h₂, Measure.dirac_bind M.measurable]
  have e₂ : M ∘ₘ θ[|s'] = M D₂ := by
    rw [show θ = (2⁻¹ : ℝ≥0∞) • (Measure.dirac D₂ + Measure.dirac D₁) by rw [add_comm],
      Pufferfish.cond_half_dirac_add_dirac h₂' h₁', Measure.dirac_bind M.measurable]
  rcases hp with hp | hp
  · simpa [e₁, e₂] using (h hp θ (hΘ D₁ D₂) hθs hθs').1
  · simpa [e₁, e₂] using (h hp θ (hΘ D₁ D₂) hθs' hθs).2

/-! ### Databases of individual records -/

/-! We model the paper's databases (Section 2) as functions `D : H → R` from the finite
population `H = {h₁, …, h_N}` of individuals to record slots: `D i = o` for a distinguished value
`o : R` means that individual `hᵢ` has no record in the data (`¬σᵢ`), and `D i = t ≠ o` means that
the record `rᵢ` of `hᵢ` is in the data with value `t` (`σ_(i,t)`). So the tuple domain `T` of the
paper is `R \ {o}`; for instance `R = Option T` with `o = none`. Each individual has at most one
record, as assumed in Section 2 of the paper. -/

section Database

variable {H R : Type*} {mR : MeasurableSpace R}

/-- The discriminative pairs of equation (4) of Kifer–Machanavajjhala, for Pufferfish without
assumptions (Section 3.2): `(σ_(i,ta), σ_(i,tb))` for all individuals `i` and tuple values
`ta, tb`, and `(σᵢ, ¬σᵢ)` for all individuals `i`. -/
def Pufferfish.noAssumptionPairs (o : R) : Set (Set (H → R) × Set (H → R)) :=
  {p | ∃ i ta tb, ta ≠ o ∧ tb ≠ o ∧ p = ({D | D i = ta}, {D | D i = tb})} ∪
    {p | ∃ i, p = ({D | D i ≠ o}, {D | D i = o})}

/-- **Theorem 3.1 of Kifer–Machanavajjhala** (Pufferfish with no assumptions is no-free-lunch
privacy). With the discriminative pairs of equation (4) and `D` the set of all probability
distributions over databases, a mechanism `M` satisfies `ε-PufferFish(S, Spairs, D)` if and only
if `M(D₁) ≤ e^ε M(D₂)` for every two databases `D₁, D₂` (as measures; on a countable output space
this is `e^{-ε} P(M(D₂) = ω) ≤ P(M(D₁) = ω) ≤ e^ε P(M(D₂) = ω)` for every output `ω`, see
`isPufferfish_noAssumptionPairs_iff_forall_singleton`). The paper assumes `ε > 0`; `ε ≥ 0`
suffices. -/
theorem isPufferfish_noAssumptionPairs_iff [Finite H] [MeasurableSingletonClass R] (o : R)
    {M : Kernel (H → R) Y} (hε : 0 ≤ ε) :
    IsPufferfish M (Pufferfish.noAssumptionPairs o) {θ | IsProbabilityMeasure θ} ε ↔
      ∀ D₁ D₂, M D₁ ≤ ENNReal.ofReal (exp ε) • M D₂ := by
  refine ⟨fun h ↦ h.le_smul_of_separating hε (fun D₁ D₂ ↦ ?_) fun D₁ D₂ hne ↦ ?_,
    fun h ↦ isPufferfish_of_forall_le_smul h fun θ hθ ↦ by have : IsProbabilityMeasure θ := hθ
                                                           infer_instance⟩
  · refine ⟨?_⟩
    simp [ENNReal.inv_two_add_inv_two]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    by_cases h₁ : D₁ i = o <;> by_cases h₂ : D₂ i = o
    · exact absurd (h₁.trans h₂.symm) hi
    · exact ⟨{D | D i = o}, {D | D i ≠ o}, Or.inr (Or.inr ⟨i, rfl⟩), h₁, h₂, h₂, by simp [h₁]⟩
    · exact ⟨{D | D i ≠ o}, {D | D i = o}, Or.inl (Or.inr ⟨i, rfl⟩), h₁, by simp [h₂], h₂, h₁⟩
    · exact ⟨{D | D i = D₁ i}, {D | D i = D₂ i},
        Or.inl (Or.inl ⟨i, D₁ i, D₂ i, h₁, h₂, rfl⟩), rfl, Ne.symm hi, rfl, hi⟩

/-- **Theorem 3.1 of Kifer–Machanavajjhala**, pointwise form on a countable output space. -/
theorem isPufferfish_noAssumptionPairs_iff_forall_singleton [Finite H]
    [MeasurableSingletonClass R] [Countable Y] [MeasurableSingletonClass Y] (o : R)
    {M : Kernel (H → R) Y} (hε : 0 ≤ ε) :
    IsPufferfish M (Pufferfish.noAssumptionPairs o) {θ | IsProbabilityMeasure θ} ε ↔
      ∀ D₁ D₂ (ω : Y), M D₁ {ω} ≤ ENNReal.ofReal (exp ε) * M D₂ {ω} := by
  simp only [isPufferfish_noAssumptionPairs_iff o hε, Pufferfish.le_smul_iff_forall_singleton]

/-! ### Section 6.1: differential privacy as an instance of Pufferfish -/

/-- Databases differing in the presence of one tuple (Definition 6.1 of Kifer–Machanavajjhala):
`D` and `D'` differ exactly at one individual `i`, whose record is absent from one of them. So `D'`
is obtained from `D` by deleting or by adding the record of `i`. -/
def Pufferfish.AddRemoveAdj (o : R) (D D' : H → R) : Prop :=
  ∃ i, D i ≠ D' i ∧ (D i = o ∨ D' i = o) ∧ ∀ j, j ≠ i → D j = D' j

/-- The potential secrets of equation (6) of Kifer–Machanavajjhala: `σ_(i,t)` ("the record of
`hᵢ` is in the data and has value `t`") for every individual `i` and tuple value `t`, and `¬σᵢ`
("the data has no record of `hᵢ`") for every individual `i`. -/
def Pufferfish.dpSecrets (o : R) : Set (Set (H → R)) :=
  {s | ∃ i t, t ≠ o ∧ s = {D | D i = t}} ∪ {s | ∃ i, s = {D | D i = o}}

/-- The discriminative pairs of equation (7) of Kifer–Machanavajjhala: `(σ_(i,t), ¬σᵢ)` for every
individual `i` and tuple value `t`. -/
def Pufferfish.dpPairs (o : R) : Set (Set (H → R) × Set (H → R)) :=
  {p | ∃ i t, t ≠ o ∧ p = ({D | D i = t}, {D | D i = o})}

lemma Pufferfish.dpPairs_subset (o : R) :
    Pufferfish.dpPairs (H := H) o ⊆ Pufferfish.dpSecrets o ×ˢ Pufferfish.dpSecrets o := by
  rintro _ ⟨i, t, ht, rfl⟩
  exact ⟨Or.inl ⟨i, t, ht, rfl⟩, Or.inr ⟨i, rfl⟩⟩

variable (H R) in
/-- The data evolution scenarios `D*` of equation (8) of Kifer–Machanavajjhala: the presence,
absence and record value of each individual are independent of those of the other individuals,
i.e. the prior is a product `θ = ⨂ᵢ qᵢ` of laws `qᵢ` of the record slots. In the paper's
parametrization `qᵢ{o} = 1 - πᵢ` (absence) and `qᵢ{t} = πᵢ fᵢ(t)` for `t ≠ o`; every probability
measure on `R` is of this form (`πᵢ = 1 - qᵢ{o}`, `fᵢ = qᵢ[|{o}ᶜ]`, any `fᵢ` if `πᵢ = 0`). -/
def Pufferfish.indepPriors [Fintype H] : Set (Measure (H → R)) :=
  {θ | ∃ q : H → Measure R, (∀ i, IsProbabilityMeasure (q i)) ∧ θ = Measure.pi q}

/-- Every law `q` of a record slot has the form used in equation (8) of Kifer–Machanavajjhala:
`q = (1 - π) δ_o + π f` with presence probability `π = q {o}ᶜ` and record-value law
`f = q[|{o}ᶜ]` (a probability measure on the tuple values when `π ≠ 0`). Hence
`Pufferfish.indepPriors` is exactly the set `D*` of all distributions of the form (8). -/
lemma Pufferfish.eq_absent_add_present [MeasurableSingletonClass R] (q : Measure R)
    [IsFiniteMeasure q] (o : R) :
    q = q {o} • Measure.dirac o + q {o}ᶜ • q[|{o}ᶜ] := by
  ext t ht
  have h := cond_add_cond_compl_eq (measurableSet_singleton o) q (t := t)
  rw [cond_mul_eq_inter (measurableSet_singleton o)] at h
  rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, ← h, mul_comm (q {o}ᶜ)]
  congr 1
  by_cases hot : o ∈ t
  · rw [inter_eq_left.2 (singleton_subset_iff.2 hot), Measure.dirac_apply_of_mem hot, mul_one]
  · rw [singleton_inter_eq_empty.2 hot, measure_empty, Measure.dirac_apply' _ ht,
      indicator_of_notMem hot, mul_zero]

lemma Pufferfish.measurableSet_eval_eq [MeasurableSingletonClass R] (i : H) (a : R) :
    MeasurableSet {D : H → R | D i = a} :=
  (measurableSet_singleton a).preimage (measurable_pi_apply i)

section Pi

variable [Fintype H] [MeasurableSingletonClass R] {q : H → Measure R}
  [∀ i, IsProbabilityMeasure (q i)]

lemma Pufferfish.pi_eval_eq (q : H → Measure R) [∀ i, IsProbabilityMeasure (q i)] (i : H)
    (a : R) : Measure.pi q {D | D i = a} = q i {a} :=
  (measurePreserving_eval q i).measure_preimage (measurableSet_singleton a).nullMeasurableSet

omit [MeasurableSingletonClass R] in
/-- A product of point masses is the point mass at the tuple. -/
lemma Pufferfish.pi_dirac (x : H → R) : Measure.pi (fun i ↦ Measure.dirac (x i)) =
    Measure.dirac x := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  by_cases hx : x ∈ Set.pi univ s
  · rw [indicator_of_mem hx, Finset.prod_eq_one fun i _ ↦ indicator_of_mem (hx i (mem_univ i)) _]
    rfl
  · obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_univ_pi] using hx
    rw [indicator_of_notMem hx, Finset.prod_eq_zero (Finset.mem_univ i)
      (indicator_of_notMem hi _)]

/-- Conditioning an independent prior on the value `a` of the slot of individual `i` replaces the
law of that slot by the point mass at `a` and leaves the other slots unchanged. -/
lemma Pufferfish.cond_pi_eval_eq [DecidableEq H] (i : H) {a : R} (ha : q i {a} ≠ 0) :
    (Measure.pi q)[|{D | D i = a}] = Measure.pi (Function.update q i (Measure.dirac a)) := by
  have : ∀ j, IsProbabilityMeasure (Function.update q i (Measure.dirac a) j) := fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]; infer_instance
    · rw [Function.update_of_ne hj]; infer_instance
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have hset : {D : H → R | D i = a} ∩ Set.pi univ s =
      Set.pi univ (Function.update s i ({a} ∩ s i)) := by
    ext D
    simp only [mem_inter_iff, Set.mem_univ_pi]
    rw [Function.forall_update_iff s (fun j (A : Set R) ↦ D j ∈ A)]
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨⟨rfl, h _⟩, fun j _ ↦ h j⟩
    · rintro ⟨⟨h₁, h₂⟩, h⟩
      refine ⟨h₁, fun j ↦ ?_⟩
      rcases eq_or_ne j i with rfl | hj
      · exact h₂
      · exact h j hj
  rw [cond_apply (Pufferfish.measurableSet_eval_eq i a), hset, Measure.pi_pi,
    Pufferfish.pi_eval_eq]
  have e₁ : (fun j ↦ q j (Function.update s i ({a} ∩ s i) j)) =
      Function.update (fun j ↦ q j (s j)) i (q i ({a} ∩ s i)) := by
    funext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  have e₂ : (fun j ↦ Function.update q i (Measure.dirac a) j (s j)) =
      Function.update (fun j ↦ q j (s j)) i (Measure.dirac a (s i)) := by
    funext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  rw [e₁, e₂, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (Finset.mem_univ i), ← mul_assoc]
  congr 1
  by_cases has : a ∈ s i
  · rw [inter_eq_left.2 (singleton_subset_iff.2 has), ENNReal.inv_mul_cancel ha
      (measure_ne_top _ _), Measure.dirac_apply_of_mem has]
  · rw [singleton_inter_eq_empty.2 has, measure_empty, mul_zero, Measure.dirac_apply' _ (hs i),
      indicator_of_notMem has]

omit [MeasurableSingletonClass R] in
/-- The point mass at `a` in slot `i` of an independent prior is the law of `update D i a` for
`D` drawn from the prior. -/
lemma Pufferfish.pi_update_dirac [DecidableEq H] (i : H) (a : R) :
    Measure.pi (Function.update q i (Measure.dirac a)) =
      (Measure.pi q).map (Function.update · i a) := by
  set f : ∀ j : H, R → R := Function.update (fun _ ↦ id) i (fun _ ↦ a)
  have hf : (fun (D : H → R) j ↦ f j (D j)) = (Function.update · i a) := by
    funext D j
    rcases eq_or_ne j i with rfl | hj <;> simp [f, *]
  have hfm (j : H) : AEMeasurable (f j) (q j) := by
    rcases eq_or_ne j i with rfl | hj
    · simp only [f, Function.update_self]
      exact measurable_const.aemeasurable
    · simp only [f, Function.update_of_ne hj]
      exact measurable_id.aemeasurable
  rw [← hf, Measure.pi_map_pi hfm]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp [f, Measure.map_const]
  · simp [f, hj]

end Pi

/-- **Theorem 6.1 of Kifer–Machanavajjhala** (differential privacy is Pufferfish for independent
records). With the potential secrets and discriminative pairs of equations (6)–(7) and the data
evolution scenarios `D*` of equation (8) (records of different individuals are independent), a
mechanism satisfies `ε-PufferFish(S, Spairs, D*)` if and only if it is `ε`-differentially private
for databases that differ in the presence of one tuple (Definition 6.1). The record space `R`
is an arbitrary measurable space with measurable singletons, the output space is arbitrary and
`ε` is any real number (the paper assumes `ε > 0`). -/
theorem isPufferfish_indepPriors_iff_isEpsDP [Fintype H] [MeasurableSingletonClass R] (o : R)
    {M : Kernel (H → R) Y} [IsFiniteKernel M] :
    IsPufferfish M (Pufferfish.dpPairs o) (Pufferfish.indepPriors H R) ε ↔
      IsEpsDP M (Pufferfish.AddRemoveAdj o) ε := by
  classical
  rw [isEpsDP_iff_le_smul]
  set c := ENNReal.ofReal (exp ε)
  constructor
  · -- Case 1 of the proof (Appendix C): a prior with two possible databases.
    intro h
    have key (D : H → R) (i : H) (hi : D i ≠ o) :
        M D ≤ c • M (Function.update D i o) ∧ M (Function.update D i o) ≤ c • M D := by
      set q : H → Measure R := Function.update (fun j ↦ Measure.dirac (D j)) i
        ((2⁻¹ : ℝ≥0∞) • (Measure.dirac (D i) + Measure.dirac o))
      have hq (j : H) : IsProbabilityMeasure (q j) := by
        rcases eq_or_ne j i with rfl | hj
        · simp only [q, Function.update_self]
          constructor
          simp [ENNReal.inv_two_add_inv_two]
        · simp only [q, Function.update_of_ne hj]
          infer_instance
      have hqt : q i {D i} ≠ 0 := by simp [q]
      have hqo : q i {o} ≠ 0 := by simp [q]
      have hs : Measure.pi q {D' | D' i = D i} ≠ 0 := by rwa [Pufferfish.pi_eval_eq]
      have hs' : Measure.pi q {D' | D' i = o} ≠ 0 := by rwa [Pufferfish.pi_eval_eq]
      have e₁ : M ∘ₘ (Measure.pi q)[|{D' | D' i = D i}] = M D := by
        rw [Pufferfish.cond_pi_eval_eq i hqt, Function.update_idem,
          Function.update_eq_self_iff.2 rfl, Pufferfish.pi_dirac, Measure.dirac_bind M.measurable]
      have hupd : Function.update (fun j ↦ Measure.dirac (D j)) i (Measure.dirac o) =
          fun j ↦ Measure.dirac (Function.update D i o j) :=
        funext fun j ↦ (Function.apply_update (fun _ ↦ Measure.dirac) D i o j).symm
      have e₂ : M ∘ₘ (Measure.pi q)[|{D' | D' i = o}] = M (Function.update D i o) := by
        rw [Pufferfish.cond_pi_eval_eq i hqo, Function.update_idem, hupd, Pufferfish.pi_dirac,
          Measure.dirac_bind M.measurable]
      have h₀ := h ⟨i, D i, hi, rfl⟩ _ ⟨q, hq, rfl⟩ hs hs'
      rwa [e₁, e₂] at h₀
    rintro D D' ⟨i, hne, ho, heq⟩
    rcases ho with ho | ho
    · have hD : D = Function.update D' i o := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [ho]
        · simp [hj, heq j hj]
      rw [hD]
      exact (key D' i fun h ↦ hne (ho.trans h.symm)).2
    · have hD' : D' = Function.update D i o := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [ho]
        · simp [hj, heq j hj]
      rw [hD']
      exact (key D i fun h ↦ hne (h.trans ho.symm)).1
  · -- Case 2 of the proof (Appendix C): couple `σ_(i,t)` and `¬σᵢ` through `update D i ·`.
    rintro h s s' ⟨i, t, ht, hp⟩ θ ⟨q, hq, rfl⟩ hs hs'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    rw [Pufferfish.pi_eval_eq] at hs hs'
    have e (a : R) (ha : q i {a} ≠ 0) : M ∘ₘ (Measure.pi q)[|{D | D i = a}] =
        (M.comap (Function.update · i a) measurable_update_left) ∘ₘ Measure.pi q := by
      rw [Pufferfish.cond_pi_eval_eq i ha, Pufferfish.pi_update_dirac,
        ← Measure.deterministic_comp_eq_map measurable_update_left, Measure.comp_assoc,
        Kernel.comp_deterministic_eq_comap]
    rw [e t hs, e o hs']
    have hadj (D : H → R) :
        Pufferfish.AddRemoveAdj o (Function.update D i t) (Function.update D i o) :=
      ⟨i, by simp [ht], Or.inr (by simp), fun j hj ↦ by simp [hj]⟩
    have hadj' (D : H → R) :
        Pufferfish.AddRemoveAdj o (Function.update D i o) (Function.update D i t) :=
      ⟨i, by simp [Ne.symm ht], Or.inl (by simp), fun j hj ↦ by simp [hj]⟩
    exact ⟨Pufferfish.comp_le_smul_comp (fun D ↦ by simpa using h (hadj D)) _,
      Pufferfish.comp_le_smul_comp (fun D ↦ by simpa using h (hadj' D)) _⟩

/-! ### Lemma D.1 and Theorem 6.2 -/

/-- The direction of **Lemma D.1 of Kifer–Machanavajjhala** that the paper calls clear: under an
independent prior `θ ∈ D*`, the conditional law of the rest of the data given `σ_(i,a)` equals
that given `σ_(i,b)`; precisely, the law of `update Data i b` given `Data i = a` is the law of
`Data` given `Data i = b`. With `a = t`, `b = o` this is
`P(Data = D ∪ {rᵢ = t} | σ_(i,t)) = P(Data = D | ¬σᵢ)`. -/
lemma Pufferfish.map_cond_eq_cond_of_mem_indepPriors [DecidableEq H] [Fintype H]
    [MeasurableSingletonClass R] {θ : Measure (H → R)} (hθ : θ ∈ Pufferfish.indepPriors H R)
    (i : H) {a b : R} (ha : θ {D | D i = a} ≠ 0) (hb : θ {D | D i = b} ≠ 0) :
    (θ[|{D | D i = a}]).map (Function.update · i b) = θ[|{D | D i = b}] := by
  obtain ⟨q, hq, rfl⟩ := hθ
  rw [Pufferfish.pi_eval_eq] at ha hb
  rw [Pufferfish.cond_pi_eval_eq i ha, Pufferfish.cond_pi_eval_eq i hb,
    Pufferfish.pi_update_dirac, Pufferfish.pi_update_dirac,
    Measure.map_map measurable_update_left measurable_update_left]
  congr 1
  funext D
  simp

/-- The property of Lemma D.1 of Kifer–Machanavajjhala: for every individual `i` and tuple
value `t ≠ o` for which both conditional distributions are defined, the law of the rest of the
data is the same given `σ_(i,t)` and given `¬σᵢ`, i.e.
`P(Data = D ∪ {rᵢ = t} | σ_(i,t), θ) = P(Data = D | ¬σᵢ, θ)` for every `D` without a record of
`hᵢ`; formally, the law of `update Data i o` given `Data i = t` is the law of `Data` given
`Data i = o`. -/
def Pufferfish.CondRestInvariant [DecidableEq H] (o : R) (θ : Measure (H → R)) : Prop :=
  ∀ i t, t ≠ o → θ {D | D i = t} ≠ 0 → θ {D | D i = o} ≠ 0 →
    (θ[|{D | D i = t}]).map (Function.update · i o) = θ[|{D | D i = o}]

/-- Every independent prior has the property of Lemma D.1. -/
lemma Pufferfish.condRestInvariant_of_mem_indepPriors [DecidableEq H] [Fintype H]
    [MeasurableSingletonClass R] {o : R} {θ : Measure (H → R)}
    (hθ : θ ∈ Pufferfish.indepPriors H R) : Pufferfish.CondRestInvariant o θ :=
  fun i _ _ ht ho ↦ Pufferfish.map_cond_eq_cond_of_mem_indepPriors hθ i ht ho

/-- Step 1 of the proof of Lemma D.1: under the property of Lemma D.1, removing the record of
`hᵢ` from `D` multiplies its probability by `P(¬σᵢ) / P(σ_(i,D i))`. -/
private lemma Pufferfish.measure_singleton_mul_eq [DecidableEq H] [Finite H]
    [MeasurableSingletonClass R] {o : R} {θ : Measure (H → R)} [IsFiniteMeasure θ]
    (h : Pufferfish.CondRestInvariant o θ) (hθo : ∀ j, θ {D | D j = o} ≠ 0) (D : H → R) (i : H)
    (hi : D i ≠ o) :
    θ {D} * θ {E | E i = o} = θ {Function.update D i o} * θ {E | E i = D i} := by
  by_cases ht : θ {E | E i = D i} = 0
  · have : θ {D} = 0 := measure_mono_null (singleton_subset_iff.2 (show D i = D i from rfl)) ht
    simp [this, ht]
  have e := congrArg (fun μ : Measure (H → R) ↦ μ {Function.update D i o})
    (h i (D i) hi ht (hθo i))
  rw [Measure.map_apply measurable_update_left (measurableSet_singleton _),
    cond_apply (Pufferfish.measurableSet_eval_eq i _),
    cond_apply (Pufferfish.measurableSet_eval_eq i _)] at e
  have s₁ : {E : H → R | E i = D i} ∩ (Function.update · i o) ⁻¹' {Function.update D i o} =
      {D} := by
    ext E
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ funext fun j ↦ ?_, fun h' ↦ ⟨h' ▸ rfl, h' ▸ rfl⟩⟩
    rcases eq_or_ne j i with rfl | hj
    · exact h₁
    · simpa [hj] using congrFun h₂ j
  have s₂ : {E : H → R | E i = o} ∩ {Function.update D i o} = {Function.update D i o} :=
    inter_eq_right.2 (singleton_subset_iff.2 (by simp))
  rw [s₁, s₂] at e
  calc θ {D} * θ {E | E i = o}
      = θ {E | E i = D i} * ((θ {E | E i = D i})⁻¹ * θ {D}) * θ {E | E i = o} := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel ht (measure_ne_top _ _), one_mul]
    _ = θ {E | E i = D i} * ((θ {E | E i = o})⁻¹ * θ {Function.update D i o}) *
        θ {E | E i = o} := by rw [e]
    _ = θ {Function.update D i o} * θ {E | E i = D i} *
        ((θ {E | E i = o})⁻¹ * θ {E | E i = o}) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel (hθo i) (measure_ne_top _ _), mul_one]

/-- Step 2 of the proof of Lemma D.1, cross-multiplied: removing the records one by one,
`θ{D} · ∏ⱼ P(¬σⱼ) = θ{∅} · ∏ⱼ P(rⱼ = D j)`, where `∅` is the database without records. -/
private lemma Pufferfish.measure_singleton_mul_prod_eq [DecidableEq H] [Fintype H]
    [MeasurableSingletonClass R] {o : R} {θ : Measure (H → R)} [IsFiniteMeasure θ]
    (h : Pufferfish.CondRestInvariant o θ) (hθo : ∀ j, θ {D | D j = o} ≠ 0) (D : H → R) :
    θ {D} * ∏ j, θ {E | E j = o} = θ {fun _ ↦ o} * ∏ j, θ {E | E j = D j} := by
  suffices ∀ S : Finset H, ∀ D : H → R, (∀ j ∉ S, D j = o) →
      θ {D} * ∏ j, θ {E | E j = o} = θ {fun _ ↦ o} * ∏ j, θ {E | E j = D j} from
    this Finset.univ D (by simp)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro D hD
    obtain rfl : D = fun _ ↦ o := funext fun j ↦ hD j (Finset.notMem_empty j)
    rfl
  | insert i S hiS ih =>
    intro D hD
    set D' := Function.update D i o
    have hD' (j : H) (hj : j ∉ S) : D' j = o := by
      rcases eq_or_ne j i with rfl | hji
      · simp [D']
      · simp [D', hji, hD j (by simp [hji, hj])]
    have ih' := ih D' hD'
    by_cases hDi : D i = o
    · rwa [show D' = D from Function.update_eq_self_iff.2 hDi.symm] at ih'
    have key := Pufferfish.measure_singleton_mul_eq h hθo D i hDi
    have hp₁ : ∏ j, θ {E | E j = D j} =
        θ {E | E i = D i} * ∏ j ∈ Finset.univ.erase i, θ {E | E j = D j} :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have hp₂ : ∏ j, θ {E | E j = D' j} =
        θ {E | E i = o} * ∏ j ∈ Finset.univ.erase i, θ {E | E j = D j} := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      congr 1
      · simp [D']
      · exact Finset.prod_congr rfl fun j hj ↦ by simp [D', Finset.ne_of_mem_erase hj]
    rw [hp₂] at ih'
    rw [hp₁, ← ENNReal.mul_right_inj (hθo i) (measure_ne_top θ {E | E i = o})]
    calc θ {E | E i = o} * (θ {D} * ∏ j, θ {E | E j = o})
        = θ {E | E i = D i} * (θ {D'} * ∏ j, θ {E | E j = o}) := by
          rw [← mul_assoc, mul_comm (θ {E | E i = o}), key]
          ring
      _ = _ := by rw [ih']; ring

/-- **Lemma D.1 of Kifer–Machanavajjhala, converse direction, non-degenerate case.** If every
individual is absent with positive probability (`P(¬σⱼ | θ) ≠ 0` for all `j`, the assumption of
Step 2 of the paper's proof) and `θ` has the property of Lemma D.1, then `θ` is an independent
prior: `θ = ⨂ⱼ θ ∘ evalⱼ⁻¹`. Records take values in a countable space. Without the positivity
assumption the statement is false (`Pufferfish.correlatedPrior_condRestInvariant`). -/
theorem Pufferfish.mem_indepPriors_of_condRestInvariant [DecidableEq H] [Fintype H]
    [Countable R] [MeasurableSingletonClass R] {o : R} {θ : Measure (H → R)}
    [IsProbabilityMeasure θ] (hθo : ∀ j, θ {D | D j = o} ≠ 0)
    (h : Pufferfish.CondRestInvariant o θ) : θ ∈ Pufferfish.indepPriors H R := by
  set q : H → Measure R := fun j ↦ θ.map (Function.eval j)
  have hq (j : H) : IsProbabilityMeasure (q j) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply j).aemeasurable).2 inferInstance
  have hqa (j : H) (a : R) : q j {a} = θ {D | D j = a} :=
    Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton a)
  refine ⟨q, hq, ?_⟩
  set K := ∏ j, θ {D | D j = o}
  have hK₀ : K ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hθo j
  have hK : K ≠ ∞ := ENNReal.prod_ne_top fun j _ ↦ measure_ne_top _ _
  have hpi (D : H → R) : Measure.pi q {D} = ∏ j, θ {E | E j = D j} := by
    rw [Measure.pi_singleton]
    exact Finset.prod_congr rfl fun j _ ↦ hqa j (D j)
  have hrel (D : H → R) : θ {D} * K = θ {fun _ ↦ o} * Measure.pi q {D} := by
    rw [hpi]
    exact Pufferfish.measure_singleton_mul_prod_eq h hθo D
  have htsum (μ : Measure (H → R)) [IsProbabilityMeasure μ] : ∑' D, μ {D} = 1 := by
    simpa using μ.tsum_indicator_apply_singleton univ .univ
  have h₀ : θ {fun _ ↦ o} = K := by
    have := congrArg tsum (funext hrel)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, htsum, htsum] at this
    simpa using this.symm
  refine Measure.ext_iff_singleton.2 fun D ↦ ?_
  rw [← ENNReal.mul_left_inj hK₀ hK, hrel, h₀, mul_comm]

/-- The prior used to show that Theorem 6.2 fails as stated: two individuals, records in
`Fin 3` with `0` meaning "absent", both records always present and perfectly correlated
(`D = (1, 1)` or `D = (2, 2)`, each with probability `1/2`). -/
noncomputable def Pufferfish.correlatedPrior : Measure (Fin 2 → Fin 3) :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac ![1, 1] + Measure.dirac ![2, 2])

/-- `Pufferfish.correlatedPrior` is not an independent prior: it is not of the form of
equation (8). -/
lemma Pufferfish.correlatedPrior_notMem_indepPriors :
    Pufferfish.correlatedPrior ∉ Pufferfish.indepPriors (Fin 2) (Fin 3) := by
  rintro ⟨q, hq, hθ⟩
  have h₁ : q 0 {1} = 2⁻¹ := by
    rw [← Pufferfish.pi_eval_eq q 0 1, ← hθ]
    simp [Pufferfish.correlatedPrior, Measure.dirac_apply, Set.indicator_apply]
  have h₂ : q 1 {2} = 2⁻¹ := by
    rw [← Pufferfish.pi_eval_eq q 1 2, ← hθ]
    simp [Pufferfish.correlatedPrior, Measure.dirac_apply]
  have h₃ : Measure.pi q {![1, 2]} = 0 := by
    rw [← hθ]
    simp [Pufferfish.correlatedPrior]
  rw [Measure.pi_singleton, Fin.prod_univ_two] at h₃
  simp [h₁, h₂] at h₃

/-- **The converse of Lemma D.1 fails in the degenerate case.** `Pufferfish.correlatedPrior` has
the property of Lemma D.1 (vacuously: every individual is present with probability one, so
`P(¬σᵢ) = 0` and no conditional given `¬σᵢ` is defined) but it is not an independent prior
(`Pufferfish.correlatedPrior_notMem_indepPriors`). It does fail the generalized property
`P(Data = D ∪ {rᵢ = b} | σ_(i,b)) = P(Data = D ∪ {rᵢ = a} | σ_(i,a))` at `i = 0`, `a = 1`, `b = 2`;
Lemma D.1 only involves the pairs `(t, o)`. -/
lemma Pufferfish.correlatedPrior_condRestInvariant :
    Pufferfish.CondRestInvariant 0 Pufferfish.correlatedPrior := by
  intro i t _ _ ho
  refine absurd ?_ ho
  fin_cases i <;> simp [Pufferfish.correlatedPrior, Measure.dirac_apply]

/-- **Theorem 6.2 of Kifer–Machanavajjhala is false as stated.** The theorem claims that for any
set of evolution scenarios `D_other ⊄ D*`, `ε`-differential privacy is not equivalent to
`ε-PufferFish(S, Spairs, D_other)` (with `S`, `Spairs` of equations (6)–(7)). But adding to `D*`
the prior `Pufferfish.correlatedPrior`, under which every individual is present with
probability one, gives `D_other ⊄ D*` imposing exactly the same constraints as `D*` (the
conditions of Definition 3.4 are vacuous for a prior with `P(¬σᵢ) = 0`), so by Theorem 6.1
`ε-PufferFish(S, Spairs, D_other)` is still equivalent to `ε`-differential privacy. -/
theorem Pufferfish.exists_not_subset_indepPriors_isPufferfish_iff :
    ∃ Θ : Set (Measure (Fin 2 → Fin 3)), ¬ Θ ⊆ Pufferfish.indepPriors (Fin 2) (Fin 3) ∧
      ∀ (M : Kernel (Fin 2 → Fin 3) Y) [IsFiniteKernel M] (ε : ℝ),
        IsPufferfish M (Pufferfish.dpPairs 0) Θ ε ↔ IsEpsDP M (Pufferfish.AddRemoveAdj 0) ε := by
  refine ⟨insert Pufferfish.correlatedPrior (Pufferfish.indepPriors _ _),
    fun h ↦ Pufferfish.correlatedPrior_notMem_indepPriors (h (mem_insert _ _)),
    fun M _ ε ↦ ?_⟩
  rw [isPufferfish_insert_iff, isPufferfish_indepPriors_iff_isEpsDP]
  rintro s s' ⟨i, t, -, hp⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  right
  fin_cases i <;> simp [Pufferfish.correlatedPrior, Measure.dirac_apply]

/-- The output probabilities `φ(p, a) = x^{[p] + [a]} / (x (1 + x))` of the mechanism in the
proof of Theorem 6.2 are within a factor `x ≥ 1` of each other, together with their complements,
as soon as one of the two arguments agrees. -/
private lemma Pufferfish.thm62_ineq {x : ℝ} (hx : 1 < x) (p p' a a' : Bool) (h : p = p' ∨ a = a') :
    (if p then x else 1) * (if a then x else 1) / (x * (1 + x)) ≤
      x * ((if p' then x else 1) * (if a' then x else 1) / (x * (1 + x))) ∧
    1 - (if p then x else 1) * (if a then x else 1) / (x * (1 + x)) ≤
      x * (1 - (if p' then x else 1) * (if a' then x else 1) / (x * (1 + x))) := by
  have hx0 : 0 < x := by linarith
  cases p <;> cases p' <;> cases a <;> cases a' <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, or_self, or_false, false_or] at h <;>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one] <;>
    constructor <;> rw [← sub_nonneg] <;> field_simp <;>
    nlinarith [mul_pos hx0 hx0, mul_pos (mul_pos hx0 hx0) hx0,
      mul_nonneg (sq_nonneg (x - 1)) hx0.le, sq_nonneg (x - 1)]

/-- **The argument of Appendix D of Kifer–Machanavajjhala** (proof of Theorem 6.2, after
Lemma D.1). Suppose some attacker `θ ∈ D_other` violates the property of Lemma D.1 at an
individual `i` and a tuple value `t` for which both conditional distributions are defined
(`P(σ_(i,t) | θ) ≠ 0`, `P(¬σᵢ | θ) ≠ 0`): the law of the rest of the data given `σ_(i,t)` differs
from its law given `¬σᵢ`, i.e. `P(Data = D ∪ {rᵢ = t} | σ_(i,t), θ) ≠ P(Data = D | ¬σᵢ, θ)` for
some `D`. Then for every `ε > 0` the mechanism of Appendix D (outputs in `Bool`) is
`ε`-differentially private but does not satisfy `ε-PufferFish(S, Spairs, D_other)` (equations
(6)–(7)). The record space is countable. Combined with the converse of Lemma D.1 this gives the
corrected Theorem 6.2, `Pufferfish.exists_isEpsDP_not_isPufferfish_of_notMem`. -/
theorem Pufferfish.exists_isEpsDP_not_isPufferfish [DecidableEq H] [Finite H] [Countable R]
    [MeasurableSingletonClass R] (o : R) (hε : 0 < ε) {Θ : Set (Measure (H → R))}
    {θ : Measure (H → R)} (hθ : θ ∈ Θ) [IsProbabilityMeasure θ] {i : H} {t : R} (ht : t ≠ o)
    (hθt : θ {D | D i = t} ≠ 0) (hθo : θ {D | D i = o} ≠ 0)
    (hne : (θ[|{D | D i = t}]).map (Function.update · i o) ≠ θ[|{D | D i = o}]) :
    ∃ M : Kernel (H → R) Bool, IsMarkovKernel M ∧ IsEpsDP M (Pufferfish.AddRemoveAdj o) ε ∧
      ¬ IsPufferfish M (Pufferfish.dpPairs o) Θ ε := by
  classical
  set ρ : (H → R) → (H → R) := (Function.update · i o)
  have hρm : Measurable ρ := measurable_update_left
  set P₁ := θ[|{D | D i = o}]
  set Q := θ[|{D | D i = t}]
  have : IsProbabilityMeasure P₁ := cond_isProbabilityMeasure hθo
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure hθt
  have : IsProbabilityMeasure (Q.map ρ) :=
    (Measure.isProbabilityMeasure_map_iff hρm.aemeasurable).2 inferInstance
  -- A set `A` of record-free databases, more likely given `¬σᵢ` than its translate given `σ_(i,t)`.
  obtain ⟨A, hA⟩ : ∃ A, Q.map ρ A < P₁ A := by
    by_contra! hle
    exact hne (Measure.eq_of_le_of_isProbabilityMeasure (Measure.le_iff.2 fun A _ ↦ hle A)).symm
  have hAm : MeasurableSet A := .of_discrete
  set x := exp ε
  have hx : 1 < x := Real.one_lt_exp_iff.2 hε
  have hx0 : 0 < x := exp_pos ε
  set φ : Bool → Bool → ℝ := fun p a ↦
    (if p then x else 1) * (if a then x else 1) / (x * (1 + x))
  have hφ0 (p a : Bool) : 0 ≤ φ p a := by
    simp only [φ]
    cases p <;> cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  have hφ1 (p a : Bool) : φ p a ≤ 1 := by
    simp only [φ]
    rw [div_le_one (by positivity)]
    cases p <;> cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith
  -- The mechanism of Appendix D: `P(M(D) = true) = g D`.
  set g : (H → R) → ℝ := fun D ↦ φ (decide (D i = o)) (decide (ρ D ∈ A))
  set M : Kernel (H → R) Bool := Kernel.ofFunOfCountable fun D ↦
    ENNReal.ofReal (g D) • Measure.dirac true + ENNReal.ofReal (1 - g D) • Measure.dirac false
  have hM (D : H → R) (b : Bool) :
      M D {b} = ENNReal.ofReal (if b then g D else 1 - g D) := by
    cases b <;> simp [M, Kernel.ofFunOfCountable]
  have hMk : IsMarkovKernel M := ⟨fun D ↦ ⟨by
    simp only [M, Kernel.ofFunOfCountable, Kernel.coe_mk, add_apply, smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (hφ0 _ _) (sub_nonneg.2 (hφ1 _ _))]
    simp⟩⟩
  refine ⟨M, hMk, ?_, fun h ↦ ?_⟩
  · -- Step 1: `M` is `ε`-differentially private.
    rw [isEpsDP_iff_le_smul]
    rintro D D' ⟨j, -, -, heq⟩
    rw [Pufferfish.le_smul_iff_forall_singleton]
    have hc : decide (D i = o) = decide (D' i = o) ∨
        decide (ρ D ∈ A) = decide (ρ D' ∈ A) := by
      by_cases hji : i = j
      · right
        have : ρ D = ρ D' := by
          funext k
          rcases eq_or_ne k i with rfl | hk
          · simp [ρ]
          · simp [ρ, hk, heq k (hji ▸ hk)]
        rw [this]
      · left
        rw [heq i hji]
    intro b
    rw [hM, hM, ← ENNReal.ofReal_mul hx0.le]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨h₁, h₂⟩ := Pufferfish.thm62_ineq hx _ _ _ _ hc
    cases b
    · exact h₂
    · exact h₁
  · -- Step 2: `M` violates the Pufferfish constraint for `(σ_(i,t), ¬σᵢ)` under `θ`.
    have h₀ := (Pufferfish.le_smul_iff_forall_singleton.1
      (h ⟨i, t, ht, rfl⟩ θ hθ hθt hθo).2) true
    have eval (μ : Measure (H → R)) : (M ∘ₘ μ) {true} = ∫⁻ D, ENNReal.ofReal (g D) ∂μ := by
      rw [Measure.bind_apply (measurableSet_singleton _) M.aemeasurable]
      simp [hM]
    set F : Bool → (H → R) → ℝ≥0∞ := fun p D ↦ A.indicator (fun _ ↦ ENNReal.ofReal (φ p true)) D +
      Aᶜ.indicator (fun _ ↦ ENNReal.ofReal (φ p false)) D
    have hF (p : Bool) (D : H → R) : ENNReal.ofReal (φ p (decide (D ∈ A))) = F p D := by
      by_cases hD : D ∈ A <;> simp [F, hD]
    have intF (p : Bool) (P : Measure (H → R)) : ∫⁻ D, F p D ∂P =
        ENNReal.ofReal (φ p true) * P A + ENNReal.ofReal (φ p false) * P Aᶜ := by
      simp only [F]
      rw [lintegral_add_left (measurable_const.indicator hAm), lintegral_indicator_const hAm,
        lintegral_indicator_const hAm.compl]
    have e₁ : (M ∘ₘ P₁) {true} =
        ENNReal.ofReal (φ true true) * P₁ A + ENNReal.ofReal (φ true false) * P₁ Aᶜ := by
      rw [eval, ← intF]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_cond_mem (Pufferfish.measurableSet_eval_eq i o)] with D hD
      have hρD : ρ D = D := Function.update_eq_self_iff.2 hD.symm
      simp only [g, hρD, ← hF]
      simp [show D i = o from hD]
    have e₂ : (M ∘ₘ Q) {true} = ENNReal.ofReal (φ false true) * Q.map ρ A +
        ENNReal.ofReal (φ false false) * Q.map ρ Aᶜ := by
      rw [eval, ← intF, lintegral_map (measurable_of_countable _) hρm]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_cond_mem (Pufferfish.measurableSet_eval_eq i t)] with D hD
      have hDo : ¬ D i = o := fun h' ↦ ht ((show D i = t from hD).symm.trans h')
      simp only [g, ← hF, hDo, decide_false]
    rw [e₁, e₂] at h₀
    have conv (μ : Measure (H → R)) [IsProbabilityMeasure μ] (u v : ℝ) (hu : 0 ≤ u)
        (hv : 0 ≤ v) : (ENNReal.ofReal u * μ A + ENNReal.ofReal v * μ Aᶜ).toReal =
          u * μ.real A + v * (1 - μ.real A) := by
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hu, ENNReal.toReal_ofReal hv, ← measureReal_def,
        ← measureReal_def, probReal_compl_eq_one_sub hAm]
    have r := ENNReal.toReal_mono (by finiteness) h₀
    rw [conv P₁ _ _ (hφ0 _ _) (hφ0 _ _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0.le,
      conv (Q.map ρ) _ _ (hφ0 _ _) (hφ0 _ _)] at r
    have hr : (Q.map ρ).real A < P₁.real A :=
      (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hA
    have key₁ : φ true true = x * φ false true := by
      simp only [φ, ↓reduceIte, Bool.false_eq_true]
      ring
    have key₀ : φ true false = x * φ false false := by
      simp only [φ, ↓reduceIte, Bool.false_eq_true]
      ring
    have hlt : φ false false < φ false true := by
      simp only [φ, ↓reduceIte, Bool.false_eq_true, one_mul]
      exact div_lt_div_of_pos_right hx (by positivity)
    rw [key₁, key₀] at r
    nlinarith [mul_pos (mul_pos hx0 (sub_pos.2 hlt)) (sub_pos.2 hr)]

/-- **Theorem 6.2 of Kifer–Machanavajjhala, corrected.** If the evolution scenarios `D_other`
contain a prior `θ ∉ D*` under which every individual is absent with positive probability
(`P(¬σⱼ | θ) ≠ 0` for all `j`), then for every `ε > 0` some `ε`-differentially private mechanism
does not satisfy `ε-PufferFish(S, Spairs, D_other)` (equations (6)–(7)); in particular the two
definitions are not equivalent. Records take values in a countable space. The positivity
assumption cannot be dropped (`Pufferfish.exists_not_subset_indepPriors_isPufferfish_iff`). -/
theorem Pufferfish.exists_isEpsDP_not_isPufferfish_of_notMem [Fintype H]
    [Countable R] [MeasurableSingletonClass R] (o : R) (hε : 0 < ε)
    {Θ : Set (Measure (H → R))} {θ : Measure (H → R)} (hθ : θ ∈ Θ) [IsProbabilityMeasure θ]
    (hθD : θ ∉ Pufferfish.indepPriors H R) (hθo : ∀ j, θ {D | D j = o} ≠ 0) :
    ∃ M : Kernel (H → R) Bool, IsMarkovKernel M ∧ IsEpsDP M (Pufferfish.AddRemoveAdj o) ε ∧
      ¬ IsPufferfish M (Pufferfish.dpPairs o) Θ ε := by
  classical
  have hD1 : ¬ Pufferfish.CondRestInvariant o θ :=
    fun h ↦ hθD (Pufferfish.mem_indepPriors_of_condRestInvariant hθo h)
  simp only [Pufferfish.CondRestInvariant, not_forall] at hD1
  obtain ⟨i, t, ht, hθt, hθo', hne⟩ := hD1
  exact Pufferfish.exists_isEpsDP_not_isPufferfish o hε hθ ht hθt hθo' hne

end Database

end InformationTheory
