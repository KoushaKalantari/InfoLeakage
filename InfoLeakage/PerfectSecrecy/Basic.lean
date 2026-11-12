/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.MaximalLeakage.MutualInfo
public import InfoLeakage.MaximalLeakage.Properties
public import Mathlib.Probability.ConditionalProbability

/-!
# Perfect secrecy

This file formalizes the definition of perfect secrecy and its characterization, Theorem 6, from
§10 of C. E. Shannon, *Communication Theory of Secrecy Systems*, Bell System Technical Journal
28(4), 656–715, 1949 (not on arXiv).

Shannon's setting (§2 and §10): there are finitely many messages `M`, keys `K` and cryptograms
`E`. A secrecy system is a family of enciphering transformations `T k : M → E` indexed by the
keys, the key being drawn from a key law `ν` independently of the message, which has an
a priori law `μ`. Writing `P_M(E)` for the probability of the cryptogram `E` given the message
`M` ("the sum of the probabilities of all keys which produce cryptogram `E` from message `M`"),
`P(E)` for the probability of `E` and `P_E(M)` for the a posteriori probability of `M` after `E`
is intercepted, Shannon defines perfect secrecy by `P_E(M) = P(M)` for all `E` and `M`,
"independently of the values" of the a priori probabilities.

Shannon's transformations are moreover uniquely reversible (injective). None of the results of
this file needs that, so it is not assumed here; it is assumed in
`InfoLeakage.PerfectSecrecy.Keys`, where it is needed.

## Main definitions

* `cipherKernel T ν`: the channel `m ↦ law of T k m` with `k ∼ ν`, so that
  `cipherKernel T ν m {e}` is Shannon's `P_M(E)`.
* `IsPerfectlySecret μ T ν`: perfect secrecy for the a priori law `μ`: for every cryptogram `e`
  of positive probability, `P_E(M) = P(M)` for every message.
* `IsPerfectSystem T ν`: Shannon's notion, perfect secrecy for every a priori law of the messages.

## Main statements

* `map_prod_eq_compProd`: if the key is drawn independently of the message, the joint law of
  message and cryptogram is `μ ⊗ₘ cipherKernel T ν`.
* `cond_eq_mul_div`: Bayes' theorem in Shannon's form `P_E(M) = P(M) P_M(E) / P(E)`.
* `isPerfectSystem_iff_forall_cipherKernel_eq_comp`: **Theorem 6** as stated (perfect secrecy
  independently of the a priori law): `P_M(E) = P(E)` for all `M`, `E` and every a priori law.
* `isPerfectlySecret_iff`: refinement to a fixed a priori law `μ`, following Shannon's derivation:
  perfect secrecy for `μ` iff `P_M(E) = P(E)` for every message of positive probability.
* `isPerfectlySecret_iff_of_forall_ne_zero`: the same for an a priori law charging every message:
  perfect secrecy for `μ` iff `P_M(E) = P(E)` for all `M` and `E`.
* `isPerfectlySecret_iff_cipherKernel_eq`: perfect secrecy for `μ` iff all messages of positive
  a priori probability have the same row `P_M`.
* `isPerfectSystem_iff`, `isPerfectSystem_iff_forall_measure_setOf_eq`: **Theorem 6**, the
  paper's two restatements: `P_M(E)` is independent of `M`, i.e. the total probability of the
  keys taking `Mᵢ` to `E` equals that of the keys taking `Mⱼ` to `E`.
* `isPerfectlySecret_iff_compProd_eq_prod`: perfect secrecy iff message and cryptogram are
  independent.
* `isPerfectlySecret_iff_maxLeakage_eq_zero`: perfect secrecy iff the maximal leakage from the
  message to the cryptogram is zero.
* `isPerfectlySecret_iff_mutualInfo_eq_zero`: perfect secrecy iff the mutual information between
  message and cryptogram is zero.
* `isPerfectSystem_iff_forall_maxLeakage_eq_zero`: a system is perfect iff its maximal leakage
  vanishes for every a priori law.

## Mapping from the paper

* §10, definition of perfect secrecy → `IsPerfectlySecret` (fixed a priori law) and
  `IsPerfectSystem` (all a priori laws, "independently of the values of these").
* §10, Bayes' theorem → `cond_eq_mul_div`.
* §10, Theorem 6 → `isPerfectSystem_iff_forall_cipherKernel_eq_comp` (as stated),
  `isPerfectSystem_iff` and `isPerfectSystem_iff_forall_measure_setOf_eq` (its restatements);
  `isPerfectlySecret_iff` and `isPerfectlySecret_iff_of_forall_ne_zero` refine it to a fixed
  a priori law, following Shannon's derivation.

## Implementation notes

Shannon's derivation of Theorem 6 divides by `P(M)` and excludes `P(M) = 0` "since we demand the
equality independent of the values of `P(M)`". For a fixed a priori law that vanishes on some
message `M`, perfect secrecy does not constrain `P_M(E)`, so the condition "for all `M`" of
Theorem 6 is only necessary under that exclusion; `isPerfectlySecret_iff` gives the exact
condition for a fixed a priori law, and `isPerfectlySecret_iff_of_forall_ne_zero` the condition
for a fixed a priori law charging every message.

The definitions require countable alphabets with measurable singletons and probability measures
for the key and a priori laws (`cipherKernel`, `IsPerfectlySecret`, `IsPerfectSystem`). Without
them the definitions can hold for degenerate reasons: for a zero key law, or a cryptogram
σ-algebra in which the events `{e}` are not measurable, every system would be "perfect".

The a posteriori probability `P_E(M)` is the elementary conditional probability
`(μ ⊗ₘ cipherKernel T ν)[Prod.fst ⁻¹' {m} | Prod.snd ⁻¹' {e}]`, defined only for cryptograms of
positive probability; `IsPerfectlySecret` quantifies over exactly those cryptograms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {M K E : Type*} [MeasurableSpace M] [MeasurableSpace K] [MeasurableSpace E]

section Auxiliary

/-! The lemmas of this section hold for any kernel and are not specific to secrecy systems. -/

variable [MeasurableSingletonClass M] [MeasurableSingletonClass E] {μ : Measure M}
  {κ : Kernel M E}

/-- The probability that the input of a kernel is `m` and its output is `e`. -/
lemma compProd_apply_singleton_prod [SFinite μ] [IsSFiniteKernel κ] (m : M) (e : E) :
    (μ ⊗ₘ κ) ({m} ×ˢ {e}) = μ {m} * κ m {e} := by
  rw [Measure.compProd_apply_prod (measurableSet_singleton m) (measurableSet_singleton e),
    lintegral_singleton, mul_comm]

/-- **Bayes' theorem**: the conditional probability that the input of the kernel `κ` is `m`
given that its output is `e` is `μ {m} * κ m {e} / (κ ∘ₘ μ) {e}`. -/
lemma cond_eq_mul_div [SFinite μ] [IsMarkovKernel κ] (m : M) (e : E) :
    (μ ⊗ₘ κ)[Prod.fst ⁻¹' {m} | Prod.snd ⁻¹' {e}] = μ {m} * κ m {e} / (κ ∘ₘ μ) {e} := by
  have h_inter : Prod.snd ⁻¹' {e} ∩ Prod.fst ⁻¹' {m} = ({m} ×ˢ {e} : Set (M × E)) := by
    ext ⟨m', e'⟩
    simp [and_comm]
  rw [cond_apply (measurable_snd (measurableSet_singleton e)), h_inter,
    compProd_apply_singleton_prod, ← Measure.snd_apply (measurableSet_singleton e),
    Measure.snd_compProd, div_eq_mul_inv, mul_comm]

omit [MeasurableSingletonClass M] in
/-- The output law of a kernel is the mixture of its rows: `(κ ∘ₘ μ) {e} = ∫⁻ m, κ m {e} ∂μ`. -/
lemma comp_apply_singleton_eq_lintegral (e : E) : (κ ∘ₘ μ) {e} = ∫⁻ m, κ m {e} ∂μ :=
  Measure.bind_apply (measurableSet_singleton e) κ.aemeasurable

omit [MeasurableSingletonClass M] in
/-- On a countable input alphabet, `κ m {e} = (κ ∘ₘ μ) {e}` for all atoms `m` of `μ` iff the
rows of `κ` on the atoms of `μ` coincide. -/
lemma forall_apply_eq_comp_apply_iff [Countable M] [Countable E] [IsProbabilityMeasure μ] :
    (∀ m, μ {m} ≠ 0 → ∀ e, κ m {e} = (κ ∘ₘ μ) {e}) ↔
      ∀ m m', μ {m} ≠ 0 → μ {m'} ≠ 0 → κ m = κ m' := by
  refine ⟨fun h m m' hm hm' ↦ Measure.ext_of_singleton fun e ↦ (h m hm e).trans (h m' hm' e).symm,
    fun h m hm e ↦ ?_⟩
  have h_ae : ∀ᵐ m' ∂μ, κ m' {e} = κ m {e} :=
    ae_iff_of_countable.2 fun m' hm' ↦ by rw [h m' m hm' hm]
  rw [comp_apply_singleton_eq_lintegral, lintegral_congr_ae h_ae, lintegral_const, measure_univ,
    mul_one]

end Auxiliary

section SecrecySystem

/-! ### Secrecy systems and perfect secrecy

All alphabets are countable with measurable singletons. These assumptions are part of the
definitions below, together with the requirement that the key law and the a priori law be
probability measures, so that the definitions cannot hold for degenerate reasons (e.g. a zero key
law, or a cryptogram σ-algebra in which the events `{e}` are not measurable). -/

variable [Countable M] [MeasurableSingletonClass M]

/-- The channel from messages to cryptograms of the secrecy system with enciphering
transformations `T k : M → E` and key law `ν`: `cipherKernel T ν m` is the law of `T k m` for a
key `k ∼ ν`. Its value `cipherKernel T ν m {e}` is Shannon's `P_M(E)`, the total probability of
the keys that encipher `m` into `e` (`cipherKernel_apply_singleton`).

The instances `[Countable K] [MeasurableSingletonClass K]` (every map out of `K` is measurable,
so the image law is not degenerate) and `[MeasurableSingletonClass E]` (the events `{e}` are
measurable) are not used in the body; they restrict the definition to the setting in which it
means `P_M(E)`. -/
@[nolint unusedArguments]
noncomputable def cipherKernel [Countable K] [MeasurableSingletonClass K]
    [MeasurableSingletonClass E] (T : K → M → E) (ν : Measure K) : Kernel M E :=
  Kernel.ofFunOfCountable fun m ↦ ν.map fun k ↦ T k m

variable [Countable K] [MeasurableSingletonClass K] [MeasurableSingletonClass E]
  {T : K → M → E} {ν : Measure K}

lemma cipherKernel_apply (T : K → M → E) (ν : Measure K) (m : M) {s : Set E}
    (hs : MeasurableSet s) :
    cipherKernel T ν m s = ν {k | T k m ∈ s} :=
  Measure.map_apply (measurable_of_countable _) hs

lemma cipherKernel_apply_singleton (T : K → M → E) (ν : Measure K) (m : M) (e : E) :
    cipherKernel T ν m {e} = ν {k | T k m = e} :=
  cipherKernel_apply T ν m (measurableSet_singleton e)

instance [IsProbabilityMeasure ν] : IsMarkovKernel (cipherKernel T ν) :=
  ⟨fun m ↦ (Measure.isProbabilityMeasure_map_iff (measurable_of_countable (T · m)).aemeasurable).2
    inferInstance⟩

/-- The key is drawn independently of the message: if `(m, k) ∼ μ × ν`, then the pair
`(m, T k m)` of message and cryptogram has law `μ ⊗ₘ cipherKernel T ν`. -/
lemma map_prod_eq_compProd [Countable E] (T : K → M → E)
    (μ : Measure M) (ν : Measure K) [SFinite μ] [IsProbabilityMeasure ν] :
    (μ.prod ν).map (fun p ↦ (p.1, T p.2 p.1)) = μ ⊗ₘ cipherKernel T ν := by
  refine Measure.ext_of_singleton fun ⟨m, e⟩ ↦ ?_
  have h_pre : (fun p : M × K ↦ (p.1, T p.2 p.1)) ⁻¹' {(m, e)} = {m} ×ˢ {k | T k m = e} := by
    ext ⟨m', k⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_prod]
    exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₁ ▸ h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₁ ▸ h₂⟩⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), h_pre,
    Measure.prod_prod, ← Set.singleton_prod_singleton, compProd_apply_singleton_prod,
    cipherKernel_apply_singleton]

/-- **Perfect secrecy** (Shannon 1949, §10) of the secrecy system `T` with key law `ν`, for the
a priori law `μ` of the messages: for every cryptogram `e` of positive probability
`P(E) = (cipherKernel T ν ∘ₘ μ) {e}`, the a posteriori probability `P_E(M)` of every message `m`
equals its a priori probability `P(M) = μ {m}`.

The probability-measure instances on `μ` and `ν` are not used in the body; they restrict the
definition to a priori and key laws. -/
@[nolint unusedArguments]
def IsPerfectlySecret (μ : Measure M) [IsProbabilityMeasure μ] (T : K → M → E) (ν : Measure K)
    [IsProbabilityMeasure ν] : Prop :=
  ∀ e, (cipherKernel T ν ∘ₘ μ) {e} ≠ 0 →
    ∀ m, (μ ⊗ₘ cipherKernel T ν)[Prod.fst ⁻¹' {m} | Prod.snd ⁻¹' {e}] = μ {m}

/-- A **perfect system** (Shannon 1949, §10): the secrecy system `T` with key law `ν` is perfectly
secret for every a priori law of the messages, "independently of the values" of the a priori
probabilities. -/
def IsPerfectSystem (T : K → M → E) (ν : Measure K) [IsProbabilityMeasure ν] : Prop :=
  ∀ (μ : Measure M) [IsProbabilityMeasure μ], IsPerfectlySecret μ T ν

variable {μ : Measure M} [IsProbabilityMeasure ν]

/-- Refinement of **Theorem 6** of Shannon (1949) to a fixed a priori law `μ`, following his
derivation via Bayes' theorem: perfect secrecy for `μ` holds iff `P_M(E) = P(E)` for every
cryptogram `E` and every message `M` of positive a priori probability. Messages of a priori
probability zero are unconstrained, as Shannon notes when he excludes `P(M) = 0`. -/
theorem isPerfectlySecret_iff [IsProbabilityMeasure μ] :
    IsPerfectlySecret μ T ν ↔
      ∀ m, μ {m} ≠ 0 → ∀ e, cipherKernel T ν m {e} = (cipherKernel T ν ∘ₘ μ) {e} := by
  set κ := cipherKernel T ν
  have hP_ne_top (e : E) : (κ ∘ₘ μ) {e} ≠ ∞ := measure_ne_top _ _
  refine ⟨fun h m hm e ↦ ?_, fun h e hP m ↦ ?_⟩
  · by_cases hP : (κ ∘ₘ μ) {e} = 0
    · rw [hP]
      by_contra hκ
      exact Measure.comp_apply_ne_zero (measurableSet_singleton e) hm hκ hP
    · have h_eq := h e hP m
      rw [cond_eq_mul_div] at h_eq
      have h_eq' := (ENNReal.eq_div_iff hP (hP_ne_top e)).1 h_eq.symm
      exact (ENNReal.mul_right_inj hm (measure_ne_top _ _)).1 (h_eq'.symm.trans (mul_comm _ _))
  · rw [cond_eq_mul_div]
    by_cases hm : μ {m} = 0
    · simp [hm]
    · rw [h m hm e, ENNReal.mul_div_cancel_right hP (hP_ne_top e)]

/-- Refinement of **Theorem 6** of Shannon (1949) to a fixed a priori law `μ` that charges every
message, following his derivation (which divides by `P(M) ≠ 0`): perfect secrecy for `μ` holds
iff `P_M(E) = P(E)` for all `M` and `E`. Theorem 6 itself, where perfect secrecy is required
independently of the a priori probabilities, is `isPerfectSystem_iff_forall_cipherKernel_eq_comp`.
-/
theorem isPerfectlySecret_iff_of_forall_ne_zero [IsProbabilityMeasure μ] (hμ : ∀ m, μ {m} ≠ 0) :
    IsPerfectlySecret μ T ν ↔ ∀ m e, cipherKernel T ν m {e} = (cipherKernel T ν ∘ₘ μ) {e} := by
  rw [isPerfectlySecret_iff]
  exact ⟨fun h m ↦ h m (hμ m), fun h m _ ↦ h m⟩

/-- Perfect secrecy for `μ` holds iff the channel `P_M` from messages to cryptograms has the same
row for all messages of positive a priori probability. -/
theorem isPerfectlySecret_iff_cipherKernel_eq [Countable E] [IsProbabilityMeasure μ] :
    IsPerfectlySecret μ T ν ↔
      ∀ m m', μ {m} ≠ 0 → μ {m'} ≠ 0 → cipherKernel T ν m = cipherKernel T ν m' :=
  isPerfectlySecret_iff.trans forall_apply_eq_comp_apply_iff

/-- **Theorem 6** of Shannon (1949), second form: the system is perfect iff "`P_M(E)` must be
independent of `M`", i.e. all messages have the same channel row `cipherKernel T ν m`. -/
theorem isPerfectSystem_iff [Countable E] :
    IsPerfectSystem T ν ↔ ∀ m m', cipherKernel T ν m = cipherKernel T ν m' := by
  refine ⟨fun h m m' ↦ ?_, fun h μ _ ↦ isPerfectlySecret_iff_cipherKernel_eq.2 fun m m' _ _ ↦
    h m m'⟩
  -- Use the a priori law giving probability `1 / 2` to each of `m` and `m'`.
  set μ : Measure M := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac m + Measure.dirac m')
  have : IsProbabilityMeasure μ := ⟨by
    simp [μ, ENNReal.inv_two_add_inv_two]⟩
  have hm : μ {m} ≠ 0 := by simp [μ]
  have hm' : μ {m'} ≠ 0 := by simp [μ]
  exact isPerfectlySecret_iff_cipherKernel_eq.1 (h μ) m m' hm hm'

/-- **Theorem 6** of Shannon (1949), third form, in terms of keys: the system is perfect
iff "the total probability of all keys that transform `Mᵢ` into a given cryptogram `E` is equal to
that of all keys transforming `Mⱼ` into the same `E`, for all `Mᵢ`, `Mⱼ` and `E`". -/
theorem isPerfectSystem_iff_forall_measure_setOf_eq [Countable E] :
    IsPerfectSystem T ν ↔ ∀ m m' e, ν {k | T k m = e} = ν {k | T k m' = e} := by
  simp_rw [isPerfectSystem_iff, ← cipherKernel_apply_singleton]
  exact ⟨fun h m m' e ↦ by rw [h m m'], fun h m m' ↦ Measure.ext_of_singleton (h m m')⟩

/-- **Theorem 6** of Shannon (1949), as stated in the paper, where perfect secrecy is required
independently of the a priori probabilities: the system is perfect iff `P_M(E) = P(E)` for all
`M` and `E`, whatever the a priori law of the messages. -/
theorem isPerfectSystem_iff_forall_cipherKernel_eq_comp [Countable E] :
    IsPerfectSystem T ν ↔ ∀ μ : Measure M, IsProbabilityMeasure μ →
      ∀ m e, cipherKernel T ν m {e} = (cipherKernel T ν ∘ₘ μ) {e} := by
  refine ⟨fun h μ _ m e ↦ ?_, fun h μ _ ↦ isPerfectlySecret_iff.2 fun m _ e ↦ h μ ‹_› m e⟩
  rw [comp_apply_singleton_eq_lintegral,
    lintegral_congr fun m' ↦ by rw [isPerfectSystem_iff.1 h m' m], lintegral_const, measure_univ,
    mul_one]

end SecrecySystem

section Leakage

/-! ### Perfect secrecy as zero leakage -/

variable [Countable M] [MeasurableSingletonClass M] [Countable K] [MeasurableSingletonClass K]
  [MeasurableSingletonClass E] {T : K → M → E} {μ : Measure M} {ν : Measure K}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Perfect secrecy holds iff the maximal leakage `L(M → E)` from the message to the cryptogram
is zero. -/
theorem isPerfectlySecret_iff_maxLeakage_eq_zero [Fintype E] :
    IsPerfectlySecret μ T ν ↔ maxLeakage μ (cipherKernel T ν) = 0 :=
  isPerfectlySecret_iff_cipherKernel_eq.trans maxLeakage_eq_zero_iff.symm

/-- Perfect secrecy holds iff the message and the cryptogram are independent, i.e. iff their joint
law `μ ⊗ₘ cipherKernel T ν` is the product of its marginals. -/
theorem isPerfectlySecret_iff_compProd_eq_prod [Finite E] :
    IsPerfectlySecret μ T ν ↔ μ ⊗ₘ cipherKernel T ν = μ.prod (cipherKernel T ν ∘ₘ μ) := by
  have := Fintype.ofFinite E
  exact isPerfectlySecret_iff_maxLeakage_eq_zero.trans maxLeakage_eq_zero_iff_compProd_eq_prod

/-- Perfect secrecy holds iff the mutual information `I(M; E)` between the message and the
cryptogram is zero. -/
theorem isPerfectlySecret_iff_mutualInfo_eq_zero [Finite E] :
    IsPerfectlySecret μ T ν ↔ mutualInfo (μ ⊗ₘ cipherKernel T ν) = 0 := by
  rw [isPerfectlySecret_iff_compProd_eq_prod, mutualInfo_compProd, klDiv_eq_zero_iff]

omit [IsProbabilityMeasure μ] in
/-- A secrecy system is perfect iff its maximal leakage is zero for every a priori law of the
messages. -/
theorem isPerfectSystem_iff_forall_maxLeakage_eq_zero [Fintype E] :
    IsPerfectSystem T ν ↔
      ∀ μ : Measure M, IsProbabilityMeasure μ → maxLeakage μ (cipherKernel T ν) = 0 :=
  forall₂_congr fun _ _ ↦ isPerfectlySecret_iff_maxLeakage_eq_zero

end Leakage

end InformationTheory
