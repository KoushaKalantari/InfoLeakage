/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.Amplification.HockeyStick
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Privacy amplification by subsampling

This file formalizes the amplification theorems for Poisson subsampling and for sampling without
replacement, and their tightness, from B. Balle, G. Barthe and M. Gaboardi, *Privacy
amplification by subsampling: tight analyses via couplings and divergences*, NeurIPS 2018
([arXiv:1807.01647](https://arxiv.org/abs/1807.01647)); result numbers follow arXiv v2. The
divergence tools (hockey-stick divergence, privacy profiles, advanced joint convexity) are in
`InfoLeakage.Amplification.HockeyStick`.

**Setting.** Datasets are finite sets `x : Finset U` of records from a countable universe `U`;
with Mathlib's σ-algebra `Finset U` is then discrete, so every map out of it is measurable.
(Countability is an artefact of using Mathlib's σ-algebra on `Finset U`: the paper allows an
arbitrary universe.) A
mechanism is a kernel `M : Kernel (Finset U) Z` into an arbitrary measurable space `Z`, a
subsampling mechanism is a kernel `S : Kernel (Finset U) (Finset U)` whose values are finite
mixtures of Dirac masses, and the subsampled mechanism `M^S` is the kernel composition `M ∘ₖ S`
(`comp_poissonSubsampleKernel_apply` and `comp_samplingWORKernel_apply` unfold it into the
mixtures `∑_y S(x)(y) M(y)` used by the paper). As in the paper, `(ε, δ)`-DP of the subsampled
mechanism is stated for `ε ≥ 0`, with `ε' = log (1 + η (e^ε - 1))`.

**Proofs.** They follow Appendix B: the outputs on neighbouring datasets are overlapping mixtures
`(1 - η) μ₀ + η μ₁` and `(1 - η) μ₀ + η μ₁'`, so advanced joint convexity
(`hockeyStickDiv_mixture_le`) reduces the claim to `D_α(μ₁ ‖ μ₀) ≤ δ` and `D_α(μ₁ ‖ μ₁') ≤ δ`.
These follow from joint convexity along the paper's `d`-compatible couplings, which here are
written out as finite sums: `y ↦ y ∪ {v}` for Poisson subsampling, and `y₀ ∪ {v} ↔ y₀ ∪ {v'}` and
`y₀ ∪ {v} ↔ y₀ ∪ {u}` (`u ∈ x₀ \ y₀`, by the double counting `sum_powersetCard_sum_sdiff`) for
sampling without replacement. Theorem 7 itself is not used.

## Main definitions

* `IsAddRemoveNeighbour`, `IsSubstNeighbour`: the remove/add-one relation `≃ᵣ` and the
  substitute-one relation `≃ₛ` on sets (Section 4).
* `poissonSubsample γ x`, `poissonSubsampleKernel γ`: Poisson subsampling `S^po_γ` (Section 4).
* `samplingWOR m x`, `samplingWORKernel m`: sampling without replacement `S^wo_m` (Section 4).
* `Amplification.randResp p b`, `Amplification.membershipKernel v p`: the randomized response
  `R_p` and the randomized membership mechanism `M_{v,p}` (Section 5).

## Main statements (paper result → Lean name)

* Theorem 8 (Poisson subsampling, `≃ᵣ`): `privacyProfile_comp_poissonSubsampleKernel_le`
  (`δ_{M'}(ε') ≤ γ δ_M(ε)`), with the pairwise form `hockeyStickDiv_comp_poissonSubsampleKernel_le`
  and the `(ε, δ)`-DP form `IsEpsDeltaDP.comp_poissonSubsampleKernel`.
* Theorem 9 (sampling without replacement, `≃ₛ`): `privacyProfile_comp_samplingWORKernel_le`
  (`δ_{M'}(ε') ≤ (m / n) δ_M(ε)`), with the pairwise form
  `hockeyStickDiv_comp_samplingWORKernel_le` and the `(ε, δ)`-DP form
  `IsEpsDeltaDP.comp_samplingWORKernel`.
* Theorem 13 for Theorems 8 and 9 (the bounds are attained by `M_{v,p}`, proved along the lines of
  Lemma 12): `privacyProfile_comp_poissonSubsampleKernel_membershipKernel` and
  `privacyProfile_comp_samplingWORKernel_membershipKernel`, with the privacy profile of `M_{v,p}`
  computed in `Amplification.privacyProfile_membershipKernel` and
  `Amplification.hockeyStickDiv_randResp`.

## Notes on the paper

* Section 4 (arXiv v2, p. 9), the sentence before Theorem 8 calls the subsampled mechanism
  `M^{S^wo_γ}`, and the proof of Theorem 8 (Appendix B) writes `ω = S^wo_η(x)`,
  `ω' = S^wo_η(x')`; all three should be Poisson subsampling `S^po`, as in Theorem 8 itself.
  In the proof of Theorem 9 (Appendix B), "`y = y₀ ∪ {v}` and `y' ∪ {v'}`" should read
  "`y' = y₀ ∪ {v'}`", and "`π_{1,1}` and `π_{0,1}`" should read "`π_{1,1}` and `π_{1,0}`".
  These are typos; Theorems 8 and 9 hold as stated.
* Section 5 (p. 11) claims `D_{e^ε}(ν₀ ‖ ν₁) = D_{e^ε}(ν₁ ‖ ν₀) = ψ_p(ε) = [p - e^ε (1 - p)]₊`
  for `ν_b = R_p(b)`, every `ε ≥ 0` and every `p ∈ [0, 1]`. The value is in fact
  `[p - e^ε (1 - p)]₊ + [(1 - p) - e^ε p]₊` (`Amplification.hockeyStickDiv_randResp`), which equals
  `ψ_p(ε)` iff `p ≥ 1 / (1 + e^ε)`; so the claim holds for all `ε ≥ 0` iff `p ≥ 1/2`. For `p = 0`
  the divergence is `1` while `ψ₀(ε) = 0` (`Amplification.hockeyStickDiv_randResp_zero`). (For
  `e^ε ≥ 1` the two-term value equals `ψ_{max(p, 1 - p)}(ε)`; that identity is not formalized.)
  Lemma 12 inherits this error: its value `η ψ_p(ε)` for the privacy profile of the subsampled
  `M_{v,p}` rests on the Section 5 claim, and is wrong (when `η > 0`) for `p < 1 / (1 + e^ε)`,
  e.g. `p = 0`.
  Theorem 13's tightness survives with the corrected divergence: the theorems below state it as
  an equality of privacy profiles, with the two-term value, for every `p ∈ [0, 1]`.
* Lemma 12 (p. 11, proof in Appendix C) has a second, independent gap: the last step of its proof
  replaces `θ* = sup_{x ≃ x', v ∈ x \ x'} Pr_{y ∼ S(x)}[v ∈ y]` by
  `η = sup_{x ≃ x'} TV(S(x), S(x'))`, and these differ for general natural subsampling mechanisms.
  For example, take `U = {v, w}`, datasets of size `1` under `≃ₛ`, and the natural `S` keeping `v`
  with probability `0.1` and `w` with probability `0.5`; then `η = 0.5`, but for `p = 1` and
  `ε = 0` the supremum of the divergences is `0.1`, not `η ψ_1(0) = 0.5`. For a
  membership-crossing pair (`v ∈ x \ x'`, for the record `v` of `M_{v,p}`) the divergence is
  exactly `θ D_{1 + (e^{ε'} - 1) / θ}(ν₁ ‖ ν₀)` with `θ = Pr_{y ∼ S(x)}[v ∈ y]` (by
  `hockeyStickDiv_mixture_left_eq`), which is `η ψ_p(ε)` (for `p ≥ 1/2`) when `θ = η`. This does
  not characterize the general profile: pairs in which both datasets contain `v` also contribute
  and can dominate. For example (from an independent review; not formalized), take datasets
  `a = {v}`, `b = {w}`, `c = {v, w}` with the symmetric adjacency edges `a ≃ b` and `a ≃ c`, and
  the natural `S` that keeps its whole input with probability `0.1`, `0.1`, `0.9` respectively and
  otherwise returns `∅`. For `p = 1` and `ε = 0` the pair `(c, a)` gives `0.8`, while the only
  membership-crossing pair for `v`, `(a, b)`, gives `θ = 0.1`. For `S^po`, `S^wo` and `S^wr`,
  Theorems 8–10 bound every pair by `η δ_M(ε)` and a membership-crossing pair with
  `θ = θ* = η` attains this bound, so Theorem 13 is unaffected; it is proved here for Theorems 8
  and 9 and every `p ∈ [0, 1]`, stated as equality of privacy profiles.

## Not formalized

* Sampling with replacement (Theorems 10 and 11), Poisson subsampling under substitution
  (Theorem 14), group-privacy profiles, Theorem 7 and the general form of Lemma 12 (arbitrary
  natural subsampling mechanisms), and Theorem 13 for Theorem 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal

namespace InformationTheory

variable {U Z ι : Type*} {mZ : MeasurableSpace Z}

/-! ### Neighbouring relations on finite sets -/

section Neighbour

variable [DecidableEq U]

/-- The **remove/add-one** neighbouring relation `x ≃ᵣ x'` on sets (Section 4): `x'` is obtained
from `x` by adding or by removing a single element. -/
def IsAddRemoveNeighbour (x x' : Finset U) : Prop :=
  ∃ v, (v ∉ x ∧ x' = insert v x) ∨ (v ∉ x' ∧ x = insert v x')

/-- The **substitute-one** neighbouring relation `x ≃ₛ x'` on sets (Section 4): `x'` is obtained
from `x` by replacing one element by a different one, i.e. `x = x₀ ∪ {v}` and `x' = x₀ ∪ {v'}`
with `v ≠ v'` both outside `x₀`. -/
def IsSubstNeighbour (x x' : Finset U) : Prop :=
  ∃ x₀ v v', v ∉ x₀ ∧ v' ∉ x₀ ∧ v ≠ v' ∧ x = insert v x₀ ∧ x' = insert v' x₀

lemma IsAddRemoveNeighbour.symm {x x' : Finset U} (h : IsAddRemoveNeighbour x x') :
    IsAddRemoveNeighbour x' x := by
  obtain ⟨v, h | h⟩ := h
  exacts [⟨v, .inr h⟩, ⟨v, .inl h⟩]

lemma IsSubstNeighbour.symm {x x' : Finset U} (h : IsSubstNeighbour x x') :
    IsSubstNeighbour x' x := by
  obtain ⟨x₀, v, v', hv, hv', hne, rfl, rfl⟩ := h
  exact ⟨x₀, v', v, hv', hv, hne.symm, rfl, rfl⟩

lemma IsSubstNeighbour.card_eq {x x' : Finset U} (h : IsSubstNeighbour x x') : #x = #x' := by
  obtain ⟨x₀, v, v', hv, hv', -, rfl, rfl⟩ := h
  rw [card_insert_of_notMem hv, card_insert_of_notMem hv']

end Neighbour

/-! ### Auxiliary lemmas -/

namespace Amplification

variable {𝒟 : Type*} {m𝒟 : MeasurableSpace 𝒟} [MeasurableSingletonClass 𝒟]

/-- Composing a kernel with a finitely supported measure gives the corresponding mixture. -/
lemma comp_sum_smul_dirac (M : Kernel 𝒟 Z) (s : Finset 𝒟) (w : 𝒟 → ℝ≥0) :
    M ∘ₘ (∑ y ∈ s, w y • Measure.dirac y) = ∑ y ∈ s, w y • M y := by
  ext E hE
  rw [Measure.bind_apply hE M.aemeasurable]
  simp [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

/-- Averaging bound: if `D_γ(P i ‖ Q i) ≤ δ` for all `i ∈ s`, then the uniform mixtures satisfy
`D_γ(avg P ‖ avg Q) ≤ δ`. -/
lemma hockeyStickDiv_avg_le {γ δ : ℝ} {s : Finset ι} (hs : s.Nonempty) (P Q : ι → Measure Z)
    [∀ i, IsFiniteMeasure (P i)] [∀ i, IsFiniteMeasure (Q i)]
    (h : ∀ i ∈ s, hockeyStickDiv γ (P i) (Q i) ≤ δ) :
    hockeyStickDiv γ ((#s : ℝ≥0)⁻¹ • ∑ i ∈ s, P i) ((#s : ℝ≥0)⁻¹ • ∑ i ∈ s, Q i) ≤ δ := by
  have hpos : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  rw [hockeyStickDiv_smul]
  calc ((#s : ℝ≥0)⁻¹ : ℝ) * hockeyStickDiv γ (∑ i ∈ s, P i) (∑ i ∈ s, Q i)
      ≤ ((#s : ℝ≥0)⁻¹ : ℝ) * (#s * δ) := by
        gcongr
        exact (hockeyStickDiv_sum_le s P Q).trans <| (sum_le_sum h).trans_eq <| by simp
    _ = δ := by push_cast; field_simp

/-- Double counting: choosing a `k`-subset `y` of `s` and then a point `u ∈ s \ y` is the same as
choosing a `(k + 1)`-subset of `s` together with one of its `k + 1` points. -/
lemma sum_powersetCard_sum_sdiff [DecidableEq U] {A : Type*} [AddCommMonoid A] (s : Finset U)
    (k : ℕ) (f : Finset U → A) :
    ∑ y ∈ s.powersetCard k, ∑ u ∈ s \ y, f (insert u y) =
      (k + 1) • ∑ y ∈ s.powersetCard (k + 1), f y := by
  have : (k + 1) • ∑ y ∈ s.powersetCard (k + 1), f y =
      ∑ y ∈ s.powersetCard (k + 1), ∑ _u ∈ y, f y := by
    rw [smul_sum]
    refine sum_congr rfl fun y hy ↦ ?_
    rw [sum_const, (mem_powersetCard.1 hy).2]
  rw [this, sum_sigma', sum_sigma']
  refine sum_bij' (fun p _ ↦ ⟨insert p.2 p.1, p.2⟩) (fun p _ ↦ ⟨p.1.erase p.2, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨y, u⟩ hp
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hp ⊢
    exact ⟨⟨insert_subset hp.2.1 hp.1.1, by rw [card_insert_of_notMem hp.2.2, hp.1.2]⟩,
      mem_insert_self _ _⟩
  · rintro ⟨y, u⟩ hp
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hp ⊢
    exact ⟨⟨(erase_subset _ _).trans hp.1.1, by rw [card_erase_of_mem hp.2, hp.1.2]; rfl⟩,
      hp.1.1 hp.2, notMem_erase _ _⟩
  · rintro ⟨y, u⟩ hp
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hp
    simp [erase_insert hp.2.2]
  · rintro ⟨y, u⟩ hp
    simp only [mem_sigma] at hp
    simp [insert_erase hp.2]
  · intro _ _
    rfl

end Amplification

open Amplification

/-! ### Poisson subsampling -/

section Poisson

variable {γ : ℝ≥0}

/-- **Poisson subsampling** `S^po_γ(x)` (Section 4): the law of the random subset `y ⊆ x` that
contains each element of `x` independently with probability `γ`, i.e.
`S^po_γ(x)(y) = γ^{|y|} (1 - γ)^{|x| - |y|}`. -/
noncomputable def poissonSubsample (γ : ℝ≥0) (x : Finset U) : Measure (Finset U) :=
  ∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • Measure.dirac y

/-- Poisson subsampling is a probability distribution for `γ ≤ 1`. -/
lemma isProbabilityMeasure_poissonSubsample (hγ : γ ≤ 1) (x : Finset U) :
    IsProbabilityMeasure (poissonSubsample γ x) := by
  constructor
  simp only [poissonSubsample, FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ]
  rw [← sum_smul, sum_pow_mul_eq_add_pow, add_tsub_cancel_of_le hγ, one_pow, one_smul]

/-- Poisson subsampling as a kernel from datasets to subsamples. -/
noncomputable def poissonSubsampleKernel [Countable U] (γ : ℝ≥0) : Kernel (Finset U) (Finset U)
    where
  toFun := poissonSubsample γ
  measurable' := .of_discrete

lemma poissonSubsampleKernel_apply [Countable U] (x : Finset U) :
    poissonSubsampleKernel γ x = poissonSubsample γ x := rfl

lemma isMarkovKernel_poissonSubsampleKernel [Countable U] (hγ : γ ≤ 1) :
    IsMarkovKernel (poissonSubsampleKernel (U := U) γ) :=
  ⟨isProbabilityMeasure_poissonSubsample hγ⟩

variable [Countable U] (M : Kernel (Finset U) Z)

/-- The subsampled mechanism `M^{S^po_γ}(x)` is the mixture
`∑_{y ⊆ x} γ^{|y|} (1 - γ)^{|x| - |y|} M(y)`. -/
lemma comp_poissonSubsampleKernel_apply (x : Finset U) :
    (M ∘ₖ poissonSubsampleKernel γ) x =
      ∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • M y := by
  rw [Kernel.comp_apply, poissonSubsampleKernel_apply, poissonSubsample, comp_sum_smul_dirac]

end Poisson

section PoissonAmplification

variable [DecidableEq U] {γ : ℝ≥0} (M : Kernel (Finset U) Z)

/-- Adding a point `v ∉ x` splits the Poisson mixture over subsets of `insert v x` into the
subsets that avoid `v` (weight `1 - γ`) and those that contain it (weight `γ`). -/
lemma Amplification.sum_powerset_insert_poisson {x : Finset U} {v : U} (hv : v ∉ x) :
    ∑ y ∈ (insert v x).powerset, (γ ^ #y * (1 - γ) ^ (#(insert v x) - #y)) • M y =
      (1 - γ) • ∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • M y +
        γ • ∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • M (insert v y) := by
  rw [sum_powerset_insert hv, card_insert_of_notMem hv, smul_sum, smul_sum]
  congr 1
  · refine sum_congr rfl fun y hy ↦ ?_
    rw [smul_smul, Nat.sub_add_comm (card_le_card (mem_powerset.1 hy)), pow_succ]
    congr 1
    ring
  · refine sum_congr rfl fun y hy ↦ ?_
    have hvy : v ∉ y := fun h ↦ hv (mem_powerset.1 hy h)
    rw [smul_smul, card_insert_of_notMem hvy, Nat.add_sub_add_right, pow_succ]
    congr 1
    ring

variable [Countable U] [IsMarkovKernel M]

/-- **Theorem 8** (Poisson subsampling, remove/add-one relation), pairwise form: if
`D_α(M(y) ‖ M(y')) ≤ δ` for all `y ≃ᵣ y'`, then for all `x ≃ᵣ x'` the subsampled mechanism
satisfies `D_{α'}(M^S(x) ‖ M^S(x')) ≤ γ δ`, where `α' = 1 + γ (α - 1)`.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem hockeyStickDiv_comp_poissonSubsampleKernel_le (hγ : γ ≤ 1) {α δ : ℝ} (hα : 1 ≤ α)
    (hM : ∀ ⦃y y'⦄, IsAddRemoveNeighbour y y' → hockeyStickDiv α (M y) (M y') ≤ δ)
    {x x' : Finset U} (hx : IsAddRemoveNeighbour x x') :
    hockeyStickDiv (1 + γ * (α - 1)) ((M ∘ₖ poissonSubsampleKernel γ) x)
      ((M ∘ₖ poissonSubsampleKernel γ) x') ≤ γ * δ := by
  have hδ : 0 ≤ δ := hockeyStickDiv_nonneg.trans (hM hx)
  -- `A x` is the subsampled output on `x`, `B x v` the same with `v` added to every subsample
  set A : Finset U → Measure Z := fun x ↦ ∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • M y
  set B : Finset U → U → Measure Z := fun x v ↦
    ∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • M (insert v y)
  have hw (x : Finset U) :
      ∑ y ∈ x.powerset, ((γ ^ #y * (1 - γ) ^ (#x - #y) : ℝ≥0) : ℝ) = 1 := by
    rw [← NNReal.coe_sum, sum_pow_mul_eq_add_pow, add_tsub_cancel_of_le hγ, one_pow,
      NNReal.coe_one]
  have hAB {x : Finset U} {v : U} (hv : v ∉ x) {P Q : Finset U → Measure Z}
      (hPQ : ∀ y ⊆ x, hockeyStickDiv α (P y) (Q y) ≤ δ) [∀ y, IsFiniteMeasure (P y)]
      [∀ y, IsFiniteMeasure (Q y)] :
      hockeyStickDiv α (∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • P y)
        (∑ y ∈ x.powerset, (γ ^ #y * (1 - γ) ^ (#x - #y)) • Q y) ≤ δ := by
    refine (hockeyStickDiv_sum_smul_le _ _ _ _).trans ?_
    calc _ ≤ ∑ y ∈ x.powerset, ((γ ^ #y * (1 - γ) ^ (#x - #y) : ℝ≥0) : ℝ) * δ :=
          sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left (hPQ y (mem_powerset.1 hy))
            (NNReal.coe_nonneg _)
      _ = δ := by rw [← sum_mul, hw, one_mul]
  have hself (μ : Measure Z) : (1 - γ) • μ + γ • μ = μ := by
    rw [← add_smul, tsub_add_cancel_of_le hγ, one_smul]
  have hnotMem {x y : Finset U} {v : U} (hv : v ∉ x) (hy : y ⊆ x) : v ∉ y := fun h ↦ hv (hy h)
  rw [comp_poissonSubsampleKernel_apply, comp_poissonSubsampleKernel_apply]
  obtain ⟨v, ⟨hv, rfl⟩ | ⟨hv, rfl⟩⟩ := hx
  · -- `x' = x ∪ {v}`: `M^S(x) = A x` and `M^S(x') = (1 - γ) A x + γ B x v`
    have h := hockeyStickDiv_mixture_le (μ₀ := A x) (μ₁ := A x) (μ₁' := B x v) hγ hα
      (by rw [hockeyStickDiv_self hα]; exact hδ)
      (hAB hv fun y hy ↦ hM ⟨v, .inl ⟨hnotMem hv hy, rfl⟩⟩)
    rwa [hself, ← Amplification.sum_powerset_insert_poisson M hv] at h
  · -- `x = x' ∪ {v}`: `M^S(x) = (1 - γ) A x' + γ B x' v` and `M^S(x') = A x'`
    have hBA := hAB hv fun y hy ↦ hM ⟨v, .inr ⟨hnotMem hv hy, rfl⟩⟩
    have h := hockeyStickDiv_mixture_le (μ₀ := A x') (μ₁ := B x' v) (μ₁' := A x') hγ hα hBA hBA
    rwa [hself, ← Amplification.sum_powerset_insert_poisson M hv] at h

/-- **Theorem 8** (Poisson subsampling, remove/add-one relation): if `M` is `(ε, δ)`-DP, then the
Poisson-subsampled mechanism `M^{S^po_γ}` is `(log (1 + γ (e^ε - 1)), γ δ)`-DP.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem IsEpsDeltaDP.comp_poissonSubsampleKernel (hγ : γ ≤ 1) {ε δ : ℝ} (hε : 0 ≤ ε)
    (h : IsEpsDeltaDP M IsAddRemoveNeighbour ε δ) :
    IsEpsDeltaDP (M ∘ₖ poissonSubsampleKernel γ) IsAddRemoveNeighbour
      (log (1 + γ * (exp ε - 1))) (γ * δ) := by
  have := isMarkovKernel_poissonSubsampleKernel (U := U) hγ
  rw [isEpsDeltaDP_iff_forall_hockeyStickDiv_le] at h ⊢
  intro x x' hx
  rw [exp_log (by nlinarith [one_le_exp hε, γ.coe_nonneg])]
  exact hockeyStickDiv_comp_poissonSubsampleKernel_le M hγ (one_le_exp hε) h hx

/-- **Theorem 8** (Poisson subsampling, remove/add-one relation), privacy-profile form:
`δ_{M'}(ε') ≤ γ δ_M(ε)` for `M' = M^{S^po_γ}` and `ε' = log (1 + γ (e^ε - 1))`.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem privacyProfile_comp_poissonSubsampleKernel_le (hγ : γ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    privacyProfile (M ∘ₖ poissonSubsampleKernel γ) IsAddRemoveNeighbour
      (log (1 + γ * (exp ε - 1))) ≤ γ * privacyProfile M IsAddRemoveNeighbour ε := by
  refine Real.iSup_le (fun p ↦ ?_) (mul_nonneg γ.coe_nonneg privacyProfile_nonneg)
  rw [exp_log (by nlinarith [one_le_exp hε, γ.coe_nonneg])]
  exact hockeyStickDiv_comp_poissonSubsampleKernel_le M hγ (one_le_exp hε)
    (fun _ _ hy ↦ hockeyStickDiv_le_privacyProfile hy) p.2

end PoissonAmplification

/-! ### Sampling without replacement -/

section WOR

/-- **Sampling without replacement** `S^wo_m(x)` (Section 4): the uniform law on the
`m`-element subsets of `x`. It is a probability measure when `m ≤ |x|` (and `0` otherwise). -/
noncomputable def samplingWOR (m : ℕ) (x : Finset U) : Measure (Finset U) :=
  ∑ y ∈ x.powersetCard m, ((#x).choose m : ℝ≥0)⁻¹ • Measure.dirac y

lemma samplingWOR_univ (m : ℕ) (x : Finset U) :
    samplingWOR m x Set.univ = (((#x).choose m : ℝ≥0) * ((#x).choose m : ℝ≥0)⁻¹ : ℝ≥0) := by
  simp only [samplingWOR, FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ]
  rw [sum_const, card_powersetCard, ← Nat.cast_smul_eq_nsmul ℝ≥0, smul_smul, ENNReal.smul_one]

/-- Sampling without replacement is a probability distribution for `m ≤ |x|`. -/
lemma isProbabilityMeasure_samplingWOR {m : ℕ} {x : Finset U} (hm : m ≤ #x) :
    IsProbabilityMeasure (samplingWOR m x) :=
  ⟨by rw [samplingWOR_univ, mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos hm).ne'),
    ENNReal.coe_one]⟩

/-- Sampling without replacement as a kernel from datasets to subsamples. -/
noncomputable def samplingWORKernel [Countable U] (m : ℕ) : Kernel (Finset U) (Finset U) where
  toFun := samplingWOR m
  measurable' := .of_discrete

variable [Countable U]

lemma samplingWORKernel_apply (m : ℕ) (x : Finset U) :
    samplingWORKernel m x = samplingWOR m x := rfl

instance (m : ℕ) : IsFiniteKernel (samplingWORKernel (U := U) m) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x ↦ by
    rw [samplingWORKernel_apply, samplingWOR_univ, ← ENNReal.coe_one, ENNReal.coe_le_coe]
    by_cases h : ((#x).choose m : ℝ≥0) = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h]⟩⟩

/-- The subsampled mechanism `M^{S^wo_m}(x)` is the uniform mixture of `M(y)` over the
`m`-subsets `y ⊆ x`. -/
lemma comp_samplingWORKernel_apply (M : Kernel (Finset U) Z) (m : ℕ) (x : Finset U) :
    (M ∘ₖ samplingWORKernel m) x = ∑ y ∈ x.powersetCard m, ((#x).choose m : ℝ≥0)⁻¹ • M y := by
  rw [Kernel.comp_apply, samplingWORKernel_apply, samplingWOR, comp_sum_smul_dirac]

end WOR

section WORAmplification

variable [DecidableEq U]

/-- The `(k + 1)`-subsets of `x ∪ {v}` are the `(k + 1)`-subsets of `x` and the sets `y ∪ {v}`
for the `k`-subsets `y` of `x`. -/
lemma Amplification.sum_powersetCard_succ_insert {A : Type*} [AddCommMonoid A]
    (f : Finset U → A) {x : Finset U} {v : U} (hv : v ∉ x) (k : ℕ) :
    ∑ y ∈ (insert v x).powersetCard (k + 1), f y =
      ∑ y ∈ x.powersetCard (k + 1), f y + ∑ y ∈ x.powersetCard k, f (insert v y) := by
  have hvy {y : Finset U} {j : ℕ} (hy : y ∈ x.powersetCard j) : v ∉ y :=
    fun h ↦ hv ((mem_powersetCard.1 hy).1 h)
  rw [powersetCard_succ_insert hv, sum_union, sum_image]
  · intro y₁ hy₁ y₂ hy₂ h
    rw [← erase_insert (hvy hy₁), ← erase_insert (hvy hy₂)]
    exact congrArg (·.erase v) h
  · rw [disjoint_left]
    intro y hy hy'
    obtain ⟨z, -, rfl⟩ := mem_image.1 hy'
    exact hvy hy (mem_insert_self v z)

/-- For `v ∉ x₀` and `k < |x₀| = N`, the uniform mixture over the `(k + 1)`-subsets of
`x₀ ∪ {v}` is the overlapping mixture, with weight `η = (k + 1) / (N + 1)`, of the uniform mixture
over the `(k + 1)`-subsets of `x₀` and the uniform mixture of `f(y ∪ {v})` over the `k`-subsets
`y` of `x₀`. -/
lemma Amplification.sum_powersetCard_insert_eq_mixture (f : Finset U → Measure Z)
    {x₀ : Finset U} {v : U} (hv : v ∉ x₀) {k : ℕ} (hk : k < #x₀) :
    ∑ y ∈ (insert v x₀).powersetCard (k + 1), ((#x₀ + 1).choose (k + 1) : ℝ≥0)⁻¹ • f y =
      (1 - ((k + 1 : ℕ) : ℝ≥0) / ((#x₀ + 1 : ℕ) : ℝ≥0)) •
          (((#x₀).choose (k + 1) : ℝ≥0)⁻¹ • ∑ y ∈ x₀.powersetCard (k + 1), f y) +
        (((k + 1 : ℕ) : ℝ≥0) / ((#x₀ + 1 : ℕ) : ℝ≥0)) •
          (((#x₀).choose k : ℝ≥0)⁻¹ • ∑ y ∈ x₀.powersetCard k, f (insert v y)) := by
  set N := #x₀
  set η : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0) / ((N + 1 : ℕ) : ℝ≥0) with hηdef
  have hη : η ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast (by omega : k + 1 ≤ N + 1)) zero_le
  have hηℝ : (η : ℝ) = ((k + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    rw [hηdef, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
  have hpos₁ : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk.le
  have hpos₂ : (0 : ℝ) < N.choose (k + 1) := by exact_mod_cast Nat.choose_pos hk
  have hpos₃ : (0 : ℝ) < (N + 1).choose (k + 1) := by exact_mod_cast Nat.choose_pos (by omega)
  have e₁ : ((N : ℝ) + 1) * N.choose k = (N + 1).choose (k + 1) * (k + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq N k
  have e₂ : (N.choose (k + 1) : ℝ) * (N + 1) = (N + 1).choose (k + 1) * (N - k) := by
    rw [← Nat.cast_sub hk.le, ← Nat.add_sub_add_right N 1 k]
    exact_mod_cast Nat.choose_mul_succ_eq N (k + 1)
  -- `1 / C(n, m) = (1 - η) / C(N, k + 1) = η / C(N, k)`
  have hc₀ : ((N + 1).choose (k + 1) : ℝ≥0)⁻¹ = (1 - η) * (N.choose (k + 1) : ℝ≥0)⁻¹ := by
    rw [← NNReal.coe_inj]
    push_cast [NNReal.coe_sub hη, hηℝ]
    field_simp
    linear_combination e₂
  have hc₁ : ((N + 1).choose (k + 1) : ℝ≥0)⁻¹ = η * (N.choose k : ℝ≥0)⁻¹ := by
    rw [← NNReal.coe_inj]
    push_cast [hηℝ]
    field_simp
    linear_combination e₁
  rw [← smul_sum, sum_powersetCard_succ_insert _ hv, smul_add, smul_smul, smul_smul, ← hc₀, ← hc₁]

variable [Countable U] (M : Kernel (Finset U) Z) [IsMarkovKernel M]

/-- **Theorem 9** (sampling without replacement, substitution relation), pairwise form: if
`D_α(M(y) ‖ M(y')) ≤ δ` for all `y ≃ₛ y'` of size `m`, then for all `x ≃ₛ x'` of size `n ≥ m`
the subsampled mechanism satisfies `D_{α'}(M^S(x) ‖ M^S(x')) ≤ (m / n) δ`, where
`α' = 1 + (m / n) (α - 1)`.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem hockeyStickDiv_comp_samplingWORKernel_le {n m : ℕ} (hmn : m ≤ n) {α δ : ℝ} (hα : 1 ≤ α)
    (hM : ∀ ⦃y y'⦄, IsSubstNeighbour y y' → #y = m → hockeyStickDiv α (M y) (M y') ≤ δ)
    {x x' : Finset U} (hx : IsSubstNeighbour x x') (hxn : #x = n) :
    hockeyStickDiv (1 + (m / n : ℝ) * (α - 1)) ((M ∘ₖ samplingWORKernel m) x)
      ((M ∘ₖ samplingWORKernel m) x') ≤ (m / n : ℝ) * δ := by
  obtain ⟨x₀, v, v', hv, hv', hne, rfl, rfl⟩ := hx
  rw [card_insert_of_notMem hv] at hxn
  subst hxn
  rw [comp_samplingWORKernel_apply, comp_samplingWORKernel_apply, card_insert_of_notMem hv,
    card_insert_of_notMem hv']
  rcases Nat.eq_zero_or_pos m with rfl | hm₀
  · simp only [powersetCard_zero, sum_singleton, CharP.cast_eq_zero, zero_div, zero_mul, add_zero]
    rw [hockeyStickDiv_self le_rfl]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hnb {y : Finset U} {j : ℕ} {w : U} (hw : w ∉ x₀) (hy : y ∈ x₀.powersetCard j) : w ∉ y :=
    fun h ↦ hw ((mem_powersetCard.1 hy).1 h)
  have hcard {y : Finset U} {w : U} (hw : w ∉ x₀) (hy : y ∈ x₀.powersetCard k) :
      #(insert w y) = k + 1 := by
    rw [card_insert_of_notMem (hnb hw hy), (mem_powersetCard.1 hy).2]
  set N := #x₀ with hN
  rcases Nat.lt_or_eq_of_le hmn with hlt | heq
  swap
  · -- `m = n`: the subsample is the whole dataset
    have hk : k = N := by omega
    subst hk
    have hself {w : U} (hw : w ∉ x₀) : (insert w x₀).powersetCard (#x₀ + 1) = {insert w x₀} := by
      rw [← card_insert_of_notMem hw, powersetCard_self]
    have h1 : ((#x₀ + 1 : ℕ) : ℝ) / ((#x₀ + 1 : ℕ) : ℝ) = 1 := div_self (by positivity)
    rw [hself hv, hself hv', sum_singleton, sum_singleton, Nat.choose_self, Nat.cast_one, inv_one,
      one_smul, one_smul, h1, one_mul, one_mul, add_sub_cancel]
    exact hM ⟨x₀, v, v', hv, hv', hne, rfl, rfl⟩ (card_insert_of_notMem hv)
  -- `0 < m < n`
  have hkN : k < N := by omega
  set η : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0) / ((N + 1 : ℕ) : ℝ≥0) with hηdef
  have hη : η ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hmn) zero_le
  have hηℝ : (η : ℝ) = ((k + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    rw [hηdef, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
  set S := ∑ y ∈ x₀.powersetCard (k + 1), M y with hS
  set B : U → Measure Z := fun w ↦ ∑ y ∈ x₀.powersetCard k, M (insert w y) with hB
  rw [sum_powersetCard_insert_eq_mixture _ hv hkN, sum_powersetCard_insert_eq_mixture _ hv' hkN,
    ← hηℝ]
  refine hockeyStickDiv_mixture_le hη hα ?_ ?_
  · -- `D_α(μ₁ ‖ μ₀) ≤ δ`, through the coupling `y ∪ {v} ↔ y ∪ {u}`, `u ∈ x₀ \ y`
    obtain ⟨σ, hσ⟩ : ∃ σ, σ = (x₀.powersetCard k).sigma fun y ↦ x₀ \ y := ⟨_, rfl⟩
    have hsd {y : Finset U} (hy : y ∈ x₀.powersetCard k) : #(x₀ \ y) = N - k := by
      rw [card_sdiff_of_subset (mem_powersetCard.1 hy).1, (mem_powersetCard.1 hy).2]
    have hσcard : #σ = N.choose k * (N - k) := by
      rw [hσ, card_sigma, sum_congr rfl fun y hy ↦ hsd hy, sum_const, card_powersetCard,
        smul_eq_mul]
    have hinv (a d : ℕ) (hd : d ≠ 0) : ((a * d : ℕ) : ℝ≥0)⁻¹ * (d : ℝ≥0) = (a : ℝ≥0)⁻¹ := by
      rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hd), mul_one]
    have hP : (N.choose k : ℝ≥0)⁻¹ • B v = (#σ : ℝ≥0)⁻¹ • ∑ p ∈ σ, M (insert v p.1) := by
      rw [hσ, sum_sigma, sum_congr rfl (g := fun y ↦ (N - k) • M (insert v y))
        fun y hy ↦ by simp only [sum_const, hsd hy], ← smul_sum,
        ← Nat.cast_smul_eq_nsmul ℝ≥0, smul_smul, ← hσ, hσcard, hinv _ _ (by omega)]
    have hQ : (N.choose (k + 1) : ℝ≥0)⁻¹ • S =
        (#σ : ℝ≥0)⁻¹ • ∑ p ∈ σ, M (insert p.2 p.1) := by
      rw [hσ, sum_sigma, Amplification.sum_powersetCard_sum_sdiff, ← Nat.cast_smul_eq_nsmul ℝ≥0,
        smul_smul, ← hσ, hσcard, ← Nat.choose_succ_right_eq, hinv _ _ k.succ_ne_zero]
    rw [hP, hQ]
    refine hockeyStickDiv_avg_le ?_ _ _ fun p hp ↦ ?_
    · rw [← card_pos, hσcard]
      exact Nat.mul_pos (Nat.choose_pos hkN.le) (Nat.sub_pos_of_lt hkN)
    · rw [hσ, mem_sigma, mem_sdiff] at hp
      refine hM ⟨p.1, v, p.2, hnb hv hp.1, ?_, ?_, rfl, rfl⟩ (hcard hv hp.1)
      · exact hp.2.2
      · rintro rfl
        exact hv hp.2.1
  · -- `D_α(μ₁ ‖ μ₁') ≤ δ`, through the coupling `y ∪ {v} ↔ y ∪ {v'}`
    have := hockeyStickDiv_avg_le (γ := α) (δ := δ) (powersetCard_nonempty.2 hkN.le)
      (fun y ↦ M (insert v y)) (fun y ↦ M (insert v' y))
      fun y hy ↦ hM ⟨y, v, v', hnb hv hy, hnb hv' hy, hne, rfl, rfl⟩ (hcard hv hy)
    rwa [card_powersetCard] at this

/-- **Theorem 9** (sampling without replacement, substitution relation): if `M` is `(ε, δ)`-DP
with respect to substitution on datasets of size `m ≤ n`, then the subsampled mechanism
`M^{S^wo_m}` is `(log (1 + (m / n) (e^ε - 1)), (m / n) δ)`-DP with respect to substitution on
datasets of size `n`.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem IsEpsDeltaDP.comp_samplingWORKernel {n m : ℕ} (hmn : m ≤ n) {ε δ : ℝ} (hε : 0 ≤ ε)
    (h : IsEpsDeltaDP M (fun y y' ↦ IsSubstNeighbour y y' ∧ #y = m) ε δ) :
    IsEpsDeltaDP (M ∘ₖ samplingWORKernel m) (fun x x' ↦ IsSubstNeighbour x x' ∧ #x = n)
      (log (1 + m / n * (exp ε - 1))) (m / n * δ) := by
  rw [isEpsDeltaDP_iff_forall_hockeyStickDiv_le] at h ⊢
  rintro x x' ⟨hx, hxn⟩
  rw [exp_log (by nlinarith [one_le_exp hε, (by positivity : (0 : ℝ) ≤ m / n)])]
  exact hockeyStickDiv_comp_samplingWORKernel_le M hmn (one_le_exp hε)
    (fun _ _ hy hym ↦ h ⟨hy, hym⟩) hx hxn

/-- **Theorem 9** (sampling without replacement, substitution relation), privacy-profile form:
`δ_{M'}(ε') ≤ (m / n) δ_M(ε)` for `M' = M^{S^wo_m}` on datasets of size `n ≥ m` and
`ε' = log (1 + (m / n) (e^ε - 1))`.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem privacyProfile_comp_samplingWORKernel_le {n m : ℕ} (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε) :
    privacyProfile (M ∘ₖ samplingWORKernel m) (fun x x' ↦ IsSubstNeighbour x x' ∧ #x = n)
      (log (1 + m / n * (exp ε - 1))) ≤
        m / n * privacyProfile M (fun y y' ↦ IsSubstNeighbour y y' ∧ #y = m) ε := by
  refine Real.iSup_le (fun p ↦ ?_) (mul_nonneg (by positivity) privacyProfile_nonneg)
  rw [exp_log (by nlinarith [one_le_exp hε, (by positivity : (0 : ℝ) ≤ m / n)])]
  exact hockeyStickDiv_comp_samplingWORKernel_le M hmn (one_le_exp hε)
    (fun _ _ hy hym ↦ hockeyStickDiv_le_privacyProfile (Adj := fun y y' ↦ IsSubstNeighbour y y' ∧
      #y = m) ⟨hy, hym⟩) p.2.1 p.2.2

end WORAmplification

/-! ### Tightness -/

namespace Amplification

/-- The randomized response `R_p(b)` on `Bool` (Section 5): it returns `b` with probability `p`
and `!b` with probability `1 - p`. -/
noncomputable def randResp (p : ℝ≥0) (b : Bool) : Measure Bool :=
  p • Measure.dirac b + (1 - p) • Measure.dirac (!b)

variable {p : ℝ≥0}

lemma isProbabilityMeasure_randResp (hp : p ≤ 1) (b : Bool) :
    IsProbabilityMeasure (randResp p b) :=
  ⟨by simpa [randResp] using add_tsub_cancel_of_le (ENNReal.coe_le_one_iff.2 hp)⟩

lemma randResp_real_singleton (hp : p ≤ 1) (b c : Bool) :
    (randResp p b).real {c} = if c = b then (p : ℝ) else 1 - p := by
  rw [randResp, measureReal_add_apply]
  cases b <;> cases c <;> simp [NNReal.coe_sub hp]

/-- The hockey-stick divergence between the two outputs of randomized response:
`D_α(R_p(b) ‖ R_p(!b)) = [p - α (1 - p)]₊ + [(1 - p) - α p]₊`, for either `b`. -/
lemma hockeyStickDiv_randResp (hp : p ≤ 1) (α : ℝ) (b : Bool) :
    hockeyStickDiv α (randResp p b) (randResp p (!b)) =
      max 0 (p - α * (1 - p)) + max 0 ((1 - p) - α * p) := by
  have := isProbabilityMeasure_randResp hp
  rw [hockeyStickDiv_eq_sum, Fintype.sum_bool]
  cases b <;> simp [randResp_real_singleton hp, add_comm]

/-- Counterexample to the formula `D_{e^ε}(ν₀ ‖ ν₁) = ψ_p(ε) = [p - e^ε (1 - p)]₊` of Section 5
(`ν_b = R_p(b)`) at `p = 0`: the divergence is `1`, while `ψ₀(ε) = 0`. -/
theorem hockeyStickDiv_randResp_zero (ε : ℝ) :
    hockeyStickDiv (exp ε) (randResp 0 false) (randResp 0 true) = 1 ∧
      max 0 (((0 : ℝ≥0) : ℝ) - exp ε * (1 - ((0 : ℝ≥0) : ℝ))) = 0 := by
  refine ⟨?_, by simp [(exp_pos ε).le]⟩
  rw [show randResp 0 true = randResp 0 (!false) from rfl, hockeyStickDiv_randResp zero_le_one]
  simp [(exp_pos ε).le]

/-- The randomized membership mechanism `M_{v,p}(x) = R_p(1[v ∈ x])` of Section 5. -/
noncomputable def membershipKernel [DecidableEq U] [Countable U] (v : U) (p : ℝ≥0) :
    Kernel (Finset U) Bool where
  toFun x := randResp p (decide (v ∈ x))
  measurable' := .of_discrete

variable [DecidableEq U] [Countable U]

lemma membershipKernel_apply (v : U) (x : Finset U) :
    membershipKernel v p x = randResp p (decide (v ∈ x)) := rfl

lemma isMarkovKernel_membershipKernel (hp : p ≤ 1) (v : U) :
    IsMarkovKernel (membershipKernel v p) :=
  ⟨fun _ ↦ isProbabilityMeasure_randResp hp _⟩

/-- For every neighbouring relation, the privacy profile of the randomized membership mechanism
is at most `D_{e^ε}(R_p(1) ‖ R_p(0))`. -/
theorem privacyProfile_membershipKernel_le (hp : p ≤ 1) (v : U) (Adj : Finset U → Finset U → Prop)
    {ε : ℝ} (hε : 0 ≤ ε) :
    privacyProfile (membershipKernel v p) Adj ε ≤
      hockeyStickDiv (exp ε) (randResp p true) (randResp p false) := by
  have := isProbabilityMeasure_randResp hp
  refine Real.iSup_le (fun q ↦ ?_) hockeyStickDiv_nonneg
  rw [membershipKernel_apply, membershipKernel_apply]
  generalize decide (v ∈ q.1.1) = b
  generalize decide (v ∈ q.1.2) = b'
  by_cases hb : b' = b
  · rw [hb, hockeyStickDiv_self (one_le_exp hε)]
    exact hockeyStickDiv_nonneg
  · rw [show b' = !b by cases b <;> cases b' <;> simp_all, hockeyStickDiv_randResp hp,
      ← hockeyStickDiv_randResp hp _ true, Bool.not_true]

/-- The privacy profile of the randomized membership mechanism with respect to the remove/add-one
relation is `D_{e^ε}(R_p(1) ‖ R_p(0))`. -/
theorem privacyProfile_membershipKernel (hp : p ≤ 1) (v : U) {ε : ℝ} (hε : 0 ≤ ε) :
    privacyProfile (membershipKernel v p) IsAddRemoveNeighbour ε =
      hockeyStickDiv (exp ε) (randResp p true) (randResp p false) := by
  have := isMarkovKernel_membershipKernel hp v
  refine le_antisymm (privacyProfile_membershipKernel_le hp v _ hε) ?_
  have h := hockeyStickDiv_le_privacyProfile (M := membershipKernel v p) (ε := ε)
    (show IsAddRemoveNeighbour {v} ∅ from ⟨v, .inr ⟨notMem_empty v, rfl⟩⟩)
  simpa [membershipKernel_apply] using h

end Amplification

/-- **Theorem 13** for Theorem 8 (tightness of Poisson subsampling): for the randomized membership
mechanism `M_{v,p}`, the bound of Theorem 8 is an equality,
`δ_{M'}(log (1 + γ (e^ε - 1))) = γ δ_M(ε)` for `M' = M^{S^po_γ}`, for every `p ∈ [0, 1]`.
`U` is countable here (see the module docstring); the paper allows any universe. -/
theorem privacyProfile_comp_poissonSubsampleKernel_membershipKernel [DecidableEq U] [Countable U]
    {p γ : ℝ≥0} (hp : p ≤ 1) (hγ : γ ≤ 1) (v : U) {ε : ℝ} (hε : 0 ≤ ε) :
    privacyProfile (membershipKernel v p ∘ₖ poissonSubsampleKernel γ) IsAddRemoveNeighbour
      (log (1 + γ * (exp ε - 1))) =
        γ * privacyProfile (membershipKernel v p) IsAddRemoveNeighbour ε := by
  have := isMarkovKernel_membershipKernel hp v
  have := isMarkovKernel_poissonSubsampleKernel (U := U) hγ
  have := isProbabilityMeasure_randResp hp
  refine le_antisymm (privacyProfile_comp_poissonSubsampleKernel_le _ hγ hε) ?_
  have h := hockeyStickDiv_le_privacyProfile (M := membershipKernel v p ∘ₖ poissonSubsampleKernel γ)
    (ε := log (1 + γ * (exp ε - 1)))
    (show IsAddRemoveNeighbour (insert v ∅) ∅ from ⟨v, .inr ⟨notMem_empty v, rfl⟩⟩)
  rw [exp_log (by nlinarith [one_le_exp hε, γ.coe_nonneg]), comp_poissonSubsampleKernel_apply,
    comp_poissonSubsampleKernel_apply, sum_powerset_insert_poisson _ (notMem_empty v)] at h
  simp only [membershipKernel_apply, card_empty, pow_zero, mul_one, tsub_zero, powerset_empty,
    sum_singleton, one_smul, notMem_empty, mem_insert_self, decide_false, decide_true] at h
  rw [hockeyStickDiv_mixture_left_eq hγ (one_le_exp hε)] at h
  rwa [privacyProfile_membershipKernel hp v hε]

/-- **Theorem 13** for Theorem 9 (tightness of sampling without replacement): if some
neighbouring datasets `x ≃ₛ x'` of size `n` have `v ∈ x` and `v ∉ x'` (the hypothesis of
Lemma 12), then for the randomized membership mechanism `M_{v,p}` the bound of Theorem 9 is an
equality, `δ_{M'}(log (1 + (m / n) (e^ε - 1))) = (m / n) δ_M(ε)` for `M' = M^{S^wo_m}`, for every
`p ∈ [0, 1]`. `U` is countable here (see the module docstring); the paper allows any universe. -/
theorem privacyProfile_comp_samplingWORKernel_membershipKernel [DecidableEq U] [Countable U]
    {p : ℝ≥0} (hp : p ≤ 1) (v : U) {n m : ℕ} (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    {x x' : Finset U} (hx : IsSubstNeighbour x x') (hxn : #x = n) (hvx : v ∈ x) (hvx' : v ∉ x') :
    privacyProfile (membershipKernel v p ∘ₖ samplingWORKernel m)
        (fun x x' ↦ IsSubstNeighbour x x' ∧ #x = n) (log (1 + m / n * (exp ε - 1))) =
      m / n * privacyProfile (membershipKernel v p)
        (fun y y' ↦ IsSubstNeighbour y y' ∧ #y = m) ε := by
  have := isMarkovKernel_membershipKernel hp v
  have := isProbabilityMeasure_randResp hp
  set M := membershipKernel v p with hMdef
  refine le_antisymm (privacyProfile_comp_samplingWORKernel_le M hmn hε) ?_
  have hmn' : (0 : ℝ) ≤ m / n := by positivity
  have key : hockeyStickDiv (1 + m / n * (exp ε - 1)) ((M ∘ₖ samplingWORKernel m) x)
      ((M ∘ₖ samplingWORKernel m) x') =
        m / n * hockeyStickDiv (exp ε) (randResp p true) (randResp p false) := by
    obtain ⟨x₀, w, w', hw, hw', hne, rfl, rfl⟩ := hx
    obtain rfl : v = w := by
      rcases mem_insert.1 hvx with h | h
      · exact h
      · exact absurd (mem_insert_of_mem h) hvx'
    have hM₀ {y : Finset U} (hy : y ⊆ x₀) : M y = randResp p false := by
      have : v ∉ y := fun h ↦ hw (hy h)
      simp [hMdef, membershipKernel_apply, this]
    have hM₁ (y : Finset U) : M (insert v y) = randResp p true := by
      simp [hMdef, membershipKernel_apply]
    have hM₀' {y : Finset U} (hy : y ⊆ x₀) : M (insert w' y) = randResp p false := by
      have : v ∉ y := fun h ↦ hw (hy h)
      simp [hMdef, membershipKernel_apply, hne, this]
    rw [card_insert_of_notMem hw] at hxn
    subst hxn
    rw [comp_samplingWORKernel_apply, comp_samplingWORKernel_apply, card_insert_of_notMem hw,
      card_insert_of_notMem hw']
    rcases Nat.eq_zero_or_pos m with rfl | hm₀
    · simp only [powersetCard_zero, sum_singleton, CharP.cast_eq_zero, zero_div, zero_mul,
        add_zero]
      rw [hockeyStickDiv_self le_rfl]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rcases Nat.lt_or_eq_of_le hmn with hlt | heq
    swap
    · -- `m = n`: the subsample is the whole dataset
      have hk : k = #x₀ := by omega
      subst hk
      have hself {u : U} (hu : u ∉ x₀) :
          (insert u x₀).powersetCard (#x₀ + 1) = {insert u x₀} := by
        rw [← card_insert_of_notMem hu, powersetCard_self]
      have h1 : ((#x₀ + 1 : ℕ) : ℝ) / ((#x₀ + 1 : ℕ) : ℝ) = 1 := div_self (by positivity)
      rw [hself hw, hself hw', sum_singleton, sum_singleton, Nat.choose_self, Nat.cast_one,
        inv_one, one_smul, one_smul, h1, one_mul, one_mul, add_sub_cancel, hM₁,
        hM₀' subset_rfl]
    -- `0 < m < n`
    have hkN : k < #x₀ := by omega
    set η : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0) / ((#x₀ + 1 : ℕ) : ℝ≥0) with hηdef
    have hη : η ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hmn) zero_le
    have hηℝ : (η : ℝ) = ((k + 1 : ℕ) : ℝ) / ((#x₀ + 1 : ℕ) : ℝ) := by
      rw [hηdef, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    have havg {j : ℕ} (hj : j ≤ #x₀) (ρ : Measure Bool) :
        ((#x₀).choose j : ℝ≥0)⁻¹ • ∑ _y ∈ x₀.powersetCard j, ρ = ρ := by
      rw [sum_const, card_powersetCard, ← Nat.cast_smul_eq_nsmul ℝ≥0, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast (Nat.choose_pos hj).ne'), one_smul]
    have hS : ∑ y ∈ x₀.powersetCard (k + 1), M y = ∑ _y ∈ x₀.powersetCard (k + 1),
        randResp p false := sum_congr rfl fun y hy ↦ hM₀ (mem_powersetCard.1 hy).1
    have hB : ∑ y ∈ x₀.powersetCard k, M (insert v y) = ∑ _y ∈ x₀.powersetCard k,
        randResp p true := sum_congr rfl fun y _ ↦ hM₁ y
    have hB' : ∑ y ∈ x₀.powersetCard k, M (insert w' y) = ∑ _y ∈ x₀.powersetCard k,
        randResp p false := sum_congr rfl fun y hy ↦ hM₀' (mem_powersetCard.1 hy).1
    rw [sum_powersetCard_insert_eq_mixture _ hw hkN, sum_powersetCard_insert_eq_mixture _ hw' hkN,
      hS, hB, hB', havg hkN, havg hkN.le, havg hkN.le, one_sub_smul_add_smul_self hη, ← hηℝ]
    exact hockeyStickDiv_mixture_left_eq hη (one_le_exp hε)
  have h := hockeyStickDiv_le_privacyProfile (M := M ∘ₖ samplingWORKernel m)
    (ε := log (1 + m / n * (exp ε - 1))) (Adj := fun x x' ↦ IsSubstNeighbour x x' ∧ #x = n)
    ⟨hx, hxn⟩
  rw [exp_log (by nlinarith [one_le_exp hε]), key] at h
  exact (mul_le_mul_of_nonneg_left (privacyProfile_membershipKernel_le hp v _ hε) hmn').trans h

end InformationTheory
