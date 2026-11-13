/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.FDP.Basic
public import Mathlib.Basic.Real.Pointwise

/-!
# The hockey-stick divergence, privacy profiles and advanced joint convexity

This file formalizes the divergence tools (Sections 2 and 3) of B. Balle, G. Barthe and
M. Gaboardi, *Privacy amplification by subsampling: tight analyses via couplings and
divergences*, NeurIPS 2018 ([arXiv:1807.01647](https://arxiv.org/abs/1807.01647)); result
numbers follow arXiv v2. The amplification theorems themselves are in
`InfoLeakage.Amplification.Subsampling`.

The `α`-divergence of the paper, better known as the hockey-stick divergence (or `E_γ`), is
`D_γ(μ ‖ ν) = sup_E (μ(E) - γ ν(E))`, the supremum ranging over measurable sets. A mechanism `M`
is `(ε, δ)`-differentially private iff `D_{e^ε}(M(S) ‖ M(S')) ≤ δ` for all neighbouring `S, S'`
(Theorem 1), and its privacy profile `δ_M(ε)` is the supremum of these divergences. The key new
tool of the paper is advanced joint convexity (Theorem 2): for overlapping mixtures
`μ = (1 - η) μ₀ + η μ₁` and `μ' = (1 - η) μ₀ + η μ₁'`,
`D_{α'}(μ ‖ μ') = η D_α(μ₁ ‖ (1 - β) μ₀ + β μ₁')` with `α' = 1 + η (α - 1)`, `β = α' / α`.

**Scope.** The divergence is defined for measures on an arbitrary measurable space. The divergence
identities and inequalities (nonnegativity, monotonicity in `γ`, joint convexity, advanced joint
convexity) hold for arbitrary finite measures (the paper uses probability measures), except the
closed form `hockeyStickDiv_eq_sum` and the data-processing inequality `hockeyStickDiv_comp_le`,
which also need a finite alphabet. The unit bounds `hockeyStickDiv_le_one` and
`privacyProfile_le_one`, and the results built on them, need the probability or Markov hypotheses
they state: for finite measures they fail, e.g. `D_1(2 δ_z ‖ 0) = 2`. Mixtures are written with
`ℝ≥0` weights, `(1 - η) • μ₀ + η • μ₁` with `η ≤ 1`, and divergence orders are real numbers
`α ≥ 1`. Mechanisms are kernels `M : Kernel 𝒟 Y` and `(ε, δ)`-DP is the library's
`IsEpsDeltaDP`.

## Main definitions

* `hockeyStickDiv γ μ ν`: the hockey-stick divergence `D_γ(μ ‖ ν)` (equation (2)).
* `privacyProfile M Adj ε`: the privacy profile `δ_M(ε) = sup_{S ≃ S'} D_{e^ε}(M(S) ‖ M(S'))`
  (Section 2).

## Main statements (paper result → Lean name)

* Equation (2), the closed form on a finite alphabet: `hockeyStickDiv_eq_sum`.
* Theorem 1 (Barthe–Olmedo): `isEpsDeltaDP_iff_forall_hockeyStickDiv_le`; in privacy-profile
  form `isEpsDeltaDP_iff_privacyProfile_le` and `isEpsDeltaDP_privacyProfile`.
* Properties (i)–(iii) of Section 3: `hockeyStickDiv_nonneg`, `hockeyStickDiv_le_one`,
  `antitone_hockeyStickDiv`, and joint convexity for finite mixtures
  `hockeyStickDiv_sum_smul_le` (with subadditivity `hockeyStickDiv_add_le`,
  `hockeyStickDiv_sum_le` and homogeneity `hockeyStickDiv_smul`).
* Theorem 2 (advanced joint convexity): `hockeyStickDiv_mixture_eq`; the inequality following
  it, i.e. equation (3): `hockeyStickDiv_mixture_le_add`, and its consequence
  `hockeyStickDiv_mixture_le` (`D_α(μ₁ ‖ μ₀), D_α(μ₁ ‖ μ₁') ≤ δ` imply `D_{α'}(μ ‖ μ') ≤ η δ`)
  on which all amplification bounds rest; the equality case `μ₁' = μ₀` used in the proof of
  Lemma 12: `hockeyStickDiv_mixture_left_eq`.

## Auxiliary results (not stated in the paper)

* Data-processing inequality for Markov kernels out of a finite alphabet: `hockeyStickDiv_comp_le`.

## Not formalized

* Equation (2) beyond finite alphabets: its middle term `∫ [dμ/dμ' - α]₊ dμ'` (Radon–Nikodym
  form) and its last equality for discrete (countably infinite) `Z`.
* Equation (5) (joint convexity along a coupling, bounded by group-privacy profiles); the
  amplification proofs use the finite-mixture form `hockeyStickDiv_sum_smul_le` instead.

* The claim that `D_α(μ ‖ μ') → 0` as `α → ∞` iff `supp μ ⊆ supp μ'` (Section 3), the maximal
  coupling construction, group-privacy profiles, and Theorems 3–7 (Laplace and Gaussian privacy
  profiles, privacy loss random variables, moment generating functions, and distance-compatible
  couplings; the couplings used by the amplification proofs are written out as finite sums in
  `InfoLeakage.Amplification.Subsampling`).
* The data-processing inequality for kernels out of a general measurable space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

namespace InformationTheory

variable {Y Z 𝒟 ι : Type*} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
  {m𝒟 : MeasurableSpace 𝒟}

/-- The **hockey-stick divergence** `D_γ(μ ‖ ν) = sup_E (μ(E) - γ ν(E))`, the supremum ranging
over the measurable sets `E` (equation (2) of Balle–Barthe–Gaboardi, where it is called the
`α`-divergence; it is also known as the elementary divergence or `E_γ`). It is meaningful for
finite measures `μ, ν` (for which the family is bounded above); the paper uses `γ ≥ 1`. -/
noncomputable def hockeyStickDiv (γ : ℝ) (μ ν : Measure Z) : ℝ :=
  ⨆ E : {E : Set Z // MeasurableSet E}, (μ.real E - γ * ν.real E)

section Basic

variable {γ γ' c : ℝ} {μ ν μ₁ μ₂ ν₁ ν₂ : Measure Z}

private lemma bddAbove_hockeyStick [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove (range fun E : {E : Set Z // MeasurableSet E} ↦ μ.real E - γ * ν.real E) := by
  refine ⟨μ.real univ + |γ| * ν.real univ, forall_mem_range.2 fun E ↦ ?_⟩
  have h₁ : μ.real E ≤ μ.real univ := measureReal_mono (subset_univ _)
  have h₂ : ν.real E ≤ ν.real univ := measureReal_mono (subset_univ _)
  have h₃ : 0 ≤ ν.real E := measureReal_nonneg
  nlinarith [neg_abs_le γ, abs_nonneg γ]

/-- To bound `D_γ(μ ‖ ν)` above it suffices to bound `μ(E) - γ ν(E)` for measurable `E`. -/
lemma hockeyStickDiv_le_of_forall (h : ∀ E, MeasurableSet E → μ.real E - γ * ν.real E ≤ c) :
    hockeyStickDiv γ μ ν ≤ c :=
  have : Nonempty {E : Set Z // MeasurableSet E} := ⟨⟨∅, .empty⟩⟩
  ciSup_le fun E ↦ h E.1 E.2

/-- Every measurable set witnesses a lower bound on the hockey-stick divergence. -/
lemma sub_le_hockeyStickDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] {E : Set Z}
    (hE : MeasurableSet E) : μ.real E - γ * ν.real E ≤ hockeyStickDiv γ μ ν :=
  le_ciSup (f := fun E : {E : Set Z // MeasurableSet E} ↦ μ.real E - γ * ν.real E)
    bddAbove_hockeyStick ⟨E, hE⟩

/-- `D_γ(μ ‖ ν) ≤ c` iff `μ(E) ≤ γ ν(E) + c` for every measurable `E`. -/
lemma hockeyStickDiv_le_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hockeyStickDiv γ μ ν ≤ c ↔ ∀ E, MeasurableSet E → μ.real E - γ * ν.real E ≤ c :=
  ⟨fun h _ hE ↦ (sub_le_hockeyStickDiv hE).trans h, hockeyStickDiv_le_of_forall⟩

/-- Property (i) of Section 3: the hockey-stick divergence is nonnegative. -/
lemma hockeyStickDiv_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ hockeyStickDiv γ μ ν := by
  simpa using sub_le_hockeyStickDiv (γ := γ) (μ := μ) (ν := ν) MeasurableSet.empty

/-- For `γ ≥ 0`, `D_γ(μ ‖ ν) ≤ μ(Z)`. -/
lemma hockeyStickDiv_le_measureReal_univ (hγ : 0 ≤ γ) [IsFiniteMeasure μ] :
    hockeyStickDiv γ μ ν ≤ μ.real univ :=
  hockeyStickDiv_le_of_forall fun E _ ↦ by
    nlinarith [measureReal_mono (μ := μ) (subset_univ E), measureReal_nonneg (μ := ν) (s := E)]

/-- Property (i) of Section 3: for a probability measure `μ` and `γ ≥ 0`, `D_γ(μ ‖ ν) ≤ 1`. -/
lemma hockeyStickDiv_le_one (hγ : 0 ≤ γ) [IsProbabilityMeasure μ] : hockeyStickDiv γ μ ν ≤ 1 := by
  simpa using hockeyStickDiv_le_measureReal_univ (ν := ν) hγ (μ := μ)

/-- Property (ii) of Section 3: `γ ↦ D_γ(μ ‖ ν)` is antitone. -/
lemma antitone_hockeyStickDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Antitone fun γ ↦ hockeyStickDiv γ μ ν := fun γ γ' h ↦
  hockeyStickDiv_le_of_forall fun E hE ↦ (by nlinarith [measureReal_nonneg (μ := ν) (s := E)] :
    μ.real E - γ' * ν.real E ≤ μ.real E - γ * ν.real E).trans (sub_le_hockeyStickDiv hE)

/-- For `γ ≥ 1`, `D_γ(μ ‖ μ) = 0`. -/
lemma hockeyStickDiv_self (hγ : 1 ≤ γ) [IsFiniteMeasure μ] : hockeyStickDiv γ μ μ = 0 :=
  le_antisymm (hockeyStickDiv_le_of_forall fun E _ ↦ by
    nlinarith [measureReal_nonneg (μ := μ) (s := E)]) hockeyStickDiv_nonneg

@[simp]
lemma hockeyStickDiv_zero_zero : hockeyStickDiv γ (0 : Measure Z) 0 = 0 := by
  simp [hockeyStickDiv]

/-- The hockey-stick divergence is positively homogeneous. -/
lemma hockeyStickDiv_smul (a : ℝ≥0) (μ ν : Measure Z) :
    hockeyStickDiv γ (a • μ) (a • ν) = a * hockeyStickDiv γ μ ν := by
  rw [hockeyStickDiv, hockeyStickDiv, Real.mul_iSup_of_nonneg a.coe_nonneg]
  congr 1 with E
  simp only [measureReal_nnreal_smul_apply]
  ring

/-- The real-valued measure of a finite sum of finite measures. -/
lemma Amplification.measureReal_finsetSum (s : Finset ι) (μ : ι → Measure Z)
    [∀ i, IsFiniteMeasure (μ i)] (E : Set Z) : (∑ i ∈ s, μ i).real E = ∑ i ∈ s, (μ i).real E := by
  simp [measureReal_def, ENNReal.toReal_sum]

open Amplification in
/-- The hockey-stick divergence is subadditive along finite sums of measures. -/
lemma hockeyStickDiv_sum_le (s : Finset ι) (μ ν : ι → Measure Z) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] :
    hockeyStickDiv γ (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, hockeyStickDiv γ (μ i) (ν i) :=
  hockeyStickDiv_le_of_forall fun E hE ↦ by
    rw [measureReal_finsetSum, measureReal_finsetSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ ↦ sub_le_hockeyStickDiv hE

/-- The hockey-stick divergence is subadditive. -/
lemma hockeyStickDiv_add_le [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] :
    hockeyStickDiv γ (μ₁ + μ₂) (ν₁ + ν₂) ≤ hockeyStickDiv γ μ₁ ν₁ + hockeyStickDiv γ μ₂ ν₂ :=
  hockeyStickDiv_le_of_forall fun E hE ↦ by
    rw [measureReal_add_apply, measureReal_add_apply]
    linarith [sub_le_hockeyStickDiv (γ := γ) (μ := μ₁) (ν := ν₁) hE,
      sub_le_hockeyStickDiv (γ := γ) (μ := μ₂) (ν := ν₂) hE]

/-- **Joint convexity** of the hockey-stick divergence (property (iii) of Section 3), for finite
mixtures with arbitrary nonnegative weights. -/
theorem hockeyStickDiv_sum_smul_le (s : Finset ι) (w : ι → ℝ≥0) (μ ν : ι → Measure Z)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    hockeyStickDiv γ (∑ i ∈ s, w i • μ i) (∑ i ∈ s, w i • ν i) ≤
      ∑ i ∈ s, w i * hockeyStickDiv γ (μ i) (ν i) :=
  (hockeyStickDiv_sum_le s _ _).trans_eq <| Finset.sum_congr rfl fun _ _ ↦ hockeyStickDiv_smul ..

/-- On a finite alphabet the hockey-stick divergence is the sum of the positive parts
`D_γ(μ ‖ ν) = ∑_z [μ{z} - γ ν{z}]₊` (the last equality of equation (2)). -/
theorem hockeyStickDiv_eq_sum [Fintype Z] [MeasurableSingletonClass Z] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : hockeyStickDiv γ μ ν = ∑ z, max 0 (μ.real {z} - γ * ν.real {z}) := by
  classical
  have hsum (s : Finset Z) : μ.real s - γ * ν.real s = ∑ z ∈ s, (μ.real {z} - γ * ν.real {z}) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_measureReal_singleton,
      sum_measureReal_singleton]
  refine le_antisymm (hockeyStickDiv_le_of_forall fun E _ ↦ ?_) ?_
  · rw [← coe_toFinset E, hsum]
    exact (Finset.sum_le_sum fun z _ ↦ le_max_right _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ le_max_left _ _)
  · set F := Finset.univ.filter fun z ↦ 0 ≤ μ.real {z} - γ * ν.real {z}
    calc ∑ z, max 0 (μ.real {z} - γ * ν.real {z}) = μ.real F - γ * ν.real F := by
          rw [hsum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          split_ifs with h
          · exact max_eq_right h
          · exact max_eq_left (not_le.1 h).le
      _ ≤ hockeyStickDiv γ μ ν := sub_le_hockeyStickDiv F.measurableSet

/-- **Data-processing inequality** for the hockey-stick divergence, for a Markov kernel out of a
finite alphabet: `D_γ(κ ∘ μ ‖ κ ∘ ν) ≤ D_γ(μ ‖ ν)`. -/
theorem hockeyStickDiv_comp_le [Finite Y] [MeasurableSingletonClass Y] (κ : Kernel Y Z)
    [IsMarkovKernel κ] (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hockeyStickDiv γ (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ hockeyStickDiv γ μ ν := by
  have := Fintype.ofFinite Y
  have key (ρ : Measure Y) [IsFiniteMeasure ρ] {E : Set Z} (hE : MeasurableSet E) :
      (κ ∘ₘ ρ).real E = ∑ y, ρ.real {y} * (κ y).real E := by
    rw [measureReal_def, Measure.bind_apply hE κ.aemeasurable, lintegral_fintype,
      ENNReal.toReal_sum fun y _ ↦ by finiteness]
    simp [measureReal_def, mul_comm]
  rw [hockeyStickDiv_eq_sum (μ := μ) (ν := ν)]
  refine hockeyStickDiv_le_of_forall fun E hE ↦ ?_
  rw [key μ hE, key ν hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  have h₀ : 0 ≤ (κ y).real E := measureReal_nonneg
  have h₁ : (κ y).real E ≤ 1 := measureReal_le_one
  nlinarith [le_max_left 0 (μ.real {y} - γ * ν.real {y}),
    le_max_right 0 (μ.real {y} - γ * ν.real {y})]

end Basic

/-! ### `(ε, δ)`-differential privacy and privacy profiles -/

section DP

variable {M : Kernel 𝒟 Y} {Adj : 𝒟 → 𝒟 → Prop} {ε δ : ℝ}

/-- **Theorem 1** (Barthe–Olmedo): a mechanism is `(ε, δ)`-differentially private iff
`D_{e^ε}(M(S) ‖ M(S')) ≤ δ` for all neighbouring `S, S'`. Here `IsEpsDeltaDP` quantifies over all
sets, not only measurable ones; the two agree since `D` only sees measurable sets and the outer
measure of `E` is attained by `toMeasurable`. -/
theorem isEpsDeltaDP_iff_forall_hockeyStickDiv_le [IsFiniteKernel M] :
    IsEpsDeltaDP M Adj ε δ ↔ ∀ ⦃S S'⦄, Adj S S' → hockeyStickDiv (exp ε) (M S) (M S') ≤ δ := by
  refine ⟨fun h S S' hS ↦ hockeyStickDiv_le_of_forall fun E _ ↦ by linarith [h hS E],
    fun h S S' hS E ↦ ?_⟩
  have h₁ : (M S).real E ≤ (M S).real (toMeasurable (M S') E) :=
    measureReal_mono (subset_toMeasurable _ _)
  have h₂ : (M S').real (toMeasurable (M S') E) = (M S').real E := by
    simp [measureReal_def, measure_toMeasurable]
  have h₃ := sub_le_hockeyStickDiv (γ := exp ε) (μ := M S) (ν := M S')
    (measurableSet_toMeasurable (M S') E)
  rw [h₂] at h₃
  linarith [h hS]

/-- The **privacy profile** `δ_M(ε) = sup_{S ≃ S'} D_{e^ε}(M(S) ‖ M(S'))` of a mechanism `M`
with respect to a neighbouring relation `Adj` (Section 2). If no two datasets are neighbours it is
`0`. -/
noncomputable def privacyProfile (M : Kernel 𝒟 Y) (Adj : 𝒟 → 𝒟 → Prop) (ε : ℝ) : ℝ :=
  ⨆ p : {p : 𝒟 × 𝒟 // Adj p.1 p.2}, hockeyStickDiv (exp ε) (M p.1.1) (M p.1.2)

/-- Each neighbouring pair contributes to the privacy profile. -/
lemma hockeyStickDiv_le_privacyProfile [IsFiniteKernel M] {S S' : 𝒟} (hS : Adj S S') :
    hockeyStickDiv (exp ε) (M S) (M S') ≤ privacyProfile M Adj ε :=
  le_ciSup (f := fun p : {p : 𝒟 × 𝒟 // Adj p.1 p.2} ↦ hockeyStickDiv (exp ε) (M p.1.1) (M p.1.2))
    ⟨M.bound.toReal, forall_mem_range.2 fun _ ↦ (hockeyStickDiv_le_measureReal_univ
      (exp_pos ε).le).trans (ENNReal.toReal_mono M.bound_ne_top (M.measure_le_bound _ _))⟩
    ⟨(S, S'), hS⟩

/-- The privacy profile is nonnegative. -/
lemma privacyProfile_nonneg [IsFiniteKernel M] : 0 ≤ privacyProfile M Adj ε :=
  Real.iSup_nonneg fun _ ↦ hockeyStickDiv_nonneg

/-- The privacy profile of a Markov kernel is at most `1`. -/
lemma privacyProfile_le_one [IsMarkovKernel M] : privacyProfile M Adj ε ≤ 1 :=
  Real.iSup_le (fun _ ↦ hockeyStickDiv_le_one (exp_pos ε).le) zero_le_one

/-- **Theorem 1** in privacy-profile form: for `δ ≥ 0`, a mechanism is `(ε, δ)`-differentially
private iff its privacy profile satisfies `δ_M(ε) ≤ δ`. -/
theorem isEpsDeltaDP_iff_privacyProfile_le [IsMarkovKernel M] (hδ : 0 ≤ δ) :
    IsEpsDeltaDP M Adj ε δ ↔ privacyProfile M Adj ε ≤ δ := by
  rw [isEpsDeltaDP_iff_forall_hockeyStickDiv_le]
  exact ⟨fun h ↦ Real.iSup_le (fun p ↦ h p.2) hδ,
    fun h S S' hS ↦ (hockeyStickDiv_le_privacyProfile hS).trans h⟩

/-- Every mechanism is `(ε, δ_M(ε))`-differentially private. -/
theorem isEpsDeltaDP_privacyProfile [IsMarkovKernel M] :
    IsEpsDeltaDP M Adj ε (privacyProfile M Adj ε) :=
  (isEpsDeltaDP_iff_privacyProfile_le privacyProfile_nonneg).2 le_rfl

end DP

/-! ### Advanced joint convexity -/

section AdvancedJointConvexity

variable {μ₀ μ₁ μ₁' : Measure Z} [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₁']
  {η β : ℝ≥0} {α : ℝ}

/-- The weight `β = α' / α ∈ [0, 1]` of advanced joint convexity. -/
lemma Amplification.exists_beta (hη : η ≤ 1) (hα : 1 ≤ α) :
    ∃ β : ℝ≥0, (β : ℝ) = (1 + η * (α - 1)) / α ∧ β ≤ 1 := by
  have hnn : 0 ≤ (1 + η * (α - 1)) / α := div_nonneg (by nlinarith [η.coe_nonneg]) (by linarith)
  refine ⟨((1 + η * (α - 1)) / α).toNNReal, Real.coe_toNNReal _ hnn, ?_⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_one, Real.coe_toNNReal _ hnn, div_le_one (by positivity)]
  nlinarith [show (η : ℝ) ≤ 1 from hη]

/-- The weight `β = α' / α` of advanced joint convexity is at most `1`. -/
lemma Amplification.beta_le_one (hη : η ≤ 1) (hα : 1 ≤ α)
    (hβ : (β : ℝ) = (1 + η * (α - 1)) / α) : β ≤ 1 := by
  obtain ⟨β', hβ', h⟩ := Amplification.exists_beta hη hα
  exact (NNReal.coe_injective (hβ.trans hβ'.symm)).le.trans h

/-- A measure is the trivial mixture of itself with itself. -/
lemma Amplification.one_sub_smul_add_smul_self {t : ℝ≥0} (ht : t ≤ 1) (μ : Measure Z) :
    (1 - t) • μ + t • μ = μ := by
  rw [← add_smul, tsub_add_cancel_of_le ht, one_smul]

open Amplification

/-- **Theorem 2** (advanced joint convexity): for overlapping mixtures
`μ = (1 - η) μ₀ + η μ₁` and `μ' = (1 - η) μ₀ + η μ₁'`, `α ≥ 1`, `α' = 1 + η (α - 1)` and
`β = α' / α`, we have `D_{α'}(μ ‖ μ') = η D_α(μ₁ ‖ (1 - β) μ₀ + β μ₁')`. The measures need only be
finite. -/
theorem hockeyStickDiv_mixture_eq (hη : η ≤ 1) (hα : 1 ≤ α)
    (hβ : (β : ℝ) = (1 + η * (α - 1)) / α) :
    hockeyStickDiv (1 + η * (α - 1)) ((1 - η) • μ₀ + η • μ₁) ((1 - η) • μ₀ + η • μ₁') =
      η * hockeyStickDiv α μ₁ ((1 - β) • μ₀ + β • μ₁') := by
  have hα₀ : α ≠ 0 := by positivity
  have hβ₁ := beta_le_one hη hα hβ
  rw [hockeyStickDiv, hockeyStickDiv, Real.mul_iSup_of_nonneg η.coe_nonneg]
  congr 1 with E
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply, NNReal.coe_sub hη, NNReal.coe_sub hβ₁, NNReal.coe_one,
    hβ]
  field_simp
  ring

/-- Advanced joint convexity followed by ordinary joint convexity (the inequality after
Theorem 2, and equation (3)):
`D_{α'}(μ ‖ μ') ≤ η ((1 - β) D_α(μ₁ ‖ μ₀) + β D_α(μ₁ ‖ μ₁'))`. -/
theorem hockeyStickDiv_mixture_le_add (hη : η ≤ 1) (hα : 1 ≤ α)
    (hβ : (β : ℝ) = (1 + η * (α - 1)) / α) :
    hockeyStickDiv (1 + η * (α - 1)) ((1 - η) • μ₀ + η • μ₁) ((1 - η) • μ₀ + η • μ₁') ≤
      η * ((1 - β) * hockeyStickDiv α μ₁ μ₀ + β * hockeyStickDiv α μ₁ μ₁') := by
  have hβ₁ := beta_le_one hη hα hβ
  rw [hockeyStickDiv_mixture_eq hη hα hβ]
  refine mul_le_mul_of_nonneg_left ?_ η.coe_nonneg
  calc hockeyStickDiv α μ₁ ((1 - β) • μ₀ + β • μ₁')
      = hockeyStickDiv α ((1 - β) • μ₁ + β • μ₁) ((1 - β) • μ₀ + β • μ₁') := by
        rw [one_sub_smul_add_smul_self hβ₁]
    _ ≤ hockeyStickDiv α ((1 - β) • μ₁) ((1 - β) • μ₀) + hockeyStickDiv α (β • μ₁) (β • μ₁') :=
      hockeyStickDiv_add_le
    _ = _ := by rw [hockeyStickDiv_smul, hockeyStickDiv_smul, NNReal.coe_sub hβ₁, NNReal.coe_one]

/-- The amplification step of the paper's method: if `D_α(μ₁ ‖ μ₀) ≤ δ` and `D_α(μ₁ ‖ μ₁') ≤ δ`,
then the overlapping mixtures satisfy `D_{1 + η (α - 1)}(μ ‖ μ') ≤ η δ`. -/
theorem hockeyStickDiv_mixture_le (hη : η ≤ 1) (hα : 1 ≤ α) {δ : ℝ}
    (h₀ : hockeyStickDiv α μ₁ μ₀ ≤ δ) (h₁ : hockeyStickDiv α μ₁ μ₁' ≤ δ) :
    hockeyStickDiv (1 + η * (α - 1)) ((1 - η) • μ₀ + η • μ₁) ((1 - η) • μ₀ + η • μ₁') ≤
      η * δ := by
  obtain ⟨β, hβ, hβ₁⟩ := exists_beta hη hα
  refine (hockeyStickDiv_mixture_le_add hη hα hβ).trans
    (mul_le_mul_of_nonneg_left ?_ η.coe_nonneg)
  have : (β : ℝ) ≤ 1 := hβ₁
  nlinarith [β.coe_nonneg]

/-- Advanced joint convexity when one of the two mixtures is its own base, `μ' = μ₀`:
`D_{1 + η (α - 1)}((1 - η) μ₀ + η μ₁ ‖ μ₀) = η D_α(μ₁ ‖ μ₀)`. This is the equality case used for
the lower bounds of Section 5 (proof of Lemma 12). -/
theorem hockeyStickDiv_mixture_left_eq (hη : η ≤ 1) (hα : 1 ≤ α) :
    hockeyStickDiv (1 + η * (α - 1)) ((1 - η) • μ₀ + η • μ₁) μ₀ =
      η * hockeyStickDiv α μ₁ μ₀ := by
  obtain ⟨β, hβ, hβ₁⟩ := exists_beta hη hα
  have h := hockeyStickDiv_mixture_eq (μ₀ := μ₀) (μ₁ := μ₁) (μ₁' := μ₀) hη hα hβ
  rwa [one_sub_smul_add_smul_self hη, one_sub_smul_add_smul_self hβ₁] at h

end AdvancedJointConvexity

end InformationTheory
