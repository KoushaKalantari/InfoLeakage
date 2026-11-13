/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.OptimalComposition.Composition
public import InfoLeakage.AdvancedComposition.Basic

/-!
# The optimal composition theorem under adaptive composition

This file proves Theorem 3.3 (the optimal composition theorem) of

* P. Kairouz, S. Oh and P. Viswanath, *The composition theorem for differential privacy*,
  ICML 2015 / IEEE Trans. Inf. Theory 63(6), 2017
  ([arXiv:1311.0776](https://arxiv.org/abs/1311.0776)); result, section, equation and page
  numbers follow arXiv v4 (6 Dec 2015),

for `k`-fold **adaptive** composition with a finite output alphabet `Y`, in the form
`AdvancedComposition.adaptiveCompose` of `InfoLeakage.AdvancedComposition.Basic`: round `n`
runs a mechanism `M n : Kernel (𝒟 × (Fin n → Y)) Y` that sees the dataset and the outputs of the
earlier rounds. As there, the neighbouring relation `Adj` is fixed and the adversary's adaptive
choices enter only through the history. The composition experiment of Section 3 with a
**deterministic** adversary is the case `𝒟 = Bool`, `Adj = (· ≠ ·)`, with `M n (b, x)` the output
distribution, on `D_{n,b}`, of the mechanism chosen in round `n` after history `x`; all rounds
share one finite output alphabet (rounds with different output spaces can be embedded in a sum
type). The adversary's internal randomness `R`, part of its view `V^b`, is not modelled; a
randomized adversary reduces to deterministic ones by mixing over `R`, an argument that is not
formalized here.

The proof is that of Section 6.2: in every round and for every history the pair of output
distributions is a post-processing of the canonical pair
(`exists_kernel_comp_canonicalMechanism_iff`), and chaining these post-processings along the
history gives a stochastic matrix from `Fin k → Fin 4` to `Fin k → Y` that carries
`(P̃₀^k, P̃₁^k)` to the two output distributions of the adaptive composition (this
replaces the Markov chain argument (20)–(22) of the paper).

## Main statements (paper result → Lean name)

* Section 6.2 (converse) for adaptive composition, for every slope `γ`:
  `hockeyStickDiv_adaptiveCompose_le`; privacy-profile form:
  `isEpsDeltaDP_adaptiveCompose_hockeyStickDiv`.
* Theorem 3.3: `isEpsDeltaDP_adaptiveCompose_compositionDelta`; tightness, by the adaptive
  composition that runs the canonical mechanism in every round:
  `not_isEpsDeltaDP_adaptiveCompose_canonicalMechanism` (its rounds are `(ε, δ)`-DP by
  `isEpsDeltaDP_sectL_comap_canonicalMechanism`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

namespace OptimalComposition

open AdvancedComposition

variable {𝒟 Y : Type*} [MeasurableSpace 𝒟] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- The `k`-fold adaptive composition gives an output tuple `y` the probability
`∏_{n < k} M_n(S, (y₀, …, y_{n-1}))(y_n)`. -/
private lemma adaptiveCompose_apply_singleton
    (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y) [∀ n, IsMarkovKernel (M n)] (k : ℕ) (S : 𝒟)
    (y : Fin k → Y) :
    adaptiveCompose M k S {y} =
      ∏ n : Fin k, M n (S, fun j : Fin n ↦ y (Fin.castLE n.isLt.le j)) {y n} := by
  induction k with
  | zero =>
    rw [adaptiveCompose_zero, Kernel.const_apply,
      Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 (Subsingleton.elim _ _))]
    simp
  | succ k ih =>
    have hpre : (fun p : (Fin k → Y) × Y ↦ (Fin.snoc p.1 p.2 : Fin (k + 1) → Y)) ⁻¹' {y} =
        {Fin.init y} ×ˢ {y (Fin.last k)} := by
      ext ⟨p, z⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
      constructor
      · rintro rfl
        simp
      · rintro ⟨rfl, rfl⟩
        exact Fin.snoc_init_self y
    rw [adaptiveCompose_succ, Kernel.map_apply' _ (measurable_snoc k) _
      (measurableSet_singleton y), hpre, Kernel.compProd_apply_prod (measurableSet_singleton _)
      (measurableSet_singleton _), lintegral_singleton, ih, Fin.prod_univ_castSucc, mul_comm]
    rfl

/-- The real-valued form of `adaptiveCompose_apply_singleton`. -/
private lemma adaptiveCompose_real_singleton
    (M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y) [∀ n, IsMarkovKernel (M n)] (k : ℕ) (S : 𝒟)
    (y : Fin k → Y) :
    (adaptiveCompose M k S).real {y} =
      ∏ n : Fin k, (M n (S, fun j : Fin n ↦ y (Fin.castLE n.isLt.le j))).real {y n} := by
  rw [measureReal_def, adaptiveCompose_apply_singleton, ENNReal.toReal_prod]
  rfl

omit [MeasurableSpace Y] [MeasurableSingletonClass Y] in
private lemma snoc_castLE {k n : ℕ} (p : Fin k → Y) (z : Y) (hn : n ≤ k) (h : n ≤ k + 1)
    (j : Fin n) : Fin.snoc (α := fun _ ↦ Y) p z (Fin.castLE h j) = p (Fin.castLE hn j) := by
  rw [show Fin.castLE h j = Fin.castSucc (Fin.castLE hn j) from Fin.ext rfl, Fin.snoc_castSucc]

omit [MeasurableSpace Y] [MeasurableSingletonClass Y] in
/-- Chaining stochastic matrices `t n h` (indexed by the round `n` and the history `h`) along
the outputs gives a stochastic matrix from `Fin k → Fin 4` to `Fin k → Y`. -/
private lemma sum_prod_history [Fintype Y] (t : (n : ℕ) → (Fin n → Y) → Fin 4 → Y → ℝ)
    (ht : ∀ n h a, ∑ y, t n h a y = 1) (k : ℕ) (x : Fin k → Fin 4) :
    ∑ y : Fin k → Y, ∏ n : Fin k, t n (fun j : Fin n ↦ y (Fin.castLE n.isLt.le j)) (x n) (y n)
      = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.snocEquiv fun _ ↦ Y).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      snoc_castLE _ _ (Fin.is_lt _).le, snoc_castLE _ _ le_rfl, ← Finset.mul_sum, ht, mul_one]
    exact ih _

/-- Data processing on finite sums: a stochastic matrix `W` does not increase
`∑ [P - γ Q]₊`. -/
private lemma sum_max_comp_le {X Z : Type*} [Fintype X] [Fintype Z] (W : X → Z → ℝ)
    (hW : ∀ x z, 0 ≤ W x z) (hW₁ : ∀ x, ∑ z, W x z = 1) (P Q : X → ℝ) (γ : ℝ) :
    ∑ z, max 0 (∑ x, W x z * P x - γ * ∑ x, W x z * Q x) ≤ ∑ x, max 0 (P x - γ * Q x) := by
  calc _ ≤ ∑ z, ∑ x, W x z * max 0 (P x - γ * Q x) := by
        refine Finset.sum_le_sum fun z _ ↦ max_le
          (Finset.sum_nonneg fun x _ ↦ mul_nonneg (hW x z) (le_max_left _ _)) ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_le_sum fun x _ ↦ ?_
        have := mul_le_mul_of_nonneg_left (le_max_right 0 (P x - γ * Q x)) (hW x z)
        linarith
    _ = ∑ x, max 0 (P x - γ * Q x) := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, hW₁]

variable {ε δ : ℝ}

omit [MeasurableSpace Y] [MeasurableSingletonClass Y] in
private lemma pi_canonicalMechanism_real' (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (b : Bool) {k : ℕ}
    (x : Fin k → Fin 4) :
    (Measure.pi fun _ : Fin k ↦ canonicalMechanism ε δ b).real {x} =
      ∏ j, canonicalProb ε δ b (x j) := by
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun j _ ↦ canonicalMechanism_real_singleton hδ₀ hδ₁ b (x j)

/-- **Converse of the optimal composition theorem for adaptive composition** (Section 6.2 of
Kairouz–Oh–Viswanath, finite output alphabet `Y`): if, for every round `n < k` and every
history `x`, the mechanism `S ↦ M n (S, x)` is `(ε, δ)`-DP (`ε ≥ 0`, `δ ∈ [0, 1]`, symmetric
`Adj`), then for neighbours `S, S'` and every `γ`, the `k`-fold adaptive composition satisfies
`D_γ(M^k(S) ‖ M^k(S')) ≤ D_γ(P̃₀^k ‖ P̃₁^k)`. -/
theorem hockeyStickDiv_adaptiveCompose_le [Finite Y] {Adj : 𝒟 → 𝒟 → Prop} [Std.Symm Adj]
    {M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y} [∀ n, IsMarkovKernel (M n)] (hε : 0 ≤ ε)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) {k : ℕ} (h : ∀ n < k, ∀ x, IsEpsDeltaDP ((M n).sectL x) Adj ε δ)
    {S S' : 𝒟} (hS : Adj S S') (γ : ℝ) :
    hockeyStickDiv γ (adaptiveCompose M k S) (adaptiveCompose M k S') ≤
      hockeyStickDiv γ (Measure.pi fun _ : Fin k ↦ canonicalMechanism ε δ false)
        (Measure.pi fun _ : Fin k ↦ canonicalMechanism ε δ true) := by
  classical
  have := Fintype.ofFinite Y
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  have hex (n : ℕ) (hh : Fin n → Y) : ∃ T : Kernel (Fin 4) Y, IsMarkovKernel T ∧
      (n < k → T ∘ₘ canonicalMechanism ε δ false = M n (S, hh) ∧
        T ∘ₘ canonicalMechanism ε δ true = M n (S', hh)) := by
    by_cases hn : n < k
    · have hdp := isEpsDeltaDP_iff_forall_hockeyStickDiv_le.1 (h n hn hh)
      obtain ⟨T, hT, h₀, h₁⟩ := (exists_kernel_comp_canonicalMechanism_iff hε hδ₀ hδ₁).2
        ⟨hdp hS, hdp (Std.Symm.symm _ _ hS)⟩
      exact ⟨T, hT, fun _ ↦ ⟨h₀, h₁⟩⟩
    · exact ⟨Kernel.const _ (M n (S, hh)), inferInstance, fun h' ↦ absurd h' hn⟩
  choose T hT hTeq using hex
  set t : (n : ℕ) → (Fin n → Y) → Fin 4 → Y → ℝ := fun n hh a y ↦ (T n hh a).real {y}
  have ht₀ (n : ℕ) (hh : Fin n → Y) (a : Fin 4) (y : Y) : 0 ≤ t n hh a y := measureReal_nonneg
  have ht₁ (n : ℕ) (hh : Fin n → Y) (a : Fin 4) : ∑ y, t n hh a y = 1 := by simp [t]
  have hrep (b : Bool) (S₀ : 𝒟)
      (hS₀ : ∀ n < k, ∀ hh, T n hh ∘ₘ canonicalMechanism ε δ b = M n (S₀, hh))
      (y : Fin k → Y) :
      (adaptiveCompose M k S₀).real {y} = ∑ x : Fin k → Fin 4,
        (∏ n : Fin k, t n (fun j : Fin n ↦ y (Fin.castLE n.isLt.le j)) (x n) (y n)) *
          ∏ n, canonicalProb ε δ b (x n) := by
    rw [adaptiveCompose_real_singleton]
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (n : Fin k) a ↦
      t n (fun j : Fin n ↦ y (Fin.castLE n.isLt.le j)) a (y n) * canonicalProb ε δ b a)]
    refine Finset.prod_congr rfl fun n _ ↦ ?_
    rw [← hS₀ n n.isLt, measureReal_comp_singleton]
    simp only [canonicalMechanism_real_singleton hδ₀ hδ₁, t]
  rw [hockeyStickDiv_eq_sum, hockeyStickDiv_eq_sum]
  simp only [pi_canonicalMechanism_real' hδ₀ hδ₁,
    hrep false S (fun n hn hh ↦ (hTeq n hh hn).1), hrep true S' (fun n hn hh ↦ (hTeq n hh hn).2)]
  exact sum_max_comp_le _ (fun x y ↦ Finset.prod_nonneg fun n _ ↦ ht₀ _ _ _ _)
    (sum_prod_history t ht₁ k) _ _ γ

/-- **Optimal composition theorem for adaptive composition, privacy-profile form** (Theorem 3.3
of Kairouz–Oh–Viswanath as proved in Section 6.2, finite output alphabet): under the hypotheses
of `hockeyStickDiv_adaptiveCompose_le`, the `k`-fold adaptive composition is
`(ε', D_{e^ε'}(P̃₀^k ‖ P̃₁^k))`-DP for every `ε'`. -/
theorem isEpsDeltaDP_adaptiveCompose_hockeyStickDiv [Finite Y] {Adj : 𝒟 → 𝒟 → Prop}
    [Std.Symm Adj] {M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y} [∀ n, IsMarkovKernel (M n)]
    (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) {k : ℕ}
    (h : ∀ n < k, ∀ x, IsEpsDeltaDP ((M n).sectL x) Adj ε δ) (ε' : ℝ) :
    IsEpsDeltaDP (adaptiveCompose M k) Adj ε'
      (hockeyStickDiv (exp ε') (Measure.pi fun _ : Fin k ↦ canonicalMechanism ε δ false)
        (Measure.pi fun _ : Fin k ↦ canonicalMechanism ε δ true)) :=
  isEpsDeltaDP_iff_forall_hockeyStickDiv_le.2 fun _ _ hS ↦
    hockeyStickDiv_adaptiveCompose_le hε hδ₀ hδ₁ h hS _

/-- **Theorem 3.3** of Kairouz–Oh–Viswanath (the optimal composition theorem) for `k`-fold
adaptive composition with a finite output alphabet `Y`: if, for every round `n < k` and every
history `x`, the mechanism `S ↦ M n (S, x)` is `(ε, δ)`-DP for a symmetric neighbouring relation
(`ε ≥ 0`, `δ ∈ [0, 1]`), then the adaptive composition `adaptiveCompose M k` is
`((k - 2i) ε, 1 - (1 - δ)^k (1 - δ_i))`-DP for every `i` with `2i ≤ k`. The bound is attained
by the adaptive composition that runs the canonical mechanism in every round
(`not_isEpsDeltaDP_adaptiveCompose_canonicalMechanism`). -/
theorem isEpsDeltaDP_adaptiveCompose_compositionDelta [Finite Y] {Adj : 𝒟 → 𝒟 → Prop}
    [Std.Symm Adj] {M : (n : ℕ) → Kernel (𝒟 × (Fin n → Y)) Y} [∀ n, IsMarkovKernel (M n)]
    (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) {k : ℕ}
    (h : ∀ n < k, ∀ x, IsEpsDeltaDP ((M n).sectL x) Adj ε δ) {i : ℕ} (hi : 2 * i ≤ k) :
    IsEpsDeltaDP (adaptiveCompose M k) Adj ((k - 2 * i) * ε)
      (1 - (1 - δ) ^ k * (1 - compositionDelta k i ε)) := by
  have h' := hockeyStickDiv_pi_canonicalMechanism (ι := Fin k) hε hδ₀ hδ₁ (i := i)
    (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin] at h'
  rw [← h']
  exact isEpsDeltaDP_adaptiveCompose_hockeyStickDiv hε hδ₀ hδ₁ h _

omit [MeasurableSpace 𝒟] [MeasurableSpace Y] [MeasurableSingletonClass Y] in
/-- Running the canonical mechanism in round `n`, ignoring the history, gives for every history
`x` an `(ε, δ)`-DP mechanism of the hypothesis `b : Bool`. -/
theorem isEpsDeltaDP_sectL_comap_canonicalMechanism (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (x : Fin n → Fin 4) :
    IsEpsDeltaDP (((canonicalMechanism ε δ).comap (fun p : Bool × (Fin n → Fin 4) ↦ p.1)
      (measurable_fst : Measurable fun p : Bool × (Fin n → Fin 4) ↦ p.1)).sectL x)
      (fun _ _ ↦ True) ε δ :=
  isEpsDeltaDP_canonicalMechanism hε hδ₀ hδ₁

omit [MeasurableSpace 𝒟] [MeasurableSpace Y] [MeasurableSingletonClass Y] in
/-- **Tightness of Theorem 3.3 for adaptive composition** (Section 6.1 of
Kairouz–Oh–Viswanath): the adaptive composition that runs the canonical `(ε, δ)`-DP mechanism in
every round (ignoring the history), whose rounds satisfy the hypothesis of
`isEpsDeltaDP_adaptiveCompose_compositionDelta` by `isEpsDeltaDP_sectL_comap_canonicalMechanism`,
is not `((k - 2i) ε, δ')`-DP for any `δ' < 1 - (1 - δ)^k (1 - δ_i)`, `2i ≤ k`. -/
theorem not_isEpsDeltaDP_adaptiveCompose_canonicalMechanism (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ)
    (hδ₁ : δ ≤ 1) {k i : ℕ} (hi : 2 * i ≤ k) {δ' : ℝ}
    (hδ' : δ' < 1 - (1 - δ) ^ k * (1 - compositionDelta k i ε)) :
    ¬ IsEpsDeltaDP (adaptiveCompose (fun n ↦ (canonicalMechanism ε δ).comap
        (fun p : Bool × (Fin n → Fin 4) ↦ p.1)
        (measurable_fst : Measurable fun p : Bool × (Fin n → Fin 4) ↦ p.1)) k) (fun _ _ ↦ True)
      ((k - 2 * i) * ε) δ' := by
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  set M : (n : ℕ) → Kernel (Bool × (Fin n → Fin 4)) (Fin 4) := fun n ↦
    (canonicalMechanism ε δ).comap (fun p : Bool × (Fin n → Fin 4) ↦ p.1)
      (measurable_fst : Measurable fun p : Bool × (Fin n → Fin 4) ↦ p.1)
  have hpi (b : Bool) :
      adaptiveCompose M k b = Measure.pi fun _ : Fin k ↦ canonicalMechanism ε δ b := by
    refine Measure.ext_of_singleton fun y ↦ ?_
    rw [adaptiveCompose_apply_singleton, Measure.pi_singleton]
    rfl
  intro h
  have h₁ := isEpsDeltaDP_iff_forall_hockeyStickDiv_le.1 h (S := false) (S' := true) trivial
  rw [hpi, hpi] at h₁
  have h₂ := hockeyStickDiv_pi_canonicalMechanism (ι := Fin k) hε hδ₀ hδ₁ (i := i)
    (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin] at h₂
  linarith

end OptimalComposition

end InformationTheory
