/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.OptimalComposition.Basic
public import InfoLeakage.ZCDP.Basic

/-!
# The optimal composition theorem for differential privacy

This file formalizes the optimal composition theorem of

* P. Kairouz, S. Oh and P. Viswanath, *The composition theorem for differential privacy*,
  ICML 2015 / IEEE Trans. Inf. Theory 63(6), 2017
  ([arXiv:1311.0776](https://arxiv.org/abs/1311.0776)); result, section, equation and page
  numbers follow arXiv v4 (6 Dec 2015),

for the **non-adaptive** composition of `k` mechanisms with finite output alphabets: the
mechanisms `M i : Kernel 𝒟 (Y i)`, `i : ι` with `|ι| = k`, run independently on the same
dataset, `S ↦ ∏ i, M i S` (`ZCDP.piKernel`). The adaptive form of the paper's Theorem 3.3 is
in `InfoLeakage.OptimalComposition.Adaptive`; the closed form `δ_i` and the tightness
statements proved here are used there.

The proof follows Section 6. Every `(ε, δ)`-DP pair is a post-processing of the canonical pair
`(P̃₀, P̃₁)` (`exists_kernel_comp_canonicalMechanism_iff`, from
`InfoLeakage.OptimalComposition.Basic`); running these post-processings coordinatewise shows that
the product of `k` such pairs is a post-processing of `(P̃₀^k, P̃₁^k)`, so by data processing the
`k`-fold composition is `(ε', D_{e^ε'}(P̃₀^k ‖ P̃₁^k))`-DP for every `ε'`, and the canonical
composition attains this. At `ε' = (k - 2i) ε` the hockey-stick divergence of the canonical
composition is computed in closed form by sorting the `4^k` outcomes by their number of
coordinates equal to `0`, `3` and `2`.

## Main definitions

* `OptimalComposition.compositionDelta k i ε`: the quantity `δ_i` of equation (6).

## Main statements (paper result → Lean name)

* Section 6.2 (converse), pairwise and for every slope: `hockeyStickDiv_pi_le`; for mechanisms,
  the exact privacy profile of `k`-fold composition: `isEpsDeltaDP_piKernel_hockeyStickDiv`,
  attained by the canonical mechanism: `not_isEpsDeltaDP_piKernel_canonicalMechanism`.
* Section 6.1 (achievability), the display
  `d_{(k-2i)ε}(P̃₀^k, P̃₁^k) = 1 - (1 - δ)^k (1 - δ_i)`: `hockeyStickDiv_pi_canonicalMechanism`.
* Theorem 3.3 (non-adaptive composition, finite alphabets):
  `isEpsDeltaDP_piKernel_compositionDelta`, with tightness
  `not_isEpsDeltaDP_piKernel_canonicalMechanism_compositionDelta`.

## Not formalized

* The heterogeneous case (Section 3.3, Theorem 3.5), the simplified bounds of Theorem 3.4, and
  Sections 4–5.
* That the privacy region of the composition is the intersection of the `⌊k/2⌋ + 1` regions of
  Theorem 3.3 (this uses Remark 6.1); `isEpsDeltaDP_piKernel_hockeyStickDiv` gives instead the
  optimal `δ` for every `ε'`.

## Notes on the paper

* Section 6.1 (p. 17): the product formula is printed as
  `P(X^{1,b} = x₁, …, X^{k,b} = x_k) = ∏_{x=1}^k P̃_b(x_i)`; the product index should be `i`.
* Section 6.1: `E` is defined (p. 16) as a set of exponents `ε̃`, but the composed set is listed
  (p. 17) as `{e^{(k-2⌊k/2⌋)ε}, …, e^{kε}}`; the exponentials should be removed, giving
  `{(k - 2⌊k/2⌋) ε, …, k ε}`. (Identifying this corrected set with the literal `E` of p. 16
  further requires excluding the outcomes where both composed distributions vanish, and treating
  `δ = 1` separately.) Neither slip affects the stated results.
* After Theorem 3.3 (p. 7): "the privacy region of `k`-fold composition is an intersection of
  `k` regions"; the intersection is over `i ∈ {0, …, ⌊k/2⌋}`, i.e. of `⌊k/2⌋ + 1` regions.
* Section 6.1 (p. 17): "the privacy region is `R({εᵢ, δᵢ})` … where … `δᵢ`'s are defined as in
  (6)"; the second parameter of the `i`-th region must be `1 - (1 - δ)^k (1 - δᵢ)` (as in
  Theorem 3.3 and the preceding display), which equals `δᵢ` of (6) only when `δ = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

namespace OptimalComposition

variable {ι : Type*} [Fintype ι] {ε δ : ℝ}

/-! ### The canonical composition dominates every composition -/

section Domination

variable {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] [∀ i, MeasurableSingletonClass (Y i)]
  [∀ i, Finite (Y i)]

/-- Running Markov kernels `T i` coordinatewise on independent inputs `x i ∼ ρ` gives
independent outputs `T i ∘ ρ`. -/
private lemma piKernel_comap_comp_pi (T : ∀ i, Kernel (Fin 4) (Y i)) [∀ i, IsMarkovKernel (T i)]
    (ρ : Measure (Fin 4)) [IsProbabilityMeasure ρ] :
    ZCDP.piKernel (fun i ↦ (T i).comap (fun x : ι → Fin 4 ↦ x i) (measurable_pi_apply i)) ∘ₘ
      Measure.pi (fun _ : ι ↦ ρ) = Measure.pi fun i ↦ T i ∘ₘ ρ := by
  classical
  refine Measure.ext_of_singleton fun z ↦ ?_
  rw [Measure.bind_apply (measurableSet_singleton z) (Kernel.aemeasurable _), lintegral_fintype,
    Measure.pi_singleton]
  simp_rw [ZCDP.piKernel_apply, Kernel.comap_apply, Measure.pi_singleton,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a ↦ T i a {z i} * ρ {a})]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _), lintegral_fintype]

/-- **Converse of the optimal composition theorem, pairwise form** (Section 6.2 of
Kairouz–Oh–Viswanath, for non-adaptive composition on finite alphabets): if each pair
`(μ i, ν i)` satisfies `D_{e^ε}(μ i ‖ ν i) ≤ δ` and `D_{e^ε}(ν i ‖ μ i) ≤ δ`, then for every
`γ` the product pair is no more distinguishable than `k = |ι|` independent copies of the canonical
pair: `D_γ(∏ μ i ‖ ∏ ν i) ≤ D_γ(P̃₀^k ‖ P̃₁^k)`. -/
theorem hockeyStickDiv_pi_le {μ ν : ∀ i, Measure (Y i)} [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (h : ∀ i, hockeyStickDiv (exp ε) (μ i) (ν i) ≤ δ ∧ hockeyStickDiv (exp ε) (ν i) (μ i) ≤ δ)
    (γ : ℝ) :
    hockeyStickDiv γ (Measure.pi μ) (Measure.pi ν) ≤
      hockeyStickDiv γ (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ false)
        (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ true) := by
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  choose T hT h₀ h₁ using fun i ↦ (exists_kernel_comp_canonicalMechanism_iff hε hδ₀ hδ₁).2 (h i)
  rw [← funext h₀, ← funext h₁, ← piKernel_comap_comp_pi, ← piKernel_comap_comp_pi]
  exact hockeyStickDiv_comp_le _ _ _

/-- **Optimal composition theorem, privacy-profile form** (Theorem 3.3 of Kairouz–Oh–Viswanath
as proved in Section 6.2, for **non-adaptive** composition on finite alphabets): if each of the
`k = |ι|` mechanisms `M i` is `(ε, δ)`-DP for a symmetric neighbouring relation (`ε ≥ 0`,
`δ ∈ [0, 1]`), then their independent composition `S ↦ ∏ i, M i S` is
`(ε', D_{e^ε'}(P̃₀^k ‖ P̃₁^k))`-DP for **every** `ε'`. By
`not_isEpsDeltaDP_piKernel_canonicalMechanism` this `δ` cannot be lowered. -/
theorem isEpsDeltaDP_piKernel_hockeyStickDiv {𝒟 : Type*} [MeasurableSpace 𝒟]
    {Adj : 𝒟 → 𝒟 → Prop} [Std.Symm Adj] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (h : ∀ i, IsEpsDeltaDP (M i) Adj ε δ) (ε' : ℝ) :
    IsEpsDeltaDP (ZCDP.piKernel M) Adj ε'
      (hockeyStickDiv (exp ε') (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ false)
        (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ true)) :=
  isEpsDeltaDP_iff_forall_hockeyStickDiv_le.2 fun S S' hS ↦ by
    rw [ZCDP.piKernel_apply, ZCDP.piKernel_apply]
    exact hockeyStickDiv_pi_le hε hδ₀ hδ₁ (fun i ↦
      ⟨isEpsDeltaDP_iff_forall_hockeyStickDiv_le.1 (h i) hS,
        isEpsDeltaDP_iff_forall_hockeyStickDiv_le.1 (h i) (Std.Symm.symm _ _ hS)⟩) _

end Domination

/-- **Achievability in the optimal composition theorem** (Section 6.1 of Kairouz–Oh–Viswanath):
the `k`-fold composition of the canonical mechanism is not `(ε', δ')`-DP for any
`δ' < D_{e^ε'}(P̃₀^k ‖ P̃₁^k)`. The hypothesis that `canonicalMechanism ε δ` is a Markov kernel
holds exactly when `δ ∈ [0, 1]` (`isMarkovKernel_canonicalMechanism`). This statement does not
assume `ε ≥ 0`; when `ε ≥ 0` (and `δ ∈ [0, 1]`) the canonical mechanism is itself `(ε, δ)`-DP
(`isEpsDeltaDP_canonicalMechanism`), which is what makes it a witness of optimality. Without
`ε ≥ 0` it need not be: for `ε = -1`, `δ = 0` it is Markov but fails `(ε, δ)`-DP on the whole
space. -/
theorem not_isEpsDeltaDP_piKernel_canonicalMechanism [IsMarkovKernel (canonicalMechanism ε δ)]
    {ε' δ' : ℝ} (hδ' : δ' < hockeyStickDiv (exp ε')
      (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ false)
      (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ true)) :
    ¬ IsEpsDeltaDP (ZCDP.piKernel fun _ : ι ↦ canonicalMechanism ε δ) (fun _ _ ↦ True) ε' δ' :=
  fun h ↦ by
    have := isEpsDeltaDP_iff_forall_hockeyStickDiv_le.1 h (S := false) (S' := true) trivial
    rw [ZCDP.piKernel_apply, ZCDP.piKernel_apply] at this
    linarith

/-! ### The explicit optimal privacy region -/

section Explicit

/-- The quantity `δ_i` of equation (6) of Kairouz–Oh–Viswanath:
`δ_i = (∑_{ℓ=0}^{i-1} C(k, ℓ) (e^{(k-ℓ)ε} - e^{(k-2i+ℓ)ε})) / (1 + e^ε)^k`. -/
noncomputable def compositionDelta (k i : ℕ) (ε : ℝ) : ℝ :=
  (∑ ℓ ∈ Finset.range i, (k.choose ℓ : ℝ) * (exp ((k - ℓ) * ε) - exp ((k - 2 * i + ℓ) * ε))) /
    (1 + exp ε) ^ k

private lemma canonicalProb_values (ε δ : ℝ) :
    canonicalProb ε δ false 0 = δ ∧
    canonicalProb ε δ false 1 = (1 - δ) / (1 + exp ε) * exp ε ∧
    canonicalProb ε δ false 2 = (1 - δ) / (1 + exp ε) ∧ canonicalProb ε δ false 3 = 0 ∧
    canonicalProb ε δ true 0 = 0 ∧ canonicalProb ε δ true 1 = (1 - δ) / (1 + exp ε) ∧
    canonicalProb ε δ true 2 = (1 - δ) / (1 + exp ε) * exp ε ∧
    canonicalProb ε δ true 3 = δ := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩ <;>
    simp only [canonicalProb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

private lemma pi_canonicalMechanism_real (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (b : Bool)
    (x : ι → Fin 4) :
    (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ b).real {x} =
      ∏ j, canonicalProb ε δ b (x j) := by
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun j _ ↦ canonicalMechanism_real_singleton hδ₀ hδ₁ b (x j)

/-- The value of a product `∏ j, (if j ∈ s then u else v)`. -/
private lemma prod_ite_mem_univ [DecidableEq ι] (s : Finset ι) (u v : ℝ) :
    ∏ j, (if j ∈ s then u else v) = u ^ s.card * v ^ (Fintype.card ι - s.card) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, show (Finset.univ.filter fun j ↦ j ∉ s) = sᶜ by ext; simp,
    Finset.card_compl]

/-- **The privacy region of the `k`-fold canonical composition** (Section 6.1 of
Kairouz–Oh–Viswanath, the display before Section 6.2): for `k = |ι|`, `ε ≥ 0`, `δ ∈ [0, 1]` and
`i ≤ k`,
`d_{(k-2i)ε}(P̃₀^k, P̃₁^k) = 1 - (1 - δ)^k + (1 - δ)^k δ_i = 1 - (1 - δ)^k (1 - δ_i)`.
The paper uses `i ≤ ⌊k/2⌋`, as do the theorems below. The identity is proved for all `i ≤ k`,
but for `2i > k` and `ε > 0` the slope `e^{(k-2i)ε} < 1` lies outside the paper's range (at
`ε = 0` every slope equals `1`) and, by the (unformalized) identity
`D_γ(P ‖ Q) = 1 - γ + γ D_{1/γ}(Q ‖ P)`, the case `i` carries the same information as the case
`k - i`; it is not a strengthening. -/
theorem hockeyStickDiv_pi_canonicalMechanism (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) {i : ℕ}
    (hi : i ≤ Fintype.card ι) :
    hockeyStickDiv (exp ((Fintype.card ι - 2 * i) * ε))
        (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ false)
        (Measure.pi fun _ : ι ↦ canonicalMechanism ε δ true) =
      1 - (1 - δ) ^ Fintype.card ι * (1 - compositionDelta (Fintype.card ι) i ε) := by
  classical
  have := isMarkovKernel_canonicalMechanism (ε := ε) hδ₀ hδ₁
  rw [hockeyStickDiv_eq_sum]
  simp only [pi_canonicalMechanism_real hδ₀ hδ₁]
  obtain ⟨v₀, v₁, v₂, v₃, u₀, u₁, u₂, u₃⟩ := canonicalProb_values ε δ
  set k := Fintype.card ι with hk
  set γ := exp ((k - 2 * i) * ε) with hγ_def
  set a := (1 - δ) / (1 + exp ε) with ha_def
  set w := canonicalProb ε δ with hw
  have ha : 0 ≤ a := div_nonneg (by linarith) (by positivity)
  have hγ : 0 ≤ γ := (exp_pos _).le
  have hw₀ (b : Bool) (x : Fin 4) : 0 ≤ w b x := canonicalProb_nonneg hδ₀ hδ₁ b x
  set w' : Bool → Fin 4 → ℝ := fun b x ↦ if x = 1 ∨ x = 2 then w b x else 0 with hw'
  have key : ∀ x : Fin 4, x ≠ 0 → x ≠ 3 → x = 1 ∨ x = 2 := by decide
  -- Step 1: the terms with a coordinate `0` or `3` contribute `1 - (1 - δ)^k`.
  have hdec (x : ι → Fin 4) : max 0 (∏ j, w false (x j) - γ * ∏ j, w true (x j)) =
      ∏ j, w false (x j) - ∏ j, w' false (x j) +
        max 0 (∏ j, w' false (x j) - γ * ∏ j, w' true (x j)) := by
    by_cases h0 : ∃ j, x j = 0
    · obtain ⟨j, hj⟩ := h0
      have e₁ : ∏ j, w true (x j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, u₀])
      have e₂ (b : Bool) : ∏ j, w' b (x j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hw', hj])
      rw [e₁, e₂, e₂, mul_zero, sub_zero, sub_zero, max_self, add_zero,
        max_eq_right (Finset.prod_nonneg fun j _ ↦ hw₀ _ _)]
    · by_cases h3 : ∃ j, x j = 3
      · obtain ⟨j, hj⟩ := h3
        have e₁ : ∏ j, w false (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, v₃])
        have e₂ (b : Bool) : ∏ j, w' b (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hw', hj])
        rw [e₁, e₂, e₂, mul_zero, sub_zero, max_self, zero_add, zero_sub,
          max_eq_left (neg_nonpos.2 (mul_nonneg hγ (Finset.prod_nonneg fun j _ ↦ hw₀ _ _)))]
      · push Not at h0 h3
        have e (b : Bool) : ∏ j, w' b (x j) = ∏ j, w b (x j) :=
          Finset.prod_congr rfl fun j _ ↦ by simp only [hw', key _ (h0 j) (h3 j), ↓reduceIte]
        rw [e, e, sub_self, zero_add]
  have hP : ∑ x : ι → Fin 4, ∏ j, w false (x j) = 1 := by
    rw [← Fintype.prod_sum (fun _ x ↦ w false x)]
    simp [hw, sum_canonicalProb]
  have hP' : ∑ x : ι → Fin 4, ∏ j, w' false (x j) = (1 - δ) ^ k := by
    rw [← Fintype.prod_sum (fun _ x ↦ w' false x), Finset.prod_const, Finset.card_univ]
    congr 1
    simp only [hw', Fin.sum_univ_four]
    simp only [Fin.reduceEq, or_self, ite_false, or_false, false_or, ite_true, zero_add,
      add_zero, v₁, v₂, ha_def]
    field_simp
    ring
  -- Step 2: the remaining terms are indexed by the set of coordinates equal to `2`.
  set φ : Finset ι → ι → Fin 4 := fun s j ↦ if j ∈ s then 2 else 1 with hφ_def
  have hφ : Function.Injective φ := fun s t hst ↦ by
    ext j
    have := congrFun hst j
    by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all
  have hprod (s : Finset ι) (b : Bool) :
      ∏ j, w' b (φ s j) = w b 2 ^ s.card * w b 1 ^ (k - s.card) := by
    rw [hk, ← prod_ite_mem_univ]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    by_cases hj : j ∈ s <;> simp [hw', hφ_def, hj]
  have hg : ∑ x : ι → Fin 4, max 0 (∏ j, w' false (x j) - γ * ∏ j, w' true (x j)) =
      ∑ s : Finset ι, max 0 (∏ j, w' false (φ s j) - γ * ∏ j, w' true (φ s j)) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := φ)
      (f := fun x ↦ max 0 (∏ j, w' false (x j) - γ * ∏ j, w' true (x j)))
      fun s _ t _ h ↦ hφ h]
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx ↦ ?_).symm
    obtain ⟨j, hj⟩ : ∃ j, x j = 0 ∨ x j = 3 := by
      by_contra hne
      push Not at hne
      refine hx (Finset.mem_image.2 ⟨Finset.univ.filter fun j ↦ x j = 2, Finset.mem_univ _,
        funext fun j ↦ ?_⟩)
      rcases key _ (hne j).1 (hne j).2 with h | h <;> simp [hφ_def, h]
    have e (b : Bool) : ∏ j, w' b (x j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rcases hj with h | h <;> simp [hw', h])
    simp [e]
  simp_rw [hprod] at hg
  have hcard := Finset.sum_powerset_apply_card (x := (Finset.univ : Finset ι)) fun m ↦
    max 0 (w false 2 ^ m * w false 1 ^ (k - m) - γ * (w true 2 ^ m * w true 1 ^ (k - m)))
  beta_reduce at hcard
  rw [Finset.powerset_univ, Finset.card_univ, ← hk] at hcard
  -- Step 3: evaluate the terms.
  have hterm (m : ℕ) (hm : m ≤ k) :
      max 0 (w false 2 ^ m * w false 1 ^ (k - m) - γ * (w true 2 ^ m * w true 1 ^ (k - m))) =
        a ^ k * (if m < i then exp ((k - m) * ε) - exp ((k - 2 * i + m) * ε) else 0) := by
    have e₁ : a ^ m * (a * exp ε) ^ (k - m) = a ^ k * exp ((k - m) * ε) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hm, ← Real.exp_nat_mul,
        Nat.cast_sub hm]
    have e₂ : γ * ((a * exp ε) ^ m * a ^ (k - m)) = a ^ k * exp ((k - 2 * i + m) * ε) := by
      rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hm, ← Real.exp_nat_mul,
        hγ_def, show ((k : ℝ) - 2 * i + m) * ε = (k - 2 * i) * ε + m * ε by ring, Real.exp_add]
      ring
    rw [v₂, v₁, u₂, u₁, e₁, e₂, ← mul_sub]
    split_ifs with h
    · have h' : (m : ℝ) < i := by exact_mod_cast h
      rw [max_eq_right (mul_nonneg (pow_nonneg ha k) (sub_nonneg.2 (exp_le_exp.2
        (mul_le_mul_of_nonneg_right (by linarith) hε))))]
    · have h' : (i : ℝ) ≤ m := by exact_mod_cast not_lt.1 h
      rw [mul_zero, max_eq_left (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha k) (sub_nonpos.2
        (exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hε))))]
  have hsum : ∑ m ∈ Finset.range (k + 1), k.choose m •
      max 0 (w false 2 ^ m * w false 1 ^ (k - m) - γ * (w true 2 ^ m * w true 1 ^ (k - m))) =
      a ^ k * ∑ m ∈ Finset.range i,
        (k.choose m : ℝ) * (exp ((k - m) * ε) - exp ((k - 2 * i + m) * ε)) := by
    calc _ = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) *
          (a ^ k * (if m < i then exp ((k - m) * ε) - exp ((k - 2 * i + m) * ε) else 0)) :=
          Finset.sum_congr rfl fun m hm ↦ by
            rw [nsmul_eq_mul, hterm m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))]
      _ = ∑ m ∈ Finset.range i, (k.choose m : ℝ) *
            (a ^ k * (exp ((k - m) * ε) - exp ((k - 2 * i + m) * ε))) + 0 := by
          rw [← Finset.sum_range_add_sum_Ico _ (hi.trans k.le_succ)]
          congr 1
          · exact Finset.sum_congr rfl fun m hm ↦ by
              simp only [Finset.mem_range.1 hm, ↓reduceIte]
          · exact Finset.sum_eq_zero fun m hm ↦ by
              simp only [not_lt.2 (Finset.mem_Ico.1 hm).1, ↓reduceIte, mul_zero]
      _ = _ := by
          rw [add_zero, Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ ↦ by ring
  -- Step 4: assemble.
  simp_rw [hdec]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hP, hP', hg, hcard, hsum, compositionDelta,
    ha_def, div_pow]
  ring

end Explicit

/-! ### The optimal composition theorem -/

/-- **Theorem 3.3** of Kairouz–Oh–Viswanath (the optimal composition theorem), for the
**non-adaptive** composition of `k = |ι|` mechanisms with finite output alphabets: if each `M i`
is `(ε, δ)`-DP for a symmetric neighbouring relation (`ε ≥ 0`, `δ ∈ [0, 1]`), then their
independent composition `S ↦ ∏ i, M i S` is `((k - 2i) ε, 1 - (1 - δ)^k (1 - δ_i))`-DP for every
`i` with `2i ≤ k`, where `δ_i = compositionDelta k i ε` is equation (6). The paper states it
also for adaptive composition (`isEpsDeltaDP_adaptiveCompose_compositionDelta`). The bound is
tight: the composition of `k` copies of
the canonical mechanism attains it (`hockeyStickDiv_pi_canonicalMechanism`,
`not_isEpsDeltaDP_piKernel_canonicalMechanism`). -/
theorem isEpsDeltaDP_piKernel_compositionDelta {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    [∀ i, MeasurableSingletonClass (Y i)] [∀ i, Finite (Y i)] {𝒟 : Type*} [MeasurableSpace 𝒟]
    {Adj : 𝒟 → 𝒟 → Prop} [Std.Symm Adj] {M : ∀ i, Kernel 𝒟 (Y i)} [∀ i, IsMarkovKernel (M i)]
    (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (h : ∀ i, IsEpsDeltaDP (M i) Adj ε δ) {i : ℕ}
    (hi : 2 * i ≤ Fintype.card ι) :
    IsEpsDeltaDP (ZCDP.piKernel M) Adj ((Fintype.card ι - 2 * i) * ε)
      (1 - (1 - δ) ^ Fintype.card ι * (1 - compositionDelta (Fintype.card ι) i ε)) := by
  rw [← hockeyStickDiv_pi_canonicalMechanism hε hδ₀ hδ₁ (by omega)]
  exact isEpsDeltaDP_piKernel_hockeyStickDiv hε hδ₀ hδ₁ h _

/-- **Tightness of Theorem 3.3** (Section 6.1 of Kairouz–Oh–Viswanath): the `k`-fold composition
of the canonical `(ε, δ)`-DP mechanism (`k = |ι|`, `ε ≥ 0`, `δ ∈ [0, 1]`) is not
`((k - 2i) ε, δ')`-DP for any `δ' < 1 - (1 - δ)^k (1 - δ_i)`, `2i ≤ k`. -/
theorem not_isEpsDeltaDP_piKernel_canonicalMechanism_compositionDelta
    [IsMarkovKernel (canonicalMechanism ε δ)] (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) {i : ℕ}
    (hi : 2 * i ≤ Fintype.card ι) {δ' : ℝ}
    (hδ' : δ' < 1 - (1 - δ) ^ Fintype.card ι * (1 - compositionDelta (Fintype.card ι) i ε)) :
    ¬ IsEpsDeltaDP (ZCDP.piKernel fun _ : ι ↦ canonicalMechanism ε δ) (fun _ _ ↦ True)
      ((Fintype.card ι - 2 * i) * ε) δ' :=
  not_isEpsDeltaDP_piKernel_canonicalMechanism
    (hδ'.trans_eq (hockeyStickDiv_pi_canonicalMechanism hε hδ₀ hδ₁ (by omega)).symm)

end OptimalComposition

end InformationTheory
