/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.MaximalLeakage.MutualInfo
public import InfoLeakage.MaximalLeakage.Operational
public import Mathlib.Probability.UniformOn

/-!
# g-vulnerability, g-leakage and their capacities

This file formalizes the gain-function theory of quantitative information flow, for a secret
`X ∼ μ` (the prior `π`) on a finite alphabet, a channel `κ : Kernel α β` (the channel matrix
`C[x, y] = κ x {y}`) with finite output alphabet, and a gain function `g : W → α → ℝ≥0` giving the
value `g(w, x)` of the guess `w` when the secret is `x`:

* M. S. Alvim, K. Chatzikokolakis, C. Palamidessi, G. Smith, *Measuring Information Leakage
  using Generalized Gain Functions*, CSF 2012, pp. 265–279 (HAL hal-00734044; not on arXiv),
  cited below as [ACPS12];
* M. S. Alvim, K. Chatzikokolakis, A. McIver, C. Morgan, C. Palamidessi, G. Smith, *Additive and
  Multiplicative Notions of Leakage, and Their Capacities*, CSF 2014, pp. 308–322
  (HAL hal-00989462; not on arXiv), cited below as [ACMMPS14].

## Main definitions

* `gVulnerability g μ`, `postGVulnerability g μ κ`: the prior and posterior g-vulnerabilities
  `V_g(π) = max_w ∑_x π[x] g(w, x)` and `V_g(π, C) = ∑_y max_w ∑_x π[x] C[x, y] g(w, x)`.
* `gLeakage g μ κ = log (V_g(π, C) / V_g(π))` and `gCapacity g κ = sup_π L_g(π, C)`, with
  multiplicative forms `gLeakageRatio` and `gCapacityRatio`; `addGLeakage g μ κ = V_g(π, C) -
  V_g(π)`.
* `gId`, `kTriesGain`, `reciprocalGain`: the identity, `k`-tries and "reciprocals of `π`" gain
  functions; `GainPos g`: `g` is not pathological; `OneSpanning g`: `g` is 1-spanning.
* `hyperKantorovich μ κ`: the closed form `∑_{y, x} π[x] |C[x, y] - p(y)| / 2` (Appendix B and
  Corollary 18 of [ACMMPS14]) of the Kantorovich distance between the point hyper `[π]` and the
  hyper `[π, C]`; `hyperKantorovich_eq_sum_posterior` writes it as
  `∑_y p(y) ‖π - p_{X|y}‖₁ / 2`.
* `addCapacityAt`, `addCapacity`, `multCapacityAtRatio`, `multCapacityRatio`: the additive and
  multiplicative capacities `L+_∀(π, C)`, `L+_∀(∀, C)`, `L_∀(π, C)`, `L_∀(∀, C)` over
  non-negative 1-spanning gain functions.
* `shannonCapacity κ = sup_π I(X; Y)`.

## Main statements

* `gVulnerability_gId`, `postGVulnerability_gId`: [ACPS12, Proposition 3.1].
* `gVulnerability_le_postGVulnerability`, `gLeakage_nonneg`: [ACPS12, Theorem 4.1].
* `gCapacity_eq_iSup_gLeakage`: the g-capacity is the supremum of the g-leakages over priors.
* `postGVulnerability_eq_gVulnerability_iff`, `gLeakage_eq_zero_iff`: [ACPS12, Theorem 4.2].
* `postGVulnerability_le_sum_iSup_mul`, `gLeakage_le_log_sum_iSup`, `gCapacity_le_log_sum_iSup`:
  the **"Miracle" Theorem** [ACPS12, Theorem 5.1]: `L_g(π, C) ≤ ML_g(C) ≤ ML(C)
  = log ∑_y max_x C[x, y]` for every non-negative gain function.
* `postGVulnerability_le_maxLeakageSum_mul`, `gLeakage_le_maxLeakage`: the Miracle Theorem with the
  maximal leakage `L(X → Y)` of Issa, Wagner and Kamath in place of the min-capacity, by the same
  proof.
* `gCapacity_kTriesGain_le`: [ACPS12, Corollary 5.2].
* `toReal_mutualInfo_le_log_sum_iSup`, `shannonCapacity_le`: [ACPS12, Theorem 5.3].
* `gLeakage_comp_le`: [ACPS12, Theorem 6.2].
* `gLeakageRatio_reciprocalGain`, `gLeakage_reciprocalGain`,
  `multCapacityAtRatio_eq_gLeakageRatio_reciprocalGain`: [ACMMPS14, Theorem 10].
* `multCapacityRatio_eq`: [ACMMPS14, Section VI-C]: `L_∀(∀, C) = ML(C)`.
* `isGreatest_addGLeakage`, `addCapacityAt_eq`: [ACMMPS14, Theorem 17], in the closed form of
  Appendix B: the additive `π`-capacity is `∑_{y, x} π[x] |C[x, y] - p(y)| / 2`.
* `addGLeakage_comp_le`, `hyperKantorovich_comp_le`: [ACMMPS14, Lemma 19].
* `exists_oneSpanning_cascade`, `hyperKantorovich_comp_le_comp`, `addCapacityAt_comp_le`:
  [ACMMPS14, Lemma 20].
* `addCapacity_comp_le`: [ACMMPS14, Theorem 21].
* `hyperKantorovich_dalenius`, `addCapacityAt_dalenius`, `addGLeakage_dalenius_le`: [ACMMPS14,
  Corollary 22] (Dalenius bound).
* `gLeakage_comp_le`, `multCapacityAtRatio_comp_le`, `multCapacityRatio_comp_le`,
  `multCapacityAtRatio_dalenius`: [ACMMPS14, Corollary 23].

## Paper-to-Lean map

* [ACPS12] Definitions 3.2–3.4: `gVulnerability`, `postGVulnerability`, `gLeakage`, `gCapacity`;
  Definition 3.5: `gId`; Section III-C3: `kTriesGain`.
* [ACPS12] Proposition 3.1, Theorems 4.1, 4.2, 5.1, 5.3, 6.2 and Corollary 5.2: see above.
* [ACMMPS14] Definition 3: `OneSpanning`; Definitions 5, 6, 8, 9: `multCapacityAtRatio`,
  `multCapacityRatio`, `addCapacityAt`, `addCapacity`; Section III: `addGLeakage`.
* [ACMMPS14] Theorem 10, Theorem 17 (in the closed form of Appendix B and Corollary 18), Lemmas
  19 and 20, Theorem 21, Corollaries 22 and 23: see above.

Not formalized: [ACPS12] Sections VI-B to VI-F (converses of Theorem 6.2, the lattice of
information) and the numerical examples; [ACMMPS14] Lemmas 1 and 2 (gain-function algebra),
Theorem 11 (NP-completeness), hypers as distributions on distributions, the Kantorovich
construction and the earth-moving (Wasserstein) metric (Definitions 12 and 15, Lemmas 13, 14,
24 and 26), the Kantorovich–Rubinstein duality (Theorem 16), hence the equalities of Theorem 17
with the abstract `W` and `K` distances (only their closed form is formalized), the complexity
statement of Corollary 18 and the examples of Section VIII. The link of g-leakage with
`InfoLeakage.QIF.MinEntropy` is in `InfoLeakage.QIF.Links`.

## Implementation notes

Gain functions take values in `ℝ≥0`: [ACPS12] uses `[0, 1]` and notes (footnote 3) that any
bounded range gives the same leakage; [ACMMPS14] uses non-negative 1-spanning gain functions. All
results hold for every non-negative gain function, not only for those with values in `[0, 1]`.
The sets of guesses are finite where the papers require it, and nonempty where needed. Leakages
are in nats.

The additive results of [ACMMPS14] are proved through the closed formula `hyperKantorovich`, not
through earth-moving duality: the upper bound uses that the posteriors
average to the prior and that 1-spanning gains vary by at most `1`; the gain function
`kantorovichGain` on the guesses `w : X → {-1, 1}` attains it. Two misprints of [ACMMPS14] are
corrected: in the proof of Theorem 17 (p. 317) this gain function is printed with
`+ ∑_{x'} π[x'] w(x')` (which gives `V_g[π] = 2`, not `1`), while Appendix C uses `-`; and the
right-capacity bound of Corollary 23 is printed `L_∀(ρ, R) ≤ L_∀(τ, S)`, which is ill-typed, for
`L_∀(ρ, R) ≤ L_∀(τ, T)`. In the proof of Lemma 20 the
paper's transported gain `h(w, y) = ∑_x Π[x, y] g(w, x) / τ[y]` divides by zero on outputs `y`
of probability zero; `cascadeGain` uses `g(w, x₀)` there, which keeps `h` 1-spanning.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace InformationTheory

universe u

variable {α : Type u} {β γ W : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β} {g : W → α → ℝ≥0}

section Definitions

variable [Fintype α]

/-- The **prior g-vulnerability** `V_g(π) = max_w ∑_x π[x] g(w, x)` of a prior `μ` under the gain
function `g : W → α → ℝ≥0` (Definition 3.2 of Alvim–Chatzikokolakis–Palamidessi–Smith): the
largest expected gain of a single guess `w`. -/
noncomputable def gVulnerability (g : W → α → ℝ≥0) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ w, ∑ x, μ {x} * g w x

/-- The **posterior g-vulnerability** `V_g(π, C) = ∑_y max_w ∑_x π[x] C[x, y] g(w, x)` of a prior
`μ` through the channel `κ` (Definition 3.3 of Alvim et al.). -/
noncomputable def postGVulnerability [Fintype β] (g : W → α → ℝ≥0) (μ : Measure α)
    (κ : Kernel α β) : ℝ≥0∞ :=
  ∑ y, ⨆ w, ∑ x, μ {x} * κ x {y} * g w x

/-- The multiplicative form `V_g(π, C) / V_g(π)` of the g-leakage. -/
noncomputable def gLeakageRatio [Fintype β] (g : W → α → ℝ≥0) (μ : Measure α) (κ : Kernel α β) :
    ℝ≥0∞ :=
  postGVulnerability g μ κ / gVulnerability g μ

/-- The **g-leakage** `L_g(π, C) = H_g(π) - H_g(π, C) = log (V_g(π, C) / V_g(π))`, in nats
(Definition 3.4 of Alvim et al.). -/
noncomputable def gLeakage [Fintype β] (g : W → α → ℝ≥0) (μ : Measure α) (κ : Kernel α β) : ℝ :=
  Real.log (gLeakageRatio g μ κ).toReal

/-- The multiplicative form of the **g-capacity** `ML_g(C) = sup_π L_g(π, C)`. -/
noncomputable def gCapacityRatio [Fintype β] (g : W → α → ℝ≥0) (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (μ : Measure α) (_ : IsProbabilityMeasure μ), gLeakageRatio g μ κ

/-- The **g-capacity** `ML_g(C) = sup_π L_g(π, C)`, in nats (Definition 3.4 of Alvim et al.). -/
noncomputable def gCapacity [Fintype β] (g : W → α → ℝ≥0) (κ : Kernel α β) : ℝ :=
  Real.log (gCapacityRatio g κ).toReal

/-- The **additive g-leakage** `L+_g(π, C) = V_g(π, C) - V_g(π)` (Section III of Alvim,
Chatzikokolakis, McIver, Morgan, Palamidessi and Smith, CSF 2014). -/
noncomputable def addGLeakage [Fintype β] (g : W → α → ℝ≥0) (μ : Measure α) (κ : Kernel α β) :
    ℝ :=
  (postGVulnerability g μ κ).toReal - (gVulnerability g μ).toReal

end Definitions

/-- The **identity gain function** `g_id(w, x) = [w = x]` (Definition 3.5 of Alvim et al.). -/
def gId [DecidableEq α] (w x : α) : ℝ≥0 :=
  if w = x then 1 else 0

lemma coe_gId [DecidableEq α] (w x : α) : (gId w x : ℝ≥0∞) = if w = x then 1 else 0 := by
  split_ifs with h <;> simp [gId, h]

/-- A gain function is **non-pathological** if every secret has a guess with positive gain, the
standing assumption of Alvim et al. (Section IV) that makes `V_g(π) > 0`. -/
def GainPos (g : W → α → ℝ≥0) : Prop :=
  ∀ x, ∃ w, g w x ≠ 0

section Basic

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass α] in
/-- Summing the joint expected gains of a guess `w` over the outputs gives its prior expected
gain. -/
lemma sum_postGain_eq [IsMarkovKernel κ] (w : W) :
    ∑ y, ∑ x, μ {x} * κ x {y} * g w x = ∑ x, μ {x} * g w x := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_measure_singleton (μ := κ x)]
  simp

omit [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
/-- **Proposition 3.1 of Alvim et al.**: under the identity gain function, g-vulnerability is the
vulnerability `V(π) = max_x π[x]`. -/
theorem gVulnerability_gId [DecidableEq α] : gVulnerability gId μ = ⨆ x, μ {x} := by
  refine iSup_congr fun w ↦ ?_
  simp [coe_gId]

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- Under the identity gain function, posterior g-vulnerability is the posterior vulnerability
`V(π, C) = ∑_y max_x π[x] C[x, y]`, so `g_id`-leakage is min-entropy leakage. -/
theorem postGVulnerability_gId [DecidableEq α] :
    postGVulnerability gId μ κ = ∑ y, ⨆ x, κ x {y} * μ {x} := by
  refine Finset.sum_congr rfl fun y _ ↦ iSup_congr fun w ↦ ?_
  simp [coe_gId, mul_comm]

omit [MeasurableSingletonClass α] in
/-- **Theorem 4.1 of Alvim et al.**: observing the output cannot decrease g-vulnerability,
`V_g(π) ≤ V_g(π, C)`. -/
theorem gVulnerability_le_postGVulnerability [IsMarkovKernel κ] :
    gVulnerability g μ ≤ postGVulnerability g μ κ := by
  refine iSup_le fun w ↦ ?_
  rw [← sum_postGain_eq (κ := κ) w]
  exact Finset.sum_le_sum fun y _ ↦ le_iSup (fun w ↦ ∑ x, μ {x} * κ x {y} * g w x) w

end Basic

section Finiteness

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
lemma gVulnerability_ne_top [Finite W] [IsFiniteMeasure μ] : gVulnerability g μ ≠ ∞ := by
  have := Fintype.ofFinite W
  have h (w : W) : ∑ x, μ {x} * g w x ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.mul_ne_top (measure_ne_top μ _) ENNReal.coe_ne_top
  refine ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun w (_ : w ∈ Finset.univ) ↦ h w)
    (iSup_le fun w ↦ ?_)
  exact Finset.single_le_sum (f := fun w ↦ ∑ x, μ {x} * g w x) (fun _ _ ↦ zero_le)
    (Finset.mem_univ w)

omit [Fintype β] [MeasurableSingletonClass β] in
/-- For a non-pathological gain function, the prior g-vulnerability of a probability measure is
positive. -/
lemma gVulnerability_ne_zero [IsProbabilityMeasure μ] (hg : GainPos g) :
    gVulnerability g μ ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, μ {x} ≠ 0 := by
    by_contra! h
    have := measure_univ (μ := μ)
    rw [← Finset.coe_univ, ← sum_measure_singleton] at this
    simp [h] at this
  obtain ⟨w, hw⟩ := hg x
  refine (lt_of_lt_of_le ?_ (le_iSup (fun w ↦ ∑ x, μ {x} * g w x) w)).ne'
  exact lt_of_lt_of_le (ENNReal.mul_pos hx (by simpa using hw))
    (Finset.single_le_sum (f := fun x ↦ μ {x} * g w x) (fun _ _ ↦ zero_le) (Finset.mem_univ x))

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma postGVulnerability_le_card_mul [IsMarkovKernel κ] :
    postGVulnerability g μ κ ≤ Fintype.card β * gVulnerability g μ := by
  calc postGVulnerability g μ κ ≤ ∑ _y : β, gVulnerability g μ := by
        refine Finset.sum_le_sum fun y _ ↦ iSup_le fun w ↦ ?_
        refine le_iSup_of_le w (Finset.sum_le_sum fun x _ ↦ ?_)
        gcongr
        exact (mul_le_of_le_one_right zero_le prob_le_one)
    _ = Fintype.card β * gVulnerability g μ := by simp

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma postGVulnerability_ne_top [Finite W] [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    postGVulnerability g μ κ ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) gVulnerability_ne_top)
    postGVulnerability_le_card_mul

/-- For a non-pathological gain function, the g-leakage ratio is at least `1`
(Theorem 4.1 of Alvim et al.) and finite. -/
lemma one_le_toReal_gLeakageRatio [Finite W] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (hg : GainPos g) : 1 ≤ (gLeakageRatio g μ κ).toReal := by
  have h0 := gVulnerability_ne_zero (g := g) (μ := μ) hg
  have ht := gVulnerability_ne_top (g := g) (μ := μ)
  rw [gLeakageRatio, ENNReal.toReal_div, le_div_iff₀ (ENNReal.toReal_pos h0 ht), one_mul]
  exact ENNReal.toReal_mono postGVulnerability_ne_top gVulnerability_le_postGVulnerability

/-- **Theorem 4.1 of Alvim et al.**: g-leakage is nonnegative. -/
theorem gLeakage_nonneg [Finite W] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (hg : GainPos g) : 0 ≤ gLeakage g μ κ :=
  Real.log_nonneg (one_le_toReal_gLeakageRatio hg)

end Finiteness

section ZeroLeakage

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass α] [Fintype β] in
/-- A guess `w₀` that is optimal for every output is also optimal a priori (Theorem 4.2 of
Alvim et al.). -/
lemma sum_le_sum_of_forall_postGain_le [Finite β] [IsMarkovKernel κ] {w₀ : W}
    (h : ∀ w y, ∑ x, μ {x} * κ x {y} * g w x ≤ ∑ x, μ {x} * κ x {y} * g w₀ x) (w : W) :
    ∑ x, μ {x} * g w x ≤ ∑ x, μ {x} * g w₀ x := by
  have := Fintype.ofFinite β
  rw [← sum_postGain_eq (κ := κ) w, ← sum_postGain_eq (κ := κ) w₀]
  exact Finset.sum_le_sum fun y _ ↦ h w y

omit [MeasurableSingletonClass α] in
/-- **Theorem 4.2 of Alvim et al.**, multiplicative form: the posterior and prior g-vulnerabilities
coincide iff some guess `w₀` gives the best expected gain for every output `y`. -/
theorem postGVulnerability_eq_gVulnerability_iff [Finite W] [Nonempty W] [IsFiniteMeasure μ]
    [IsMarkovKernel κ] :
    postGVulnerability g μ κ = gVulnerability g μ ↔
      ∃ w₀, ∀ w y, ∑ x, μ {x} * κ x {y} * g w x ≤ ∑ x, μ {x} * κ x {y} * g w₀ x := by
  set E : W → β → ℝ≥0∞ := fun w y ↦ ∑ x, μ {x} * κ x {y} * g w x
  have hE (w : W) (y : β) : E w y ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top μ _)
      (measure_ne_top _ _)) ENNReal.coe_ne_top
  constructor
  · intro h
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w ↦ ∑ x, μ {x} * g w x
    have hV : gVulnerability g μ = ∑ y, E w₀ y := by
      rw [sum_postGain_eq]
      exact le_antisymm (iSup_le hw₀) (le_iSup (fun w ↦ ∑ x, μ {x} * g w x) w₀)
    have hle (y : β) : E w₀ y ≤ ⨆ w, E w y := le_iSup (fun w ↦ E w y) w₀
    have hsup (y : β) : ⨆ w, E w y ≠ ∞ := by
      have := Fintype.ofFinite W
      exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun w _ ↦ hE w y) (iSup_le fun w ↦
        Finset.single_le_sum (f := fun w ↦ E w y) (fun _ _ ↦ zero_le) (Finset.mem_univ w))
    have hsum : ∑ y, (E w₀ y).toReal = ∑ y, (⨆ w, E w y).toReal := by
      rw [← ENNReal.toReal_sum fun y _ ↦ hE w₀ y, ← ENNReal.toReal_sum fun y _ ↦ hsup y, ← hV]
      exact congrArg ENNReal.toReal h.symm
    have heq := (Finset.sum_eq_sum_iff_of_le fun y _ ↦
      ENNReal.toReal_mono (hsup y) (hle y)).1 hsum
    refine ⟨w₀, fun w y ↦ ?_⟩
    have : ⨆ w, E w y = E w₀ y :=
      ((ENNReal.toReal_eq_toReal_iff' (hsup y) (hE w₀ y)).1 (heq y (Finset.mem_univ y)).symm)
    exact (le_iSup (fun w ↦ E w y) w).trans this.le
  · rintro ⟨w₀, hw₀⟩
    refine le_antisymm ?_ gVulnerability_le_postGVulnerability
    calc postGVulnerability g μ κ = ∑ y, E w₀ y :=
          Finset.sum_congr rfl fun y _ ↦
            le_antisymm (iSup_le fun w ↦ hw₀ w y) (le_iSup (fun w ↦ E w y) w₀)
      _ = ∑ x, μ {x} * g w₀ x := sum_postGain_eq w₀
      _ ≤ gVulnerability g μ := le_iSup (fun w ↦ ∑ x, μ {x} * g w x) w₀

/-- **Theorem 4.2 of Alvim et al.**: for a non-pathological gain function, the g-leakage is `0`
iff some guess `w₀` gives the best expected gain for every output `y`. -/
theorem gLeakage_eq_zero_iff [Finite W] [Nonempty W] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (hg : GainPos g) :
    gLeakage g μ κ = 0 ↔
      ∃ w₀, ∀ w y, ∑ x, μ {x} * κ x {y} * g w x ≤ ∑ x, μ {x} * κ x {y} * g w₀ x := by
  have h1 := one_le_toReal_gLeakageRatio (μ := μ) (κ := κ) hg
  rw [← postGVulnerability_eq_gVulnerability_iff, gLeakage, Real.log_eq_zero,
    ← ENNReal.div_eq_one_iff (gVulnerability_ne_zero hg) gVulnerability_ne_top,
    ← gLeakageRatio, ← ENNReal.toReal_eq_one_iff]
  constructor
  · rintro (h | h | h) <;> [linarith; exact h; linarith]
  · exact fun h ↦ Or.inr (Or.inl h)

end ZeroLeakage

section Miracle

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- The proof of the **"Miracle" Theorem 5.1 of Alvim et al.**, in the sharper form where each
column maximum only ranges over the support of the prior: `V_g(π, C) ≤ e^{L(X → Y)} V_g(π)`, with
`L(X → Y) = log ∑_y max_{x ∈ supp π} C[x, y]` the maximal leakage of Issa, Wagner and Kamath. -/
theorem postGVulnerability_le_maxLeakageSum_mul :
    postGVulnerability g μ κ ≤ maxLeakageSum μ κ * gVulnerability g μ := by
  rw [postGVulnerability, maxLeakageSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun y _ ↦ iSup_le fun w ↦ ?_
  set M := ⨆ (x) (_ : μ {x} ≠ 0), κ x {y}
  calc ∑ x, μ {x} * κ x {y} * g w x ≤ ∑ x, M * μ {x} * g w x :=
        Finset.sum_le_sum fun x _ ↦
          mul_le_mul_left ((mul_comm (μ {x}) _).trans_le (mul_le_iSup_mul x y)) _
    _ = M * ∑ x, μ {x} * g w x := by
        rw [Finset.mul_sum]
        simp_rw [mul_assoc]
    _ ≤ M * gVulnerability g μ := by
        gcongr
        exact le_iSup (fun w ↦ ∑ x, μ {x} * g w x) w

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- **"Miracle" Theorem 5.1 of Alvim et al.**, multiplicative form: for every prior and every
nonnegative gain function, `V_g(π, C) ≤ (∑_y max_x C[x, y]) V_g(π)`. The factor
`∑_y max_x C[x, y]` is the exponential of the min-capacity `ML(C)` (Theorem 2.1 of Alvim et al.;
`maxMultLeakage_eq` in `InfoLeakage.QIF.MinEntropy`). -/
theorem postGVulnerability_le_sum_iSup_mul :
    postGVulnerability g μ κ ≤ (∑ y, ⨆ x, κ x {y}) * gVulnerability g μ :=
  postGVulnerability_le_maxLeakageSum_mul.trans <| mul_le_mul_left
    (Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ le_iSup (fun x ↦ κ x {y}) x) _

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- **"Miracle" Theorem 5.1 of Alvim et al.**, capacity form, multiplicative: the g-capacity of a
channel is at most its min-capacity, `ML_g(C) ≤ ML(C)`, for every nonnegative gain function. -/
theorem gCapacityRatio_le_sum_iSup : gCapacityRatio g κ ≤ ∑ y, ⨆ x, κ x {y} :=
  iSup₂_le fun _ _ ↦ ENNReal.div_le_of_le_mul postGVulnerability_le_sum_iSup_mul

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma sum_iSup_ne_top [IsMarkovKernel κ] : ∑ y, ⨆ x, κ x {y} ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ ↦
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ prob_le_one)

/-- **"Miracle" Theorem 5.1 of Alvim et al.**: for every prior and every non-pathological gain
function, the g-leakage is at most the min-capacity, `L_g(π, C) ≤ ML(C) = log ∑_y max_x C[x, y]`. -/
theorem gLeakage_le_log_sum_iSup [Finite W] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (hg : GainPos g) : gLeakage g μ κ ≤ Real.log (∑ y, ⨆ x, κ x {y}).toReal :=
  Real.log_le_log (zero_lt_one.trans_le (one_le_toReal_gLeakageRatio hg))
    (ENNReal.toReal_mono sum_iSup_ne_top (ENNReal.div_le_of_le_mul
      postGVulnerability_le_sum_iSup_mul))

/-- A strengthening of the "Miracle" Theorem 5.1 of Alvim et al. with the same proof: the
g-leakage is at most the maximal leakage of Issa, Wagner and Kamath, `L_g(π, C) ≤ L(X → Y)`. -/
theorem gLeakage_le_maxLeakage [Finite W] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (hg : GainPos g) : gLeakage g μ κ ≤ maxLeakage μ κ :=
  Real.log_le_log (zero_lt_one.trans_le (one_le_toReal_gLeakageRatio hg))
    (ENNReal.toReal_mono maxLeakageSum_ne_top (ENNReal.div_le_of_le_mul
      postGVulnerability_le_maxLeakageSum_mul))

/-- **"Miracle" Theorem 5.1 of Alvim et al.**: for every non-pathological gain function `g`, the
g-capacity is at most the min-capacity, `ML_g(C) ≤ ML(C) = log ∑_y max_x C[x, y]`. -/
theorem gCapacity_le_log_sum_iSup [Finite W] [Nonempty α] [IsMarkovKernel κ] (hg : GainPos g) :
    gCapacity g κ ≤ Real.log (∑ y, ⨆ x, κ x {y}).toReal := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have h1 : 1 ≤ (gCapacityRatio g κ).toReal := by
    refine (one_le_toReal_gLeakageRatio (μ := Measure.dirac x₀) (κ := κ) hg).trans ?_
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top sum_iSup_ne_top gCapacityRatio_le_sum_iSup)
      (le_iSup₂_of_le (Measure.dirac x₀) inferInstance le_rfl)
  exact Real.log_le_log (zero_lt_one.trans_le h1)
    (ENNReal.toReal_mono sum_iSup_ne_top gCapacityRatio_le_sum_iSup)

/-- The g-capacity is the supremum over priors of the g-leakage, `ML_g(C) = sup_π L_g(π, C)`
(Definition 3.4 of Alvim et al.), for a non-pathological gain function with finitely many
guesses. -/
theorem gCapacity_eq_iSup_gLeakage [Finite W] [Nonempty α] [IsMarkovKernel κ] (hg : GainPos g) :
    gCapacity g κ = ⨆ μ : {μ : Measure α // IsProbabilityMeasure μ}, gLeakage g μ.1 κ := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have : Nonempty {μ : Measure α // IsProbabilityMeasure μ} :=
    ⟨⟨Measure.dirac x₀, inferInstance⟩⟩
  set r : {μ : Measure α // IsProbabilityMeasure μ} → ℝ := fun μ ↦ (gLeakageRatio g μ.1 κ).toReal
  have hr1 (μ : {μ : Measure α // IsProbabilityMeasure μ}) : 1 ≤ r μ := by
    have := μ.2
    exact one_le_toReal_gLeakageRatio hg
  have hrle (μ : {μ : Measure α // IsProbabilityMeasure μ}) :
      gLeakageRatio g μ.1 κ ≤ ∑ y, ⨆ x, κ x {y} :=
    ENNReal.div_le_of_le_mul postGVulnerability_le_sum_iSup_mul
  have hrtop (μ : {μ : Measure α // IsProbabilityMeasure μ}) : gLeakageRatio g μ.1 κ ≠ ∞ :=
    ne_top_of_le_ne_top sum_iSup_ne_top (hrle μ)
  have hbdd : BddAbove (Set.range r) :=
    ⟨(∑ y, ⨆ x, κ x {y}).toReal, Set.forall_mem_range.2 fun μ ↦
      ENNReal.toReal_mono sum_iSup_ne_top (hrle μ)⟩
  have hcap : (gCapacityRatio g κ).toReal = ⨆ μ, r μ := by
    rw [gCapacityRatio, iSup_subtype', ENNReal.toReal_iSup hrtop]
  have hpos : 0 < ⨆ μ, r μ := zero_lt_one.trans_le ((hr1 ⟨_, inferInstance⟩).trans
    (le_ciSup hbdd ⟨Measure.dirac x₀, inferInstance⟩))
  rw [gCapacity, hcap]
  refine le_antisymm ?_ (ciSup_le fun μ ↦
    Real.log_le_log (zero_lt_one.trans_le (hr1 μ)) (le_ciSup hbdd μ))
  have hlog : BddAbove (Set.range fun μ ↦ Real.log (r μ)) :=
    ⟨Real.log (∑ y, ⨆ x, κ x {y}).toReal, Set.forall_mem_range.2 fun μ ↦
      Real.log_le_log (zero_lt_one.trans_le (hr1 μ))
        (ENNReal.toReal_mono sum_iSup_ne_top (hrle μ))⟩
  rw [Real.log_le_iff_le_exp hpos]
  refine ciSup_le fun μ ↦ ?_
  rw [← Real.exp_log (zero_lt_one.trans_le (hr1 μ))]
  exact Real.exp_le_exp.2 (le_ciSup hlog μ)

/-- The **k-tries gain function** `g_{W_k}(S, x) = [x ∈ S]`, for guesses `S` that are sets of at
most `k` secrets (Section III-C3 of Alvim et al.). -/
def kTriesGain [DecidableEq α] (k : ℕ) (S : {S : Finset α // S.card ≤ k}) (x : α) :
    ℝ≥0 :=
  if x ∈ S.1 then 1 else 0

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
lemma gainPos_kTriesGain [DecidableEq α] {k : ℕ} (hk : k ≠ 0) :
    GainPos (kTriesGain (α := α) k) := fun x ↦
  ⟨⟨{x}, by simpa using Nat.one_le_iff_ne_zero.2 hk⟩, by simp [kTriesGain]⟩

/-- **Corollary 5.2 of Alvim et al.**: the capacity of a channel in the `k`-tries scenario is at
most its min-capacity, the capacity in the one-try scenario. -/
theorem gCapacity_kTriesGain_le [DecidableEq α] [Nonempty α] [IsMarkovKernel κ] {k : ℕ}
    (hk : k ≠ 0) :
    gCapacity (kTriesGain k) κ ≤ Real.log (∑ y, ⨆ x, κ x {y}).toReal :=
  gCapacity_le_log_sum_iSup (gainPos_kTriesGain hk)

end Miracle

section Shannon

variable [Countable α] [Fintype β] [MeasurableSingletonClass β]

/-- **Theorem 5.3 of Alvim et al.**, for one prior: the mutual information is at most the
min-capacity, `I(X; Y) ≤ ML(C) = log ∑_y max_x C[x, y]`. We derive it from Lemma 2 of Issa,
Wagner and Kamath (`toReal_mutualInfo_compProd_le_maxLeakage`), instead of the paper's Jensen
argument. -/
theorem toReal_mutualInfo_le_log_sum_iSup [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    (mutualInfo (μ ⊗ₘ κ)).toReal ≤ Real.log (∑ y, ⨆ x, κ x {y}).toReal := by
  obtain ⟨x, hx⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  refine toReal_mutualInfo_compProd_le_maxLeakage.trans ?_
  refine Real.log_le_log (zero_lt_one.trans_le (one_le_toReal_maxLeakageSum hx))
    (ENNReal.toReal_mono sum_iSup_ne_top ?_)
  exact Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x _ ↦ le_iSup (fun x ↦ κ x {y}) x

/-- The **Shannon capacity** `sup_π I(X; Y)` of a channel. -/
noncomputable def shannonCapacity (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ (μ : Measure α) (_ : IsProbabilityMeasure μ), mutualInfo (μ ⊗ₘ κ)

/-- **Theorem 5.3 of Alvim et al.**: the Shannon capacity of a channel is at most its
min-capacity `ML(C) = log ∑_y max_x C[x, y]`. -/
theorem shannonCapacity_le [IsMarkovKernel κ] :
    shannonCapacity κ ≤ ENNReal.ofReal (Real.log (∑ y, ⨆ x, κ x {y}).toReal) := by
  refine iSup₂_le fun μ _ ↦ ?_
  rw [← ENNReal.ofReal_toReal (mutualInfo_compProd_ne_top (μ := μ) (κ := κ))]
  exact ENNReal.ofReal_le_ofReal toReal_mutualInfo_le_log_sum_iSup

end Shannon

section Refinement

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [MeasurableSingletonClass α] in
/-- Post-processing the output by a channel `η` cannot increase the posterior g-vulnerability. -/
theorem postGVulnerability_comp_le (η : Kernel β γ) [IsMarkovKernel η] :
    postGVulnerability g μ (η ∘ₖ κ) ≤ postGVulnerability g μ κ := by
  set E : W → β → ℝ≥0∞ := fun w y ↦ ∑ x, μ {x} * κ x {y} * g w x
  calc postGVulnerability g μ (η ∘ₖ κ) = ∑ z, ⨆ w, ∑ y, η y {z} * E w y := by
        refine Finset.sum_congr rfl fun z _ ↦ iSup_congr fun w ↦ ?_
        simp_rw [kernel_comp_apply_singleton, E, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring
    _ ≤ ∑ z, ∑ y, η y {z} * ⨆ w, E w y := by
        refine Finset.sum_le_sum fun z _ ↦ iSup_le fun w ↦ ?_
        gcongr with y
        exact le_iSup (fun w ↦ E w y) w
    _ = postGVulnerability g μ κ := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
        rfl

/-- **Theorem 6.2 of Alvim et al.**: if `C₁ = C₂ C₃` is the cascade of `C₂` with a
post-processing channel `C₃` (composition refinement `C₁ ⊑∘ C₂`), then `C₁` leaks no more than
`C₂`, for every prior and every non-pathological gain function: `L_g(π, C₁) ≤ L_g(π, C₂)`. -/
theorem gLeakage_comp_le [Finite W] [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] (hg : GainPos g) :
    gLeakage g μ (η ∘ₖ κ) ≤ gLeakage g μ κ := by
  refine Real.log_le_log (zero_lt_one.trans_le (one_le_toReal_gLeakageRatio hg))
    (ENNReal.toReal_mono ?_ (ENNReal.div_le_div_right (postGVulnerability_comp_le η) _))
  exact ENNReal.div_ne_top postGVulnerability_ne_top (gVulnerability_ne_zero hg)

end Refinement

section ReciprocalGain

variable [DecidableEq α]

/-- The "reciprocals of `π`" gain function `g_π(w, x) = [w = x] a / π[x]` with
`a = min_x π[x]` (proof of Theorem 10 of Alvim et al., CSF 2014). For a prior of full support it
takes values in `[0, 1]` (`reciprocalGain_le_one`) and cancels the bias of a skewed prior. -/
noncomputable def reciprocalGain (μ : Measure α) (w x : α) : ℝ≥0 :=
  if w = x then ((⨅ x', μ {x'}) / μ {x}).toNNReal else 0

lemma coe_reciprocalGain [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) (w x : α) :
    (reciprocalGain μ w x : ℝ≥0∞) = if w = x then (⨅ x', μ {x'}) / μ {x} else 0 := by
  have ha : ⨅ x', μ {x'} ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ {x}) (iInf_le (fun x' ↦ μ {x'}) x)
  split_ifs with h
  · subst h
    simp only [reciprocalGain, ↓reduceIte]
    rw [ENNReal.coe_toNNReal (ENNReal.div_ne_top ha (hμ w))]
  · simp [reciprocalGain, h]

/-- The gain function `g_π` takes values in `[0, 1]`. -/
lemma reciprocalGain_le_one [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) (w x : α) :
    reciprocalGain μ w x ≤ 1 := by
  rw [← ENNReal.coe_le_coe, coe_reciprocalGain hμ]
  split_ifs
  · exact ENNReal.div_le_of_le_mul (by simpa using iInf_le (fun x' ↦ μ {x'}) x)
  · exact zero_le

omit [DecidableEq α] in
lemma exists_iInf_measure_singleton_eq [Finite α] [Nonempty α] (μ : Measure α) :
    ∃ x₀, ⨅ x, μ {x} = μ {x₀} := by
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min fun x ↦ μ {x}
  exact ⟨x₀, le_antisymm (iInf_le _ x₀) (le_iInf hx₀)⟩

variable [Fintype α] [Fintype β]

lemma gVulnerability_reciprocalGain [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) [Nonempty α] :
    gVulnerability (reciprocalGain μ) μ = ⨅ x, μ {x} := by
  have h (w : α) : ∑ x, μ {x} * reciprocalGain μ w x = ⨅ x, μ {x} := by
    simp_rw [coe_reciprocalGain hμ, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    exact ENNReal.mul_div_cancel (hμ w) (measure_ne_top μ _)
  simp_rw [gVulnerability, h, iSup_const]

lemma postGVulnerability_reciprocalGain [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) :
    postGVulnerability (reciprocalGain μ) μ κ = (∑ y, ⨆ x, κ x {y}) * ⨅ x, μ {x} := by
  have h (w : α) (y : β) : ∑ x, μ {x} * κ x {y} * reciprocalGain μ w x =
      κ w {y} * ⨅ x, μ {x} := by
    simp_rw [coe_reciprocalGain hμ, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rw [mul_right_comm, ENNReal.mul_div_cancel (hμ w) (measure_ne_top μ _), mul_comm]
  simp_rw [postGVulnerability, h, ← ENNReal.iSup_mul, Finset.sum_mul]

/-- **Theorem 10 of Alvim, Chatzikokolakis, McIver, Morgan, Palamidessi and Smith (CSF 2014)**,
multiplicative form: for a prior `π` of full support, the gain function `g_π` attains the
min-capacity, `L_{g_π}(π, C) = ML(C)`: its leakage ratio is the sum of the column maxima of `C`,
for every channel `C`. -/
theorem gLeakageRatio_reciprocalGain [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) [Nonempty α] :
    gLeakageRatio (reciprocalGain μ) μ κ = ∑ y, ⨆ x, κ x {y} := by
  obtain ⟨x₀, hx₀⟩ := exists_iInf_measure_singleton_eq μ
  rw [gLeakageRatio, postGVulnerability_reciprocalGain hμ, gVulnerability_reciprocalGain hμ, hx₀]
  exact ENNReal.mul_div_cancel_right (hμ x₀) (measure_ne_top μ _)

/-- **Theorem 10 of Alvim et al. (CSF 2014)**: for a prior `π` of full support,
`L_{g_π}(π, C) = ML(C) = log ∑_y max_x C[x, y]` for every channel `C`. -/
theorem gLeakage_reciprocalGain [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) [Nonempty α] :
    gLeakage (reciprocalGain μ) μ κ = Real.log (∑ y, ⨆ x, κ x {y}).toReal := by
  rw [gLeakage, gLeakageRatio_reciprocalGain hμ]

/-- **Theorem 10 of Alvim et al. (CSF 2014)**, consequence (upper bound): for a prior `π` of full
support, no gain function leaks more on `π` than `g_π`, by the Miracle Theorem. The resulting
equality `L_{g_π}(π, C) = L_∀(π, C)` over 1-spanning gain functions is
`multCapacityAtRatio_eq_gLeakageRatio_reciprocalGain`. -/
theorem gLeakageRatio_le_gLeakageRatio_reciprocalGain [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0)
    [Nonempty α] (g : W → α → ℝ≥0) :
    gLeakageRatio g μ κ ≤ gLeakageRatio (reciprocalGain μ) μ κ := by
  rw [gLeakageRatio_reciprocalGain hμ]
  exact ENNReal.div_le_of_le_mul postGVulnerability_le_sum_iSup_mul

end ReciprocalGain


section Kantorovich

/-! ### Additive capacity as a Kantorovich distance

Section VII-B of Alvim, Chatzikokolakis, McIver, Morgan, Palamidessi and Smith (CSF 2014):
over all non-negative 1-spanning gain functions, the largest additive leakage of a channel `C`
on a prior `π` is the Kantorovich distance between the point hyper `[π]` and the hyper
`[π, C]`. We formalize its closed form `∑_{y, x} π[x] |C[x, y] - ∑_{x'} C[x', y] π[x']| / 2`
(Appendix B and Corollary 18), not the Kantorovich and Wasserstein distances on hypers
themselves. -/

/-- A gain function is **1-spanning** if, for each guess, its gains span a range of size at most
`1` (Definition 3 of Alvim et al., CSF 2014). -/
def OneSpanning (g : W → α → ℝ≥0) : Prop :=
  ∀ w x x', |(g w x : ℝ) - g w x'| ≤ 1

/-- The closed form `∑_{y, x} π[x] |C[x, y] - p(y)| / 2`, with `p(y) = ∑_{x'} C[x', y] π[x']`,
of the Kantorovich distance `K([π], [π, C])` between the point hyper `[π]` and the hyper
`[π, C]` (Appendix B and Corollary 18 of Alvim et al., CSF 2014). The distance itself, defined
through the earth-moving metric on hypers, is not formalized; `hyperKantorovich_eq_sum_posterior`
gives the form `∑_y p(y) ‖π - p_{X|y}‖₁ / 2` of the proof of Corollary 18. -/
noncomputable def hyperKantorovich [Fintype α] [Fintype β] (μ : Measure α) (κ : Kernel α β) :
    ℝ :=
  (∑ y, ∑ x, (μ {x}).toReal *
    |(κ x {y}).toReal - ∑ x', (κ x' {y}).toReal * (μ {x'}).toReal|) / 2

/-- If `∑_x d(x) = 0` and `G` varies by at most `1`, then `∑_x d(x) G(x) ≤ ∑_x |d(x)| / 2`. -/
lemma sum_mul_le_half_sum_abs [Fintype α] [Nonempty α] (d G : α → ℝ) (hd : ∑ x, d x = 0)
    (hG : ∀ x x', |G x - G x'| ≤ 1) : ∑ x, d x * G x ≤ (∑ x, |d x|) / 2 := by
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min G
  have h1 : ∑ x, d x * G x = ∑ x, d x * (G x - (G x₀ + 1 / 2)) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd, zero_mul, sub_zero]
  rw [h1, Finset.sum_div]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have hx1 : 0 ≤ G x - G x₀ := sub_nonneg.2 (hx₀ x)
  have hx2 : G x - G x₀ ≤ 1 := (le_abs_self _).trans (hG x x₀)
  have h : |G x - (G x₀ + 1 / 2)| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  calc d x * (G x - (G x₀ + 1 / 2)) ≤ |d x * (G x - (G x₀ + 1 / 2))| := le_abs_self _
    _ = |d x| * |G x - (G x₀ + 1 / 2)| := abs_mul _ _
    _ ≤ |d x| * (1 / 2) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |d x| / 2 := by ring

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]

omit [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
lemma toReal_postGain [IsFiniteMeasure μ] [IsMarkovKernel κ] (w : W) (y : β) :
    (∑ x, μ {x} * κ x {y} * g w x).toReal =
      ∑ x, (μ {x}).toReal * (κ x {y}).toReal * g w x := by
  rw [ENNReal.toReal_sum fun x _ ↦ ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _)
    (measure_ne_top _ _)) ENNReal.coe_ne_top]
  simp [ENNReal.toReal_mul]

omit [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
lemma toReal_priorGain [IsFiniteMeasure μ] (w : W) :
    (∑ x, μ {x} * g w x).toReal = ∑ x, (μ {x}).toReal * g w x := by
  rw [ENNReal.toReal_sum fun x _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.coe_ne_top]
  simp [ENNReal.toReal_mul]

omit [Fintype β] [MeasurableSingletonClass β] in
lemma sum_toReal_measure_singleton [IsProbabilityMeasure μ] : ∑ x, (μ {x}).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _, sum_measure_singleton]
  simp

omit [Fintype α] [MeasurableSingletonClass α] in
lemma sum_toReal_kernel_singleton [IsMarkovKernel κ] (x : α) : ∑ y, (κ x {y}).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _, sum_measure_singleton]
  simp

lemma sum_sum_toReal_mul [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    ∑ y, ∑ x', (κ x' {y}).toReal * (μ {x'}).toReal = 1 := by
  rw [Finset.sum_comm]
  calc ∑ x', ∑ y, (κ x' {y}).toReal * (μ {x'}).toReal = ∑ x', (μ {x'}).toReal :=
        Finset.sum_congr rfl fun x' _ ↦ by
          rw [← Finset.sum_mul, sum_toReal_kernel_singleton, one_mul]
    _ = 1 := sum_toReal_measure_singleton

/-- **Theorem 17 of Alvim et al. (CSF 2014)**, upper bound, in the closed form of Appendix B: the
additive leakage of a channel `C` on a prior `π` under any 1-spanning gain function (with a finite
nonempty set of guesses) is at most `∑_{y, x} π[x] |C[x, y] - p(y)| / 2`. -/
theorem addGLeakage_le_hyperKantorovich [Finite W] [Nonempty W] [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] (hg : OneSpanning g) :
    addGLeakage g μ κ ≤ hyperKantorovich μ κ := by
  have := nonempty_of_isProbabilityMeasure μ
  set p : α → ℝ := fun x ↦ (μ {x}).toReal
  set c : α → β → ℝ := fun x y ↦ (κ x {y}).toReal
  set q : β → ℝ := fun y ↦ ∑ x', c x' y * p x'
  set E : W → β → ℝ≥0∞ := fun w y ↦ ∑ x, μ {x} * κ x {y} * g w x
  set V := (gVulnerability g μ).toReal
  choose wy hwy using fun y ↦ Finite.exists_max fun w ↦ E w y
  have hE (w : W) (y : β) : E w y ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top μ _)
      (measure_ne_top _ _)) ENNReal.coe_ne_top
  have hpost : (postGVulnerability g μ κ).toReal = ∑ y, ∑ x, p x * c x y * g (wy y) x := by
    have h (y : β) : ⨆ w, E w y = E (wy y) y :=
      le_antisymm (iSup_le (hwy y)) (le_iSup (fun w ↦ E w y) _)
    rw [postGVulnerability, ENNReal.toReal_sum fun y _ ↦ (h y).symm ▸ hE _ y]
    exact Finset.sum_congr rfl fun y _ ↦ by rw [h y, toReal_postGain]
  have hp0 (x : α) : 0 ≤ p x := ENNReal.toReal_nonneg
  have hp1 : ∑ x, p x = 1 := sum_toReal_measure_singleton
  have hq0 (y : β) : 0 ≤ q y :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (hp0 x)
  have hV : ∑ y, q y * ∑ x, p x * g (wy y) x ≤ V := by
    calc ∑ y, q y * ∑ x, p x * g (wy y) x ≤ ∑ y, q y * V := by
          refine Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left ?_ (hq0 y)
          rw [← toReal_priorGain]
          exact ENNReal.toReal_mono gVulnerability_ne_top
            (le_iSup (fun w ↦ ∑ x, μ {x} * g w x) (wy y))
      _ = V := by rw [← Finset.sum_mul, sum_sum_toReal_mul, one_mul]
  have hy (y : β) : ∑ x, p x * c x y * g (wy y) x - q y * ∑ x, p x * g (wy y) x ≤
      (∑ x, p x * |c x y - q y|) / 2 := by
    have hd : ∑ x, p x * (c x y - q y) = 0 := by
      rw [show ∑ x, p x * (c x y - q y) = ∑ x, c x y * p x - (∑ x, p x) * q y by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ ↦ by ring, hp1, one_mul]
      exact sub_self _
    have := sum_mul_le_half_sum_abs (fun x ↦ p x * (c x y - q y)) (fun x ↦ (g (wy y) x : ℝ)) hd
      (hg (wy y))
    convert this using 1
    · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    · congr 1
      exact Finset.sum_congr rfl fun x _ ↦ by rw [abs_mul, abs_of_nonneg (hp0 x)]
  rw [addGLeakage, hpost, hyperKantorovich, Finset.sum_div]
  calc ∑ y, ∑ x, p x * c x y * g (wy y) x - V
      ≤ ∑ y, ∑ x, p x * c x y * g (wy y) x - ∑ y, q y * ∑ x, p x * g (wy y) x := by linarith
    _ = ∑ y, (∑ x, p x * c x y * g (wy y) x - q y * ∑ x, p x * g (wy y) x) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ y, (∑ x, p x * |c x y - q y|) / 2 := Finset.sum_le_sum fun y _ ↦ hy y

/-- The sign `±1` attached by a guess `w : α → Bool` to the secret `x`. -/
def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

lemma abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> simp [boolSign]

lemma boolSign_mul_le_abs (b : Bool) (t : ℝ) : boolSign b * t ≤ |t| := by
  cases b
  · simpa [boolSign] using neg_le_abs t
  · simpa [boolSign] using le_abs_self t

/-- The gain function `g(w, x) = 1 + (w(x) - ∑_{x'} π[x'] w(x')) / 2` on the guesses
`w : X → {-1, 1}`, used in the proof of Theorem 17 of Alvim et al. (CSF 2014) to attain the
additive `π`-capacity. Erratum: the proof on p. 317 of the paper prints this gain function with
`+ ∑_{x'} π[x'] w(x')`, which has `V_g[π] = 2` instead of the required `1`; Appendix C of the
paper uses the correct sign `-`, as here. -/
noncomputable def kantorovichGain (μ : Measure α) (w : α → Bool) (x : α) : ℝ≥0 :=
  Real.toNNReal (1 + (boolSign (w x) - ∑ x', (μ {x'}).toReal * boolSign (w x')) / 2)

omit [Fintype β] [MeasurableSingletonClass β] in
lemma coe_kantorovichGain [IsProbabilityMeasure μ] (w : α → Bool) (x : α) :
    (kantorovichGain μ w x : ℝ) =
      1 + (boolSign (w x) - ∑ x', (μ {x'}).toReal * boolSign (w x')) / 2 := by
  refine Real.coe_toNNReal _ ?_
  have h1 : ∑ x', (μ {x'}).toReal * boolSign (w x') ≤ 1 := by
    calc ∑ x', (μ {x'}).toReal * boolSign (w x') ≤ ∑ x', (μ {x'}).toReal := by
          refine Finset.sum_le_sum fun x' _ ↦ ?_
          calc (μ {x'}).toReal * boolSign (w x') ≤ (μ {x'}).toReal * |boolSign (w x')| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) ENNReal.toReal_nonneg
            _ = (μ {x'}).toReal := by rw [abs_boolSign, mul_one]
      _ = 1 := sum_toReal_measure_singleton
  have h2 : -1 ≤ boolSign (w x) := by cases w x <;> norm_num [boolSign]
  linarith

omit [Fintype β] [MeasurableSingletonClass β] in
lemma oneSpanning_kantorovichGain [IsProbabilityMeasure μ] :
    OneSpanning (kantorovichGain μ) := by
  intro w x x'
  rw [coe_kantorovichGain, coe_kantorovichGain]
  have : |boolSign (w x) - boolSign (w x')| ≤ 2 :=
    (abs_sub _ _).trans (by rw [abs_boolSign, abs_boolSign]; norm_num)
  rw [show 1 + (boolSign (w x) - ∑ x'', (μ {x''}).toReal * boolSign (w x'')) / 2 -
      (1 + (boolSign (w x') - ∑ x'', (μ {x''}).toReal * boolSign (w x'')) / 2) =
      (boolSign (w x) - boolSign (w x')) / 2 by ring, abs_div, abs_two]
  linarith

/-- **Theorem 17 of Alvim et al. (CSF 2014)**, attainment: the gain function `kantorovichGain`
(non-negative and 1-spanning) has additive leakage exactly `∑_{y, x} π[x] |C[x, y] - p(y)| / 2`.
-/
theorem addGLeakage_kantorovichGain [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    addGLeakage (kantorovichGain μ) μ κ = hyperKantorovich μ κ := by
  classical
  set p : α → ℝ := fun x ↦ (μ {x}).toReal
  set c : α → β → ℝ := fun x y ↦ (κ x {y}).toReal
  set q : β → ℝ := fun y ↦ ∑ x', c x' y * p x'
  set a : (α → Bool) → ℝ := fun w ↦ ∑ x', p x' * boolSign (w x')
  set e : α → β → ℝ := fun x y ↦ p x * c x y - q y * p x
  set g := kantorovichGain μ
  set E : (α → Bool) → β → ℝ≥0∞ := fun w y ↦ ∑ x, μ {x} * κ x {y} * g w x
  have hp1 : ∑ x, p x = 1 := sum_toReal_measure_singleton
  have hE (w : α → Bool) (y : β) : E w y ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top μ _)
      (measure_ne_top _ _)) ENNReal.coe_ne_top
  -- The prior gain of every guess is `1`.
  have hprior (w : α → Bool) : ∑ x, μ {x} * g w x = 1 := by
    rw [← ENNReal.toReal_eq_one_iff, toReal_priorGain]
    simp_rw [g, coe_kantorovichGain]
    change ∑ x, p x * (1 + (boolSign (w x) - a w) / 2) = 1
    rw [show ∑ x, p x * (1 + (boolSign (w x) - a w) / 2) =
        ∑ x, p x + (∑ x, p x * boolSign (w x) - (∑ x, p x) * a w) / 2 by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by ring, hp1, one_mul]
    change 1 + (a w - a w) / 2 = 1
    simp
  have hV : gVulnerability g μ = 1 := by
    simp_rw [gVulnerability, hprior, iSup_const]
  -- The joint gains, and the guess that attains their maximum.
  have hR (w : α → Bool) (y : β) :
      (E w y).toReal = q y + (∑ x, boolSign (w x) * e x y) / 2 := by
    rw [toReal_postGain]
    simp_rw [g, coe_kantorovichGain]
    change ∑ x, p x * c x y * (1 + (boolSign (w x) - a w) / 2) = _
    have hq : ∑ x, p x * c x y = q y := Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    have lhs : ∑ x, p x * c x y * (1 + (boolSign (w x) - a w) / 2) =
        ∑ x, p x * c x y +
          (∑ x, p x * c x y * boolSign (w x) - (∑ x, p x * c x y) * a w) / 2 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    have rhs : ∑ x, boolSign (w x) * e x y = ∑ x, p x * c x y * boolSign (w x) - q y * a w := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by simp only [e]; ring
    rw [lhs, rhs, hq]
  set wy : β → α → Bool := fun y x ↦ decide (0 ≤ e x y)
  have hRy (y : β) : (E (wy y) y).toReal = q y + (∑ x, |e x y|) / 2 := by
    rw [hR]
    congr 2
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : 0 ≤ e x y
    · simp [wy, h, boolSign, abs_of_nonneg h]
    · simp [wy, h, boolSign, abs_of_neg (not_le.1 h)]
  have hmax (y : β) : ⨆ w, E w y = E (wy y) y := by
    refine le_antisymm (iSup_le fun w ↦ ?_) (le_iSup (fun w ↦ E w y) _)
    rw [← ENNReal.toReal_le_toReal (hE w y) (hE _ y), hR, hRy]
    gcongr with x hx
    exact boolSign_mul_le_abs _ _
  have hpost : (postGVulnerability g μ κ).toReal = 1 + (∑ y, ∑ x, |e x y|) / 2 := by
    rw [postGVulnerability, ENNReal.toReal_sum fun y _ ↦ (hmax y).symm ▸ hE _ y]
    have hq1 : ∑ y, q y = 1 := sum_sum_toReal_mul
    calc ∑ y, (⨆ w, ∑ x, μ {x} * κ x {y} * g w x).toReal = ∑ y, (q y + (∑ x, |e x y|) / 2) :=
          Finset.sum_congr rfl fun y _ ↦ by rw [hmax y, hRy]
      _ = 1 + (∑ y, ∑ x, |e x y|) / 2 := by rw [Finset.sum_add_distrib, hq1, Finset.sum_div]
  rw [addGLeakage, hpost, hV, hyperKantorovich, ENNReal.toReal_one, add_sub_cancel_left]
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [show e x y = p x * (c x y - q y) by simp only [e]; ring, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg]

/-- **Theorem 17 of Alvim et al. (CSF 2014)**, in the closed form of Appendix B: the additive
`π`-capacity `L+_∀(π, C)`, the largest additive leakage of `C` on the prior `π` over all
non-negative 1-spanning gain functions with a finite nonempty set of guesses, is
`∑_{y, x} π[x] |C[x, y] - p(y)| / 2`. The paper identifies this value with the Kantorovich
distance `K([π], [π, C])`, which is not formalized here. -/
theorem isGreatest_addGLeakage [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    IsGreatest {r | ∃ (W : Type u) (_ : Fintype W) (_ : Nonempty W) (g : W → α → ℝ≥0),
      OneSpanning g ∧ addGLeakage g μ κ = r} (hyperKantorovich μ κ) := by
  classical
  refine ⟨⟨α → Bool, inferInstance, inferInstance, kantorovichGain μ,
    oneSpanning_kantorovichGain, addGLeakage_kantorovichGain⟩, ?_⟩
  rintro r ⟨W, _, _, g, hg, rfl⟩
  exact addGLeakage_le_hyperKantorovich hg

end Kantorovich

section Cascade

/-! ### Capacities of cascades and the Dalenius scenario

Section IX of Alvim et al. (CSF 2014): for a cascade `R = S T` of channels `S : X → Y` and
`T : Y → Z`, the leakage of `R` is bounded by that of `S` (Lemma 19) and, on the prior induced on
`Y`, by that of `T` (Lemma 20). The key construction of Lemma 20 transports a gain function `g`
on `X` to the gain function `h(w, y) = E[g(w, X) | Y = y]` on `Y`. -/

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

omit [MeasurableSingletonClass α] in
/-- **Lemma 19 of Alvim et al. (CSF 2014)**, for one prior and one gain function: the additive
leakage of a cascade `R = S T` is at most that of `S`, `L+_g(ρ, R) ≤ L+_g(ρ, S)`. -/
theorem addGLeakage_comp_le [Finite W] [IsFiniteMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] :
    addGLeakage g μ (η ∘ₖ κ) ≤ addGLeakage g μ κ :=
  sub_le_sub_right (ENNReal.toReal_mono postGVulnerability_ne_top
    (postGVulnerability_comp_le η)) _

/-- The gain function `h(w, y) = E[g(w, X) | Y = y]` on the outputs `y` of `κ`, for `X ∼ μ`
(proof of Lemma 20 of Alvim et al., CSF 2014). On outputs of probability zero, where the
paper's formula divides by zero, we use the value `g(w, x₀)`. -/
noncomputable def cascadeGain (g : W → α → ℝ≥0) (μ : Measure α) (κ : Kernel α β) (x₀ : α)
    (w : W) (y : β) : ℝ≥0 :=
  if (κ ∘ₘ μ) {y} = 0 then g w x₀ else ((∑ x, μ {x} * κ x {y} * g w x) / (κ ∘ₘ μ) {y}).toNNReal

omit [Fintype β] [Fintype γ] [MeasurableSingletonClass γ] in
lemma comp_singleton_mul_cascadeGain [IsFiniteMeasure μ] [IsMarkovKernel κ] (x₀ : α) (w : W)
    (y : β) :
    (κ ∘ₘ μ) {y} * cascadeGain g μ κ x₀ w y = ∑ x, μ {x} * κ x {y} * g w x := by
  have hτ : (κ ∘ₘ μ) {y} = ∑ x, κ x {y} * μ {x} := comp_apply_singleton μ κ y
  by_cases h0 : (κ ∘ₘ μ) {y} = 0
  · have hx (x : α) : κ x {y} * μ {x} = 0 :=
      (Finset.sum_eq_zero_iff.1 (hτ ▸ h0)) x (Finset.mem_univ x)
    rw [h0, zero_mul]
    exact (Finset.sum_eq_zero fun x _ ↦ by rw [mul_comm (μ {x}), hx, zero_mul]).symm
  · have hN : ∑ x, μ {x} * κ x {y} * g w x ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top μ _)
        (measure_ne_top _ _)) ENNReal.coe_ne_top
    simp only [cascadeGain, h0, ↓reduceIte]
    rw [ENNReal.coe_toNNReal (ENNReal.div_ne_top hN h0),
      ENNReal.mul_div_cancel h0 (measure_ne_top _ _)]

omit [Fintype γ] [MeasurableSingletonClass γ] in
/-- The prior g-vulnerability is preserved: `V_h(τ) = V_g(ρ)` where `τ` is the law of `Y`. -/
lemma gVulnerability_cascadeGain [IsFiniteMeasure μ] [IsMarkovKernel κ] (x₀ : α) :
    gVulnerability (cascadeGain g μ κ x₀) (κ ∘ₘ μ) = gVulnerability g μ := by
  refine iSup_congr fun w ↦ ?_
  simp_rw [comp_singleton_mul_cascadeGain, sum_postGain_eq]

omit [MeasurableSingletonClass α] in
/-- Writing the posterior g-vulnerability of a cascade through the joint gains on `Y`. -/
lemma postGVulnerability_comp_eq (η : Kernel β γ) :
    postGVulnerability g μ (η ∘ₖ κ) =
      ∑ z, ⨆ w, ∑ y, η y {z} * ∑ x, μ {x} * κ x {y} * g w x := by
  refine Finset.sum_congr rfl fun z _ ↦ iSup_congr fun w ↦ ?_
  simp_rw [kernel_comp_apply_singleton, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-- The posterior g-vulnerability is preserved: `V_h(τ, T) = V_g(ρ, S T)`. -/
lemma postGVulnerability_cascadeGain [IsFiniteMeasure μ] [IsMarkovKernel κ] (x₀ : α)
    (η : Kernel β γ) :
    postGVulnerability (cascadeGain g μ κ x₀) (κ ∘ₘ μ) η = postGVulnerability g μ (η ∘ₖ κ) := by
  rw [postGVulnerability_comp_eq]
  refine Finset.sum_congr rfl fun z _ ↦ iSup_congr fun w ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  rw [mul_right_comm, comp_singleton_mul_cascadeGain, mul_comm]

omit [Fintype β] [Fintype γ] [MeasurableSingletonClass γ] in
/-- The transported gain function is 1-spanning if `g` is: its values for a guess `w` are
averages of the values of `g(w, ·)`. -/
lemma oneSpanning_cascadeGain [IsFiniteMeasure μ] [IsMarkovKernel κ] (x₀ : α)
    (hg : OneSpanning g) : OneSpanning (cascadeGain g μ κ x₀) := by
  have : Nonempty α := ⟨x₀⟩
  intro w y y'
  obtain ⟨xm, hxm⟩ := Finite.exists_min (g w)
  obtain ⟨xM, hxM⟩ := Finite.exists_max (g w)
  have hbounds (y : β) : g w xm ≤ cascadeGain g μ κ x₀ w y ∧ cascadeGain g μ κ x₀ w y ≤ g w xM := by
    by_cases h0 : (κ ∘ₘ μ) {y} = 0
    · simp only [cascadeGain, h0, ↓reduceIte]
      exact ⟨hxm x₀, hxM x₀⟩
    · have hτ : (κ ∘ₘ μ) {y} = ∑ x, μ {x} * κ x {y} := by
        rw [comp_apply_singleton]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
      have key := comp_singleton_mul_cascadeGain (g := g) (μ := μ) (κ := κ) x₀ w y
      have ht : (κ ∘ₘ μ) {y} ≠ ∞ := measure_ne_top _ _
      constructor
      · rw [← ENNReal.coe_le_coe, ← ENNReal.mul_le_mul_iff_right h0 ht, key, hτ, Finset.sum_mul]
        exact Finset.sum_le_sum fun x _ ↦ mul_le_mul_right (ENNReal.coe_le_coe.2 (hxm x)) _
      · rw [← ENNReal.coe_le_coe, ← ENNReal.mul_le_mul_iff_right h0 ht, key, hτ, Finset.sum_mul]
        exact Finset.sum_le_sum fun x _ ↦ mul_le_mul_right (ENNReal.coe_le_coe.2 (hxM x)) _
  have hspan : (g w xM : ℝ) - g w xm ≤ 1 := (le_abs_self _).trans (hg w xM xm)
  obtain ⟨h1, h2⟩ := hbounds y
  obtain ⟨h3, h4⟩ := hbounds y'
  have h1' : (g w xm : ℝ) ≤ cascadeGain g μ κ x₀ w y := by exact_mod_cast h1
  have h2' : (cascadeGain g μ κ x₀ w y : ℝ) ≤ g w xM := by exact_mod_cast h2
  have h3' : (g w xm : ℝ) ≤ cascadeGain g μ κ x₀ w y' := by exact_mod_cast h3
  have h4' : (cascadeGain g μ κ x₀ w y' : ℝ) ≤ g w xM := by exact_mod_cast h4
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- **Lemma 20 of Alvim et al. (CSF 2014)**, for one gain function: for a cascade `R = S T` and a
prior `ρ` on `X`, every 1-spanning gain function `g` on `X` has a 1-spanning counterpart `h` on
`Y` with the same prior and posterior vulnerabilities on the prior `τ = ρ S` of `T`; hence
`L+_g(ρ, R) = L+_h(τ, T)` and `L_g(ρ, R) = L_h(τ, T)`. -/
theorem exists_oneSpanning_cascade [Nonempty α] [IsFiniteMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) (hg : OneSpanning g) :
    ∃ h : W → β → ℝ≥0, OneSpanning h ∧ gVulnerability h (κ ∘ₘ μ) = gVulnerability g μ ∧
      postGVulnerability h (κ ∘ₘ μ) η = postGVulnerability g μ (η ∘ₖ κ) := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  exact ⟨cascadeGain g μ κ x₀, oneSpanning_cascadeGain x₀ hg, gVulnerability_cascadeGain x₀,
    postGVulnerability_cascadeGain x₀ η⟩

omit [Fintype γ] [MeasurableSingletonClass γ] in
/-- The closed form `hyperKantorovich μ κ` of `K([π], [π, C])` is at most `1`. -/
lemma hyperKantorovich_le_one [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    hyperKantorovich μ κ ≤ 1 := by
  set p : α → ℝ := fun x ↦ (μ {x}).toReal
  set c : α → β → ℝ := fun x y ↦ (κ x {y}).toReal
  set q : β → ℝ := fun y ↦ ∑ x', c x' y * p x'
  have hq1 : ∑ y, q y = 1 := sum_sum_toReal_mul
  have hq1' : ∑ y, ∑ x, c x y * p x = 1 := sum_sum_toReal_mul
  have hp1 : ∑ x, p x = 1 := sum_toReal_measure_singleton
  have hq0 (y : β) : 0 ≤ q y :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have h : ∑ y, ∑ x, p x * |c x y - q y| ≤ ∑ y, ∑ x, (c x y * p x + p x * q y) := by
    refine Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
    have hc : 0 ≤ c x y := ENNReal.toReal_nonneg
    have hp : 0 ≤ p x := ENNReal.toReal_nonneg
    calc p x * |c x y - q y| ≤ p x * (c x y + q y) :=
          mul_le_mul_of_nonneg_left (abs_sub_le_iff.2 ⟨by linarith [hq0 y], by linarith⟩) hp
      _ = c x y * p x + p x * q y := by ring
  have h2 : ∑ y, ∑ x, (c x y * p x + p x * q y) = 2 := by
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, hq1', hq1]
    norm_num
  change (∑ y, ∑ x, p x * |c x y - q y|) / 2 ≤ 1
  linarith

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Fintype γ]
  [MeasurableSingletonClass γ] in
lemma hyperKantorovich_nonneg : 0 ≤ hyperKantorovich μ κ :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)) zero_le_two

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Fintype γ]
  [MeasurableSingletonClass γ] in
/-- The closed form of Theorem 17 as the expected distance from the prior to the posteriors, as in
the proof of Corollary 18 of Alvim et al. (CSF 2014): `∑_y p(y) ‖π - p_{X|y}‖₁ / 2`, where
`p_{X|y}(x) = π[x] C[x, y] / p(y)` is the posterior (the half `ℓ₁` distance is the Kantorovich
distance for the discrete metric, Lemma 13). -/
theorem hyperKantorovich_eq_sum_posterior :
    hyperKantorovich μ κ = ∑ y, (∑ x', (κ x' {y}).toReal * (μ {x'}).toReal) *
      (∑ x, |(μ {x}).toReal * (κ x {y}).toReal / ∑ x', (κ x' {y}).toReal * (μ {x'}).toReal -
        (μ {x}).toReal|) / 2 := by
  set p : α → ℝ := fun x ↦ (μ {x}).toReal
  set c : α → β → ℝ := fun x y ↦ (κ x {y}).toReal
  set q : β → ℝ := fun y ↦ ∑ x', c x' y * p x'
  change (∑ y, ∑ x, p x * |c x y - q y|) / 2 = ∑ y, q y * (∑ x, |p x * c x y / q y - p x|) / 2
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have hp (x : α) : 0 ≤ p x := ENNReal.toReal_nonneg
  have hc (x : α) : 0 ≤ c x y := ENNReal.toReal_nonneg
  by_cases hq : q y = 0
  · have h0 (x : α) : c x y * p x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ mul_nonneg (hc x) (hp x)).1 hq x
        (Finset.mem_univ x)
    rw [hq, zero_mul, zero_div]
    refine div_eq_zero_iff.2 (Or.inl (Finset.sum_eq_zero fun x _ ↦ ?_))
    rw [sub_zero, abs_of_nonneg (hc x), mul_comm, h0 x]
  · rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hq0 : 0 ≤ q y := Finset.sum_nonneg fun x _ ↦ mul_nonneg (hc x) (hp x)
    rw [← abs_of_nonneg hq0, ← abs_mul, abs_of_nonneg hq0, mul_sub, mul_div_cancel₀ _ hq,
      show p x * c x y - q y * p x = p x * (c x y - q y) by ring, abs_mul, abs_of_nonneg (hp x)]

/-- **Lemma 19 of Alvim et al. (CSF 2014)**, `π`-capacity form: for a cascade `R = S T`,
`L+_∀(ρ, R) ≤ L+_∀(ρ, S)`, where by Theorem 17 the additive `π`-capacity is given by the closed
form `hyperKantorovich`. -/
theorem hyperKantorovich_comp_le [IsProbabilityMeasure μ] [IsMarkovKernel κ] (η : Kernel β γ)
    [IsMarkovKernel η] :
    hyperKantorovich μ (η ∘ₖ κ) ≤ hyperKantorovich μ κ := by
  classical
  have := nonempty_of_isProbabilityMeasure μ
  rw [← addGLeakage_kantorovichGain (κ := η ∘ₖ κ)]
  exact (addGLeakage_comp_le η).trans
    (addGLeakage_le_hyperKantorovich oneSpanning_kantorovichGain)

/-- **Lemma 20 of Alvim et al. (CSF 2014)** (right-capacity bound for a cascade): for a cascade
`R = S T` and a prior `ρ` on `X`, `L+_∀(ρ, R) ≤ L+_∀(τ, T)` where `τ = ρ S` is the induced
prior on `Y`. The additive `π`-capacities are given by the closed form of Theorem 17. -/
theorem hyperKantorovich_comp_le_comp [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (η : Kernel β γ) [IsMarkovKernel η] :
    hyperKantorovich μ (η ∘ₖ κ) ≤ hyperKantorovich (κ ∘ₘ μ) η := by
  classical
  have := nonempty_of_isProbabilityMeasure μ
  obtain ⟨h, hh, hV, hP⟩ := exists_oneSpanning_cascade (κ := κ) (μ := μ) η
    (oneSpanning_kantorovichGain (μ := μ))
  rw [← addGLeakage_kantorovichGain (κ := η ∘ₖ κ), addGLeakage, ← hV, ← hP]
  exact addGLeakage_le_hyperKantorovich hh

/-- **Corollary 22 of Alvim et al. (CSF 2014)** (Dalenius bound): let `ρ` (the paper's `Π`) be a
joint law of a
secret `X` and the input `Y` of a channel `C : Y → Z`, and let `C* : X × Y → Z` be the channel
that ignores `X` and runs `C` on `Y`. Then `L+_∀(Π, C*) ≤ L+_∀(π, C)`, where `π` is the
`Y`-marginal of `Π`: no correlation of `Y` with `X` lets `C` leak more about `(X, Y)`, measured
additively, than its capacity at `π`. -/
theorem hyperKantorovich_dalenius {ρ : Measure (α × β)} [IsProbabilityMeasure ρ]
    (C : Kernel β γ) [IsMarkovKernel C] :
    hyperKantorovich ρ (C ∘ₖ Kernel.deterministic Prod.snd measurable_snd) ≤
      hyperKantorovich ρ.snd C := by
  have h := hyperKantorovich_comp_le_comp (μ := ρ)
    (κ := Kernel.deterministic Prod.snd measurable_snd) C
  rwa [Measure.deterministic_comp_eq_map, ← Measure.snd] at h

/-- **Corollary 22 of Alvim et al. (CSF 2014)**, for an adversary interested only in the secret
`X`: for every 1-spanning gain function `g` on `X`, extended to `X × Y` by ignoring `Y`, the
additive leakage of `C*` about `X` is at most the additive capacity `L+_∀(π, C)` of `C` at the
`Y`-marginal `π` of `ρ`. -/
theorem addGLeakage_dalenius_le [Finite W] [Nonempty W] {ρ : Measure (α × β)}
    [IsProbabilityMeasure ρ] (C : Kernel β γ) [IsMarkovKernel C] (hg : OneSpanning g) :
    addGLeakage (fun w (p : α × β) ↦ g w p.1) ρ
      (C ∘ₖ Kernel.deterministic Prod.snd measurable_snd) ≤ hyperKantorovich ρ.snd C :=
  (addGLeakage_le_hyperKantorovich fun w p p' ↦ hg w p.1 p'.1).trans
    (hyperKantorovich_dalenius C)

end Cascade

section Capacities

/-! ### Capacities over all priors and gain functions

Following Section V of Alvim et al. (CSF 2014), the gain functions range over the non-negative
1-spanning gain functions `g : W → X → ℝ≥0` with a finite nonempty set of guesses `W`, taken in
the universe of the secrets. -/

universe v

variable {X Y Z : Type v} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z}

/-- The **additive `π`-capacity** `L+_∀(π, C)` (Definition 8 of Alvim et al., CSF 2014). -/
noncomputable def addCapacityAt [Fintype X] [Fintype Y] (μ : Measure X) (κ : Kernel X Y) : ℝ :=
  sSup {r | ∃ (W : Type v) (_ : Fintype W) (_ : Nonempty W) (g : W → X → ℝ≥0),
    OneSpanning g ∧ addGLeakage g μ κ = r}

/-- The **additive capacity** `L+_∀(∀, C)` (Definition 9 of Alvim et al., CSF 2014). -/
noncomputable def addCapacity [Fintype X] [Fintype Y] (κ : Kernel X Y) : ℝ :=
  sSup {r | ∃ (μ : Measure X) (_ : IsProbabilityMeasure μ) (W : Type v) (_ : Fintype W)
    (_ : Nonempty W) (g : W → X → ℝ≥0), OneSpanning g ∧ addGLeakage g μ κ = r}

/-- The **multiplicative `π`-capacity** `L_∀(π, C)`, multiplicative form (Definition 5 of
Alvim et al., CSF 2014). -/
noncomputable def multCapacityAtRatio [Fintype X] [Fintype Y] (μ : Measure X) (κ : Kernel X Y) :
    ℝ≥0∞ :=
  ⨆ (W : Type v) (_ : Fintype W) (_ : Nonempty W) (g : W → X → ℝ≥0) (_ : OneSpanning g),
    gLeakageRatio g μ κ

/-- The **multiplicative capacity** `L_∀(∀, C)`, multiplicative form (Definition 6 of Alvim et
al., CSF 2014). -/
noncomputable def multCapacityRatio [Fintype X] [Fintype Y] (κ : Kernel X Y) : ℝ≥0∞ :=
  ⨆ (μ : Measure X) (_ : IsProbabilityMeasure μ), multCapacityAtRatio μ κ

variable [Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y]
  [Fintype Z] [MeasurableSingletonClass Z] {μ : Measure X} {κ : Kernel X Y}

omit [Fintype Z] [MeasurableSingletonClass Z] in
/-- **Theorem 17 of Alvim et al. (CSF 2014)**: `L+_∀(π, C) = K([π], [π, C])`. -/
theorem addCapacityAt_eq [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    addCapacityAt μ κ = hyperKantorovich μ κ :=
  isGreatest_addGLeakage.csSup_eq

omit [Fintype Z] [MeasurableSingletonClass Z] in
lemma bddAbove_addCapacity_set [IsMarkovKernel κ] :
    BddAbove {r | ∃ (μ : Measure X) (_ : IsProbabilityMeasure μ) (W : Type v) (_ : Fintype W)
      (_ : Nonempty W) (g : W → X → ℝ≥0), OneSpanning g ∧ addGLeakage g μ κ = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨μ, _, W, _, _, g, hg, rfl⟩
  exact (addGLeakage_le_hyperKantorovich hg).trans hyperKantorovich_le_one

omit [Fintype Z] [MeasurableSingletonClass Z] in
lemma hyperKantorovich_le_addCapacity [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    hyperKantorovich μ κ ≤ addCapacity κ := by
  classical
  exact le_csSup bddAbove_addCapacity_set ⟨μ, inferInstance, X → Bool, inferInstance,
    inferInstance, kantorovichGain μ, oneSpanning_kantorovichGain, addGLeakage_kantorovichGain⟩

omit [MeasurableSingletonClass Y] [Fintype Z] [MeasurableSingletonClass Z] in
lemma addCapacity_set_nonempty [Nonempty X] :
    {r | ∃ (μ : Measure X) (_ : IsProbabilityMeasure μ) (W : Type v) (_ : Fintype W)
      (_ : Nonempty W) (g : W → X → ℝ≥0), OneSpanning g ∧ addGLeakage g μ κ = r}.Nonempty := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  exact ⟨_, Measure.dirac x₀, inferInstance, X → Bool, inferInstance, inferInstance,
    kantorovichGain (Measure.dirac x₀), oneSpanning_kantorovichGain, rfl⟩

/-- **Lemma 20 of Alvim et al. (CSF 2014)**, capacity form: `L+_∀(ρ, R) ≤ L+_∀(τ, T)` for a
cascade `R = S T`, where `τ = ρ S`. -/
theorem addCapacityAt_comp_le [IsProbabilityMeasure μ] [IsMarkovKernel κ] (η : Kernel Y Z)
    [IsMarkovKernel η] :
    addCapacityAt μ (η ∘ₖ κ) ≤ addCapacityAt (κ ∘ₘ μ) η := by
  rw [addCapacityAt_eq, addCapacityAt_eq]
  exact hyperKantorovich_comp_le_comp η

/-- **Theorem 21 of Alvim et al. (CSF 2014)** (capacity of cascades): the additive capacity of a
cascade `R = S T` is at most the minimum of the additive capacities of `S` and of `T`. -/
theorem addCapacity_comp_le [Nonempty X] [IsMarkovKernel κ] (η : Kernel Y Z)
    [IsMarkovKernel η] :
    addCapacity (η ∘ₖ κ) ≤ min (addCapacity κ) (addCapacity η) := by
  refine le_min (csSup_le addCapacity_set_nonempty ?_) (csSup_le addCapacity_set_nonempty ?_)
  · rintro r ⟨μ, _, W, _, _, g, hg, rfl⟩
    exact (addGLeakage_le_hyperKantorovich hg).trans
      ((hyperKantorovich_comp_le η).trans hyperKantorovich_le_addCapacity)
  · rintro r ⟨μ, _, W, _, _, g, hg, rfl⟩
    exact (addGLeakage_le_hyperKantorovich hg).trans
      ((hyperKantorovich_comp_le_comp η).trans hyperKantorovich_le_addCapacity)

omit [Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] [Fintype Z]
  [MeasurableSingletonClass Z] in
/-- For a prior of full support, the gain function `g_π` is 1-spanning. -/
lemma oneSpanning_reciprocalGain [DecidableEq X] [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) :
    OneSpanning (reciprocalGain μ) := fun w x x' ↦ by
  have h1 : (reciprocalGain μ w x : ℝ) ≤ 1 := by exact_mod_cast reciprocalGain_le_one hμ w x
  have h2 : (reciprocalGain μ w x' : ℝ) ≤ 1 := by exact_mod_cast reciprocalGain_le_one hμ w x'
  have h3 : (0 : ℝ) ≤ reciprocalGain μ w x := NNReal.coe_nonneg _
  have h4 : (0 : ℝ) ≤ reciprocalGain μ w x' := NNReal.coe_nonneg _
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

omit [MeasurableSingletonClass Y] [Fintype Z] [MeasurableSingletonClass Z] in
/-- **Section VI-B and VI-C of Alvim et al. (CSF 2014)**: the multiplicative capacity of a channel
is its min-capacity, `L_∀(∀, C) = ML(C)`, attained on any full-support prior `π` with the gain
function `g_π` (Theorem 10), and bounded above by the Miracle Theorem. -/
theorem multCapacityRatio_eq [Nonempty X] :
    multCapacityRatio κ = ∑ y, ⨆ x, κ x {y} := by
  classical
  refine le_antisymm (iSup₂_le fun μ _ ↦ iSup_le fun W ↦ iSup₂_le fun _ _ ↦
    iSup₂_le fun g _ ↦ ENNReal.div_le_of_le_mul postGVulnerability_le_sum_iSup_mul) ?_
  set μ := uniformOn (Set.univ : Set X)
  have hμ (x : X) : μ {x} ≠ 0 := by simp [μ, uniformOn_univ]
  rw [← gLeakageRatio_reciprocalGain (κ := κ) hμ]
  exact le_iSup₂_of_le μ inferInstance <| le_iSup_of_le X <| le_iSup₂_of_le inferInstance
    inferInstance <| le_iSup₂_of_le (reciprocalGain μ) (oneSpanning_reciprocalGain hμ) le_rfl

omit [MeasurableSingletonClass X] [MeasurableSingletonClass Y] [Fintype Z]
  [MeasurableSingletonClass Z] in
/-- **Theorem 10 of Alvim et al. (CSF 2014)**: for a prior `π` of full support, the gain function
`g_π` realizes the multiplicative `π`-capacity, `L_{g_π}(π, C) = L_∀(π, C)`. -/
theorem multCapacityAtRatio_eq_gLeakageRatio_reciprocalGain [DecidableEq X] [Nonempty X]
    [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) :
    multCapacityAtRatio μ κ = gLeakageRatio (reciprocalGain μ) μ κ := by
  refine le_antisymm (iSup_le fun W ↦ iSup₂_le fun _ _ ↦ iSup₂_le fun g _ ↦
    gLeakageRatio_le_gLeakageRatio_reciprocalGain hμ g) ?_
  exact le_iSup_of_le X <| le_iSup₂_of_le inferInstance inferInstance <|
    le_iSup₂_of_le (reciprocalGain μ) (oneSpanning_reciprocalGain hμ) le_rfl

/-- **Corollary 23 of Alvim et al. (CSF 2014)**, right-capacity bound: for a cascade `R = S T` and
a prior `ρ`, `L_∀(ρ, R) ≤ L_∀(τ, T)` with `τ = ρ S` (multiplicative form). Erratum: the paper
prints `L_∀(ρ, R) ≤ L_∀(τ, S)`, which is ill-typed (`τ` is a prior on `Y`, the output of `S`);
the intended `T` is stated here, in line with the additive Lemma 20. -/
theorem multCapacityAtRatio_comp_le [IsFiniteMeasure μ] [IsMarkovKernel κ] (η : Kernel Y Z) :
    multCapacityAtRatio μ (η ∘ₖ κ) ≤ multCapacityAtRatio (κ ∘ₘ μ) η := by
  refine iSup_le fun W ↦ iSup₂_le fun _ hW ↦ iSup₂_le fun g hg ↦ ?_
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [gLeakageRatio, show postGVulnerability g μ (η ∘ₖ κ) = 0 by simp [postGVulnerability],
      ENNReal.zero_div]
    exact zero_le
  obtain ⟨h, hh, hV, hP⟩ := exists_oneSpanning_cascade (κ := κ) (μ := μ) η hg
  refine le_iSup_of_le W <| le_iSup₂_of_le inferInstance hW <| le_iSup₂_of_le h hh ?_
  rw [gLeakageRatio, gLeakageRatio, hV, hP]

/-- **Corollary 23 of Alvim et al. (CSF 2014)**, capacity of cascades (multiplicative form): the
multiplicative capacity of a cascade `R = S T` is at most the minimum of those of `S` and `T`. -/
theorem multCapacityRatio_comp_le [Nonempty X] [IsMarkovKernel κ] (η : Kernel Y Z)
    [IsMarkovKernel η] :
    multCapacityRatio (η ∘ₖ κ) ≤ min (multCapacityRatio κ) (multCapacityRatio η) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have := nonempty_of_isProbabilityMeasure (κ x₀)
  rw [multCapacityRatio_eq, multCapacityRatio_eq, multCapacityRatio_eq]
  refine le_min ?_ ?_
  · calc ∑ z, ⨆ x, (η ∘ₖ κ) x {z} ≤ ∑ z, ∑ y, η y {z} * ⨆ x, κ x {y} := by
          refine Finset.sum_le_sum fun z _ ↦ iSup_le fun x ↦ ?_
          rw [kernel_comp_apply_singleton]
          exact Finset.sum_le_sum fun y _ ↦ mul_le_mul_right (le_iSup (fun x ↦ κ x {y}) x) _
      _ = ∑ y, ⨆ x, κ x {y} := by
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]
  · refine Finset.sum_le_sum fun z _ ↦ iSup_le fun x ↦ ?_
    calc (η ∘ₖ κ) x {z} = ∑ y, η y {z} * κ x {y} := kernel_comp_apply_singleton κ η x z
      _ ≤ ∑ y, (⨆ y', η y' {z}) * κ x {y} :=
          Finset.sum_le_sum fun y _ ↦ mul_le_mul_left (le_iSup (fun y ↦ η y {z}) y) _
      _ = ⨆ y, η y {z} := by
          rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]

/-- **Corollary 23 of Alvim et al. (CSF 2014)**, Dalenius bound (multiplicative form): with `ρ`
a joint law of `(X, Y)` and `C* : X × Y → Z` running `C` on `Y`, `L_∀(Π, C*) ≤ L_∀(π, C)` where
`π` is the `Y`-marginal of `ρ`. -/
theorem multCapacityAtRatio_dalenius {ρ : Measure (X × Y)} [IsFiniteMeasure ρ] (C : Kernel Y Z) :
    multCapacityAtRatio ρ (C ∘ₖ Kernel.deterministic Prod.snd measurable_snd) ≤
      multCapacityAtRatio ρ.snd C := by
  have h := multCapacityAtRatio_comp_le (μ := ρ)
    (κ := Kernel.deterministic Prod.snd measurable_snd) C
  rwa [Measure.deterministic_comp_eq_map, ← Measure.snd] at h

/-- **Corollary 22 of Alvim et al. (CSF 2014)** (Dalenius bound), capacity form:
`L+_∀(Π, C*) ≤ L+_∀(π, C)` where `π` is the `Y`-marginal of the joint law `ρ` of `(X, Y)`. -/
theorem addCapacityAt_dalenius {ρ : Measure (X × Y)} [IsProbabilityMeasure ρ] (C : Kernel Y Z)
    [IsMarkovKernel C] :
    addCapacityAt ρ (C ∘ₖ Kernel.deterministic Prod.snd measurable_snd) ≤
      addCapacityAt ρ.snd C := by
  rw [addCapacityAt_eq, addCapacityAt_eq]
  exact hyperKantorovich_dalenius C

end Capacities

end InformationTheory
