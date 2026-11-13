/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DPHamming.Basic
public import InfoLeakage.FDP.Basic
public import InfoLeakage.RenyiInfinity.Basic
public import Mathlib.InformationTheory.Hamming

/-!
# Max-information

This file formalizes, for finite alphabets, the pure (`β = 0`) max-information of

* C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, *Generalization in adaptive
  data analysis and holdout reuse*, NeurIPS 2015,
  [arXiv:1506.02629](https://arxiv.org/abs/1506.02629); result numbers follow arXiv v2.

For jointly distributed `(X, Y)`, the max-information is
`I∞(X; Y) = D∞((X, Y) ‖ X × Y) = log max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y))`, where `X × Y` has
the product law `P_X × P_Y`. An algorithm (channel) `A` has max-information `k` if
`I∞(S; A(S)) ≤ k` for every distribution of its input `S`. Here `X ∼ μ` and `Y` is the output of a
channel `κ : Kernel α β`, so that `P_XY = μ ⊗ₘ κ` and `P_X × P_Y = μ.prod (κ ∘ₘ μ)`, and logarithms
are natural (nats; the paper uses bits).

## Main definitions

* `expMaxInformation μ κ`: `max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y))`, in `ℝ≥0∞`; it is
  `expRenyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))`.
* `maxInformation μ κ`: the max-information `I∞(X; Y) = D∞(P_XY ‖ P_X × P_Y)`, its logarithm, in
  `EReal` (it is `renyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))`).
* `HasMaxInformation A k`: `I∞(S; A(S)) ≤ k` for every input distribution.

## Main statements

* `expMaxInformation_eq_iSup`, `expMaxInformation_le_iff`: `I∞(X; Y) ≤ k` iff
  `D∞(P_{Y|X=x} ‖ P_Y) ≤ k` for every `x` in the support of `X`, i.e.
  `P_{Y|X}(y | x) ≤ e^k P_Y(y)`.
* `maxInformation_le_iff_forall_set`: `I∞(X; Y) ≤ k` iff `P[(X, Y) ∈ O] ≤ e^k P[X × Y ∈ O]` for
  every event `O`; `measure_compProd_le_of_maxInformation_le`:
  `P[(X, Y) ∈ O] ≤ e^k max_y P[(X, y) ∈ O]`.
* `maxInformation_comp_le`: post-processing.
* `hasMaxInformation_iff`, `hasMaxInformation_iff_expRenyiDivInf_le`:
  `I∞(A) = max_{S, S'} D∞(A(S) ‖ A(S'))`.
* `HasMaxInformation.snd_compProd`: adaptive composition.
* `hasMaxInformation_of_isEpsDeltaDP`, `maxInformation_le_of_isEpsDeltaDP`: an `ε`-differentially
  private algorithm on `n`-record datasets has max-information at most `ε n`.
* Bridges: `maxLeakage_le_maxInformation` (`L(X → Y) ≤ I∞(X; Y)`),
  `mutualInfo_compProd_le_maxInformation` (`I(X; Y) ≤ I∞(X; Y)`),
  `hasMaxInformation_iff_isLocalDP` (`ε`-local DP iff max-information `ε`) and
  `maxInformation_le_of_isLocalDP`.

## Paper → Lean (Dwork et al., arXiv v2)

* Definition 10 (`β = 0`) → `expMaxInformation`, `maxInformation`; the remarks after it →
  `expMaxInformation_eq_iSup`, `expMaxInformation_le_iff`, and (mutual information)
  `mutualInfo_compProd_le_maxInformation`.
* Definition 11 (`β = 0`) → `HasMaxInformation`.
* Lemma 12 → `hasMaxInformation_iff`, `hasMaxInformation_iff_expRenyiDivInf_le` (one direction:
  `hasMaxInformation_of_forall_le`).
* Theorem 13 (`β = 0`), with its converse → `expMaxInformation_le_iff_forall_set`,
  `maxInformation_le_iff_forall_set`; its "in particular" clause →
  `measure_compProd_le_of_maxInformation_le`.
* Lemma 14 (`β₁ = β₂ = 0`) → `HasMaxInformation.snd_compProd`, where the adaptive composition
  `C(S) = B(S, A(S))` is `(A ⊗ₖ B).snd` and `B(·, y)` is `B.sectL y`.
* Lemma 16 (`β = 0`) → `expMaxInformation_comp_le`, `maxInformation_comp_le`.
* Theorem 19 → `hasMaxInformation_of_isEpsDeltaDP` (datasets `ι → 𝒳`, bound `ε |ι|`) and
  `maxInformation_le_of_isEpsDeltaDP` (datasets `Fin n → 𝒳`, bound `ε n`); the group privacy step
  is `IsEpsDeltaDP.measureReal_le_exp_mul_hammingDist`.
* Lemma 12 of Esposito, Gastpar and Issa (arXiv:1912.01439v3) → `maxLeakage_le_maxInformation`.

Not formalized: approximate max-information (`β > 0`) and everything that needs it (the `β > 0`
parts of Definitions 10–11, Theorem 13, Lemmas 14 and 16; Theorem 15, the iteration of Lemma 14;
Theorem 17 and Lemma 18 on description length; Theorem 20 on i.i.d. datasets), the symmetry
`I∞(X; Y) = I∞(Y; X)`, and Sections 4–5 (Thresholdout).

## Implementation notes

* Scope. `expMaxInformation` is a supremum over singletons, so it (and `maxInformation`,
  `HasMaxInformation`) has its probabilistic meaning only when the laws involved are purely
  atomic; this file gives that meaning for finite alphabets with measurable singletons. Several
  declarations nevertheless leave the output type unrestricted (e.g. `expMaxInformation_le_iff`,
  `expMaxInformation_comp_le`, `hasMaxInformation_iff`, `hasMaxInformation_iff_isLocalDP`,
  `HasMaxInformation.snd_compProd`, `hasMaxInformation_of_isEpsDeltaDP`). They remain true, but
  for a diffuse output law every singleton ratio is `0 / 0 = 0`, so `maxInformation = ⊥` and
  `HasMaxInformation A k` holds vacuously, and the singleton-based `IsLocalDP` need not mean
  event-based local differential privacy. Read them as statements about max-information only when
  the output alphabet is finite (or, more generally, the laws are purely atomic).
* Differential privacy is the library's `IsEpsDeltaDP M Adj ε 0`, with `M : Kernel (ι → 𝒳) Z`
  and `Adj S S'` the relation `hammingDist S S' = 1` (the datasets differ in exactly one record),
  as in Definition 2 of the paper.
* `maxInformation` takes values in `EReal`, through `ENNReal.log`, so that an infinite ratio is
  `⊤` rather than a junk value. On finite alphabets and for a probability measure `μ` the ratio
  `expMaxInformation μ κ` lies in `[1, ∞)` (`one_le_expMaxInformation`,
  `expMaxInformation_ne_top`), and `maxInformation μ κ` is a nonnegative real number
  (`maxInformation_eq_coe`). The criterion `maxInformation_le_iff` holds with no hypothesis.
* Lemma 12 is proved as in the paper: the direction `⟸` averages over the input, the direction
  `⟹` uses the inputs `t δ_S + (1 - t) δ_{S'}` and lets `t → 0`.

## Notes on the paper

* Proof of Theorem 19 (Section 3.1.2, p. 13 of arXiv v2): "By Lemma 3 we obtain the claim" should
  cite Lemma 12 (Theorem 3 is the composition theorem for differential privacy). The theorem is
  true (`hasMaxInformation_of_isEpsDeltaDP`).
* Proof of Lemma 14 (Section 3, pp. 10–11 of arXiv v2): a published proof gap. The lemma is true
  for `β₁ = β₂ = 0` and is proved here (`HasMaxInformation.snd_compProd`, via Lemma 12 rather than
  the paper's argument). The paper's proof fixes one distribution `D` of the dataset `𝐒` and uses
  the hypotheses only at `D` and, trivially, at point masses. Its final equality,
  `∑_{S, y} P[S × B(S, y) ∈ Q] · P[𝐒 = S] · P[A(𝐒) = y] = P[𝐒 × B(𝐒, A(𝐒)) ∈ Q]`, replaces the
  law of `(𝐒, B(𝐒, Y))`, with `𝐒 ∼ D` and `Y ∼ P_{A(𝐒)}` independent, by the law of
  `(𝐒, B(𝐒', A(𝐒')))`, with `𝐒, 𝐒'` independent copies; these differ in general. Read with this
  fixed-prior quantification (hypotheses and conclusion at one `D`), the last step would prove a
  statement that is false, already for `β₁ = β₂ = 0`:
  `MaxInformation.exists_not_maxInformation_snd_compProd_le` (for `𝐒` on `{0, 1, 2}` with
  probabilities `1/10, 9/20, 9/20` and the deterministic algorithms `A(S) = [S = 2]`,
  `B(S, 0) = [S = 1]`, `B(S, 1) = 1`, the hypotheses hold at `D` with `k₁ = k₂ = log (20/9)`, while
  `C(S) = B(S, A(S)) = [S ≠ 0]` has `I∞(𝐒; C(𝐒)) = log 10 > 2 log (20/9)`). The counterexample
  refutes only this fixed-prior version, not Lemma 14, whose hypotheses quantify over every prior.
  Nothing is claimed here about `β > 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β}

/-! ### Definitions -/

/-- The exponential `max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y))` of the max-information between an
input `X ∼ μ` and the output `Y` of the channel `κ`, in `ℝ≥0∞`. It is the exponential of
`D∞(P_XY ‖ P_X × P_Y)`, with `P_XY = μ ⊗ₘ κ` and `P_X × P_Y = μ.prod (κ ∘ₘ μ)`. The supremum
ranges over singletons, so this is that exponential only when both laws are purely atomic, e.g.
for countable alphabets with measurable singletons; its probabilistic interpretation below is for
finite alphabets. Some results below leave the output type unrestricted; for a diffuse output law
every ratio is `0 / 0 = 0` and this is `0` (see the scope note in the module docstring). -/
noncomputable def expMaxInformation (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  expRenyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))

/-- The **max-information** `I∞(X; Y) = D∞((X, Y) ‖ X × Y) = log max_{x, y} P_XY(x, y) /
(P_X(x) P_Y(y))` (Definition 10 of Dwork et al., in nats) between an input `X ∼ μ` and the output
`Y` of the channel `κ`: the Rényi divergence `renyiDivInf` of order `∞` between the joint law and
the product of the marginals, with values in `EReal`. The same scope remark as for
`expMaxInformation` applies. On finite alphabets and for a probability measure `μ` it is a
nonnegative real number (`maxInformation_nonneg`, `maxInformation_eq_coe`). -/
noncomputable def maxInformation (μ : Measure α) (κ : Kernel α β) : EReal :=
  renyiDivInf (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))

lemma maxInformation_eq_log : maxInformation μ κ = ENNReal.log (expMaxInformation μ κ) := rfl

/-- `I∞(X; Y) ≤ k` iff `max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y)) ≤ e^k`. -/
lemma maxInformation_le_iff {k : ℝ} :
    maxInformation μ κ ≤ k ↔ expMaxInformation μ κ ≤ ENNReal.ofReal (exp k) := by
  rw [maxInformation_eq_log, ← ENNReal.log_le_log_iff, ENNReal.log_ofReal_of_pos (exp_pos k),
    Real.log_exp]

section Finite

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- `P_{Y|X}(y | x) P_X(x) ≤ P_Y(y)`. -/
lemma MaxInformation.mul_le_comp_apply_singleton (μ : Measure α) (κ : Kernel α β) (x : α) (y : β) :
    κ x {y} * μ {x} ≤ (κ ∘ₘ μ) {y} := by
  have := Fintype.ofFinite α
  rw [comp_apply_singleton]
  exact Finset.single_le_sum (f := fun x ↦ κ x {y} * μ {x}) (fun _ _ ↦ zero_le)
    (Finset.mem_univ x)

/-- The max-information as the largest divergence `D∞(P_{Y|X=x} ‖ P_Y)` over the support of `X`
(Dwork et al., after Definition 10): `max_{x ∈ supp μ} max_y κ x {y} / P_Y(y)`. -/
theorem expMaxInformation_eq_iSup [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    expMaxInformation μ κ = ⨆ (x) (_ : μ {x} ≠ 0), expRenyiDivInf (κ x) (κ ∘ₘ μ) := by
  rw [expMaxInformation, expRenyiDivInf, iSup_prod]
  refine iSup_congr fun x ↦ ?_
  by_cases hx : μ {x} = 0
  · simp [hx, compProd_singleton]
  rw [iSup_pos hx, expRenyiDivInf]
  refine iSup_congr fun y ↦ ?_
  rw [compProd_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm (μ {x}),
    ENNReal.mul_div_mul_right _ _ hx (measure_ne_top _ _)]

/-- **Pointwise form of a max-information bound** (Definition 10 of Dwork et al., with `β = 0`):
`I∞(X; Y) ≤ log c` iff `P_{Y|X}(y | x) ≤ c P_Y(y)` for every `x` in the support of `X` and
every `y`. -/
theorem expMaxInformation_le_iff [IsFiniteMeasure μ] [IsMarkovKernel κ] {c : ℝ≥0∞} :
    expMaxInformation μ κ ≤ c ↔ ∀ x, μ {x} ≠ 0 → ∀ y, κ x {y} ≤ c * (κ ∘ₘ μ) {y} := by
  simp only [expMaxInformation_eq_iSup, expRenyiDivInf, iSup_le_iff]
  refine forall₂_congr fun x hx ↦ forall_congr' fun y ↦ ?_
  by_cases hy : (κ ∘ₘ μ) {y} = 0
  · have h0 : κ x {y} = 0 := by
      have h := MaxInformation.mul_le_comp_apply_singleton μ κ x y
      rw [hy, nonpos_iff_eq_zero, mul_eq_zero] at h
      exact h.resolve_right hx
    simp [hy, h0]
  · exact ENNReal.div_le_iff_le_mul (Or.inl hy) (Or.inl (measure_ne_top _ _))

lemma le_expMaxInformation_mul [IsFiniteMeasure μ] [IsMarkovKernel κ] {x : α} (hx : μ {x} ≠ 0)
    (y : β) : κ x {y} ≤ expMaxInformation μ κ * (κ ∘ₘ μ) {y} :=
  expMaxInformation_le_iff.1 le_rfl x hx y

/-- On finite alphabets the max-information is finite: every ratio
`P_XY(x, y) / (P_X(x) P_Y(y))` is at most `1 / P_X(x)`. -/
lemma expMaxInformation_ne_top [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    expMaxInformation μ κ ≠ ∞ := by
  have := Fintype.ofFinite α
  set c := ∑ x, (μ {x})⁻¹ * (if μ {x} = 0 then 0 else 1)
  have hc : c ≠ ∞ := by
    refine ENNReal.sum_ne_top.2 fun x _ ↦ ?_
    by_cases hx : μ {x} = 0 <;> simp [hx]
  refine ne_top_of_le_ne_top hc (expMaxInformation_le_iff.2 fun x hx y ↦ ?_)
  calc κ x {y} = (μ {x})⁻¹ * (κ x {y} * μ {x}) := by
        rw [mul_comm (κ x {y}), ← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top _ _),
          one_mul]
    _ ≤ (μ {x})⁻¹ * (if μ {x} = 0 then 0 else 1) * (κ ∘ₘ μ) {y} := by
        simp only [hx, ↓reduceIte, mul_one]
        exact mul_le_mul_right (MaxInformation.mul_le_comp_apply_singleton μ κ x y) _
    _ ≤ c * (κ ∘ₘ μ) {y} := by
        refine mul_le_mul_left ?_ _
        exact Finset.single_le_sum (f := fun x ↦ (μ {x})⁻¹ * (if μ {x} = 0 then 0 else 1))
          (fun _ _ ↦ zero_le) (Finset.mem_univ x)

/-- **Event form of a max-information bound** (Theorem 13 of Dwork et al. with `β = 0`, together
with its converse): `I∞(X; Y) ≤ log c` iff `P[(X, Y) ∈ O] ≤ c P[X × Y ∈ O]` for every event
`O ⊆ 𝒳 × 𝒴`, where `X × Y` has the product law `P_X × P_Y`. -/
theorem expMaxInformation_le_iff_forall_set [Finite β] [IsFiniteMeasure μ] [IsMarkovKernel κ]
    {c : ℝ≥0∞} :
    expMaxInformation μ κ ≤ c ↔ ∀ O : Set (α × β), (μ ⊗ₘ κ) O ≤ c * μ.prod (κ ∘ₘ μ) O := by
  refine ⟨fun h O ↦ ?_, fun h ↦ iSup_le fun p ↦ ENNReal.div_le_of_le_mul (h {p})⟩
  have hp (p : α × β) : (μ ⊗ₘ κ) {p} ≤ c * μ.prod (κ ∘ₘ μ) {p} := by
    obtain ⟨x, y⟩ := p
    rw [compProd_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod]
    by_cases hx : μ {x} = 0
    · simp [hx]
    calc κ x {y} * μ {x} ≤ c * (κ ∘ₘ μ) {y} * μ {x} :=
          mul_le_mul_left (expMaxInformation_le_iff.1 h x hx y) _
      _ = c * (μ {x} * (κ ∘ₘ μ) {y}) := by ring
  classical
  have := Fintype.ofFinite (α × β)
  rw [← Set.coe_toFinset O, ← sum_measure_singleton, ← sum_measure_singleton, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ ↦ hp p

variable [Finite β] [IsProbabilityMeasure μ] [IsMarkovKernel κ]

/-- The max-information is nonnegative: `1 ≤ max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y))`. -/
lemma one_le_expMaxInformation : 1 ≤ expMaxInformation μ κ := by
  have h := expMaxInformation_le_iff_forall_set.1 (le_refl (expMaxInformation μ κ)) Set.univ
  simpa using h

lemma maxInformation_nonneg : 0 ≤ maxInformation μ κ :=
  ENNReal.zero_le_log_iff.2 one_le_expMaxInformation

/-- On finite alphabets and for a probability measure `μ`, the max-information is the real number
`log max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y))`. -/
lemma maxInformation_eq_coe :
    maxInformation μ κ = (Real.log (expMaxInformation μ κ).toReal : ℝ) := by
  rw [maxInformation_eq_log, ENNReal.log_pos_real
    (zero_lt_one.trans_le one_le_expMaxInformation).ne' expMaxInformation_ne_top]

/-- **Event form of a max-information bound** (Theorem 13 of Dwork et al. with `β = 0`, and its
converse), in nats: `I∞(X; Y) ≤ k` iff `P[(X, Y) ∈ O] ≤ e^k P[X × Y ∈ O]` for every event `O`. -/
theorem maxInformation_le_iff_forall_set {k : ℝ} :
    maxInformation μ κ ≤ k ↔
      ∀ O : Set (α × β), (μ ⊗ₘ κ) O ≤ ENNReal.ofReal (exp k) * μ.prod (κ ∘ₘ μ) O := by
  rw [maxInformation_le_iff, expMaxInformation_le_iff_forall_set]

/-- The product law of an event `O` is at most the largest probability of one of its sections:
`P[X × Y ∈ O] ≤ max_y P[(X, y) ∈ O]`. -/
lemma MaxInformation.prod_apply_le_iSup (O : Set (α × β)) :
    μ.prod (κ ∘ₘ μ) O ≤ ⨆ y, μ {x | (x, y) ∈ O} := by
  rw [Measure.prod_apply_symm O.toFinite.measurableSet]
  calc ∫⁻ y, μ ((fun x ↦ (x, y)) ⁻¹' O) ∂(κ ∘ₘ μ)
      ≤ ∫⁻ _, ⨆ y, μ {x | (x, y) ∈ O} ∂(κ ∘ₘ μ) :=
        lintegral_mono fun y ↦ le_iSup (fun y ↦ μ {x | (x, y) ∈ O}) y
    _ = ⨆ y, μ {x | (x, y) ∈ O} := by simp

/-- **Theorem 13 of Dwork et al.**, second inequality ("in particular"), with `β = 0`: if
`I∞(X; Y) ≤ k`, then `P[(X, Y) ∈ O] ≤ e^k max_y P[(X, y) ∈ O]` for every event `O`. -/
theorem measure_compProd_le_of_maxInformation_le {k : ℝ} (h : maxInformation μ κ ≤ k)
    (O : Set (α × β)) : (μ ⊗ₘ κ) O ≤ ENNReal.ofReal (exp k) * ⨆ y, μ {x | (x, y) ∈ O} :=
  (maxInformation_le_iff_forall_set.1 h O).trans
    (mul_le_mul_right (MaxInformation.prod_apply_le_iSup O) _)

end Finite

/-! ### Post-processing -/

section PostProcessing

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ] [IsMarkovKernel κ]

/-- **Post-processing** (Lemma 16 of Dwork et al., with `β = 0`), multiplicative form: passing the
output through a further channel `η` cannot increase the max-information. The output type `γ`
of `η` is not assumed finite; see the scope note in the module docstring. -/
theorem expMaxInformation_comp_le [IsFiniteMeasure μ] (η : Kernel β γ) [IsMarkovKernel η] :
    expMaxInformation μ (η ∘ₖ κ) ≤ expMaxInformation μ κ := by
  have := Fintype.ofFinite β
  refine expMaxInformation_le_iff.2 fun x hx z ↦ ?_
  rw [kernel_comp_apply_singleton, ← Measure.comp_assoc, comp_apply_singleton, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  calc η y {z} * κ x {y} ≤ η y {z} * (expMaxInformation μ κ * (κ ∘ₘ μ) {y}) :=
        mul_le_mul_right (le_expMaxInformation_mul hx y) _
    _ = expMaxInformation μ κ * (η y {z} * (κ ∘ₘ μ) {y}) := by ring

/-- **Post-processing** (Lemma 16 of Dwork et al., with `β = 0`): for every input distribution,
`I∞(X; B(A(X))) ≤ I∞(X; A(X))`. -/
theorem maxInformation_comp_le [IsFiniteMeasure μ] (η : Kernel β γ) [IsMarkovKernel η] :
    maxInformation μ (η ∘ₖ κ) ≤ maxInformation μ κ := by
  rw [maxInformation_eq_log, maxInformation_eq_log, ENNReal.log_le_log_iff]
  exact expMaxInformation_comp_le η

end PostProcessing

/-! ### Max-information of an algorithm -/

/-- An algorithm (channel) `A` **has max-information `k`** if `I∞(S; A(S)) ≤ k` for every
distribution of the input `S` (Definition 11 of Dwork et al., with `β = 0`). It is meant for
finite alphabets with measurable singletons, where `maxInformation` is the max-information; for a
diffuse output law it holds vacuously (`maxInformation = ⊥`). -/
def HasMaxInformation (A : Kernel α β) (k : ℝ) : Prop :=
  ∀ μ : Measure α, IsProbabilityMeasure μ → maxInformation μ A ≤ k

namespace MaxInformation

open Filter Topology in
/-- If `a ≤ c (t a + (1 - t) b)` for all `t ∈ (0, 1)`, then `a ≤ c b` (let `t → 0`). -/
lemma le_of_forall_le_mix {a b c : ℝ} (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a ≤ c * (t * a + (1 - t) * b)) :
    a ≤ c * b := by
  have hlim : Tendsto (fun t : ℝ ↦ c * (t * a + (1 - t) * b)) (𝓝[>] 0) (𝓝 (c * b)) := by
    have hc : Continuous fun t : ℝ ↦ c * (t * a + (1 - t) * b) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) h)

end MaxInformation

section Algorithm

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {A : Kernel α β} [IsMarkovKernel A] {k : ℝ}

/-- One direction of Lemma 12 of Dwork et al.: if `P[A(S) = y] ≤ e^k P[A(S') = y]` for all inputs
`S, S'`, then `A` has max-information `k`. The output type is not assumed finite; see the scope
note in the module docstring. -/
theorem hasMaxInformation_of_forall_le
    (h : ∀ S S' y, A S {y} ≤ ENNReal.ofReal (exp k) * A S' {y}) : HasMaxInformation A k := by
  have := Fintype.ofFinite α
  intro μ hμ
  rw [maxInformation_le_iff, expMaxInformation_le_iff]
  intro x _ y
  calc A x {y} = ∑ S', A x {y} * μ {S'} := by
        rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
    _ ≤ ∑ S', ENNReal.ofReal (exp k) * A S' {y} * μ {S'} :=
        Finset.sum_le_sum fun S' _ ↦ mul_le_mul_left (h x S' y) _
    _ = ENNReal.ofReal (exp k) * (A ∘ₘ μ) {y} := by
        rw [comp_apply_singleton, Finset.mul_sum]
        simp_rw [mul_assoc]

/-- **Lemma 12 of Dwork et al.** (with `β = 0`), pointwise form: an algorithm has max-information
`k` iff `P[A(S) = y] ≤ e^k P[A(S') = y]` for all inputs `S, S'` and outputs `y`. The output type
is not assumed finite; see the scope note in the module docstring. -/
theorem hasMaxInformation_iff :
    HasMaxInformation A k ↔ ∀ S S' y, A S {y} ≤ ENNReal.ofReal (exp k) * A S' {y} := by
  refine ⟨fun h S S' y ↦ ?_, hasMaxInformation_of_forall_le⟩
  set a := (A S {y}).toReal
  set b := (A S' {y}).toReal
  have ha : A S {y} = ENNReal.ofReal a := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hb : A S' {y} = ENNReal.ofReal b := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [ha, hb, ← ENNReal.ofReal_mul (exp_pos k).le]
  refine ENNReal.ofReal_le_ofReal (MaxInformation.le_of_forall_le_mix fun t ht ↦ ?_)
  -- The input law `t δ_S + (1 - t) δ_{S'}`.
  set μ : Measure α := ENNReal.ofReal t • Measure.dirac S + ENNReal.ofReal (1 - t) •
    Measure.dirac S'
  have : IsProbabilityMeasure μ := ⟨by
    simp [μ, ← ENNReal.ofReal_add ht.1.le (sub_nonneg.2 ht.2.le)]⟩
  have hS : μ {S} ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (le_self_add : ENNReal.ofReal t • Measure.dirac S {S} ≤ _)).ne'
    simpa using ht.1
  have hY : (A ∘ₘ μ) {y} = ENNReal.ofReal (t * a + (1 - t) * b) := by
    rw [Measure.comp_add, Measure.comp_smul, Measure.comp_smul, add_apply, smul_apply,
      smul_apply, Measure.dirac_bind A.measurable, Measure.dirac_bind A.measurable, ha, hb,
      smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_mul ht.1.le,
      ← ENNReal.ofReal_mul (sub_nonneg.2 ht.2.le), ← ENNReal.ofReal_add
        (mul_nonneg ht.1.le ENNReal.toReal_nonneg)
        (mul_nonneg (sub_nonneg.2 ht.2.le) ENNReal.toReal_nonneg)]
  have h' := (expMaxInformation_le_iff.1 ((maxInformation_le_iff).1 (h μ this))) S hS y
  rw [hY, ha, ← ENNReal.ofReal_mul (exp_pos k).le] at h'
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (exp_pos k).le
    (add_nonneg (mul_nonneg ht.1.le ENNReal.toReal_nonneg)
      (mul_nonneg (sub_nonneg.2 ht.2.le) ENNReal.toReal_nonneg)))).1 h'

/-- **Lemma 12 of Dwork et al.** (with `β = 0`): an algorithm has max-information `k` iff
`D∞(A(S) ‖ A(S')) ≤ k` for all inputs `S, S'`, i.e. `I∞(A) = max_{S, S'} D∞(A(S) ‖ A(S'))`.
The output type is not assumed finite; see the scope note in the module docstring. -/
theorem hasMaxInformation_iff_expRenyiDivInf_le :
    HasMaxInformation A k ↔ ∀ S S', expRenyiDivInf (A S) (A S') ≤ ENNReal.ofReal (exp k) := by
  rw [hasMaxInformation_iff]
  refine forall₂_congr fun S S' ↦ ?_
  rw [expRenyiDivInf, iSup_le_iff]
  exact forall_congr' fun y ↦ (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
    (Or.inl (measure_ne_top _ _))).symm

omit [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- `C(S) = B(S, A(S))`, the adaptive composition `(A ⊗ₖ B).snd`, as a finite sum:
`P[C(S) = z] = ∑_y P[A(S) = y] P[B(S, y) = z]`. -/
lemma MaxInformation.snd_compProd_apply_singleton [Fintype β] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] (A : Kernel α β) [IsSFiniteKernel A] (B : Kernel (α × β) γ)
    [IsSFiniteKernel B] (S : α) (z : γ) :
    (A ⊗ₖ B).snd S {z} = ∑ y, A S {y} * B (S, y) {z} := by
  rw [Kernel.snd_apply' _ _ (measurableSet_singleton z),
    Kernel.compProd_apply (measurable_snd (measurableSet_singleton z)), lintegral_fintype]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [mul_comm]
  rfl

/-- **Lemma 14 of Dwork et al.** (adaptive composition, with `β₁ = β₂ = 0`): if `A` has
max-information `k₁` and `B(·, y)` has max-information `k₂` for every `y`, then the adaptive
composition `C(S) = B(S, A(S))`, i.e. `(A ⊗ₖ B).snd`, has max-information `k₁ + k₂`. The output
type `γ` of `B` is not assumed finite; the conclusion is a statement about max-information only for
finite (more generally, purely atomic) outputs (see the scope note in the module docstring). -/
theorem HasMaxInformation.snd_compProd [Finite β] [MeasurableSingletonClass γ]
    {B : Kernel (α × β) γ} [IsMarkovKernel B] {k₁ k₂ : ℝ} (hA : HasMaxInformation A k₁)
    (hB : ∀ y, HasMaxInformation (B.sectL y) k₂) :
    HasMaxInformation (A ⊗ₖ B).snd (k₁ + k₂) := by
  have := Fintype.ofFinite β
  rw [hasMaxInformation_iff] at hA ⊢
  simp_rw [hasMaxInformation_iff, Kernel.sectL_apply] at hB
  intro S S' z
  rw [MaxInformation.snd_compProd_apply_singleton, MaxInformation.snd_compProd_apply_singleton,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  calc A S {y} * B (S, y) {z}
      ≤ (ENNReal.ofReal (exp k₁) * A S' {y}) * (ENNReal.ofReal (exp k₂) * B (S', y) {z}) :=
        mul_le_mul' (hA S S' y) (hB y S S' z)
    _ = ENNReal.ofReal (exp (k₁ + k₂)) * (A S' {y} * B (S', y) {z}) := by
        rw [exp_add, ENNReal.ofReal_mul (exp_pos _).le]
        ring

/-- A channel has max-information `ε` iff it is `ε`-locally differentially private
(`IsLocalDP`, every pair of inputs being neighbours); this is Lemma 12 of Dwork et al. The output
type is not assumed finite. `IsLocalDP` here compares singleton masses, so for a finite output
alphabet it is `ε`-local differential privacy, but for a diffuse output law both sides hold
vacuously and it need not imply event-based local DP (see the scope note in the module
docstring). -/
theorem hasMaxInformation_iff_isLocalDP :
    HasMaxInformation A k ↔ IsLocalDP (fun x y ↦ (A x {y}).toReal) k := by
  rw [hasMaxInformation_iff]
  refine forall₃_congr fun S S' y ↦ ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top (A S) {y}),
    ← ENNReal.ofReal_toReal (measure_ne_top (A S') {y}), ← ENNReal.ofReal_mul (exp_pos k).le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (exp_pos k).le ENNReal.toReal_nonneg)]

/-- **Local differential privacy bounds max-information**: if the channel `κ` is
`ε`-locally differentially private, then `I∞(X; Y) ≤ ε` for every input distribution. The
same scope remark as for `hasMaxInformation_iff_isLocalDP` applies. -/
theorem maxInformation_le_of_isLocalDP {ε : ℝ} (hA : IsLocalDP (fun x y ↦ (A x {y}).toReal) ε)
    (μ : Measure α) [IsProbabilityMeasure μ] : maxInformation μ A ≤ ε :=
  hasMaxInformation_iff_isLocalDP.2 hA μ inferInstance

end Algorithm

/-! ### Pure differential privacy bounds max-information -/

section DifferentialPrivacy

variable {ι 𝒳 Z : Type*} [Fintype ι] [DecidableEq 𝒳] {m𝒳 : MeasurableSpace 𝒳}
  {mZ : MeasurableSpace Z} {M : Kernel (ι → 𝒳) Z} {ε : ℝ}

/-- **Group privacy** for pure differential privacy: if `M` is `ε`-differentially private for
datasets differing in one record, then `P[M(S) ∈ E] ≤ e^{ε d(S, S')} P[M(S') ∈ E]`, where
`d(S, S')` is the Hamming distance (the number of records in which `S` and `S'` differ). -/
theorem IsEpsDeltaDP.measureReal_le_exp_mul_hammingDist
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε 0) (S S' : ι → 𝒳) (E : Set Z) :
    (M S).real E ≤ exp (ε * hammingDist S S') * (M S').real E := by
  classical
  induction h : hammingDist S S' generalizing S with
  | zero => simp [hammingDist_eq_zero.1 h]
  | succ n ih =>
    obtain ⟨i, hi⟩ : ∃ i, S i ≠ S' i := by
      by_contra! h'
      simp [funext h'] at h
    set T := Function.update S i (S' i)
    have hST : hammingDist S T = 1 := by
      rw [hammingDist, Finset.card_eq_one]
      refine ⟨i, ?_⟩
      ext k
      by_cases hk : k = i <;> simp [T, hk, hi, Function.update_apply]
    have hTS' : hammingDist T S' = n := by
      have hset : Finset.univ.filter (fun k ↦ T k ≠ S' k) =
          (Finset.univ.filter fun k ↦ S k ≠ S' k).erase i := by
        ext k
        by_cases hk : k = i <;> simp [T, hk, Function.update_apply]
      rw [hammingDist, hset, Finset.card_erase_of_mem (by simpa using hi), ← hammingDist, h]
      rfl
    calc (M S).real E ≤ exp ε * (M T).real E := by simpa using hM hST E
      _ ≤ exp ε * (exp (ε * n) * (M S').real E) :=
        mul_le_mul_of_nonneg_left (ih T hTS') (exp_pos ε).le
      _ = exp (ε * ↑(n + 1)) * (M S').real E := by
        push_cast
        rw [mul_add, mul_one, exp_add]
        ring

/-- Group privacy, pointwise form in `ℝ≥0∞`. -/
lemma IsEpsDeltaDP.apply_singleton_le_hammingDist [IsFiniteKernel M]
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε 0) (S S' : ι → 𝒳) (z : Z) :
    M S {z} ≤ ENNReal.ofReal (exp (ε * hammingDist S S')) * M S' {z} := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (M S) {z}),
    ← ENNReal.ofReal_toReal (measure_ne_top (M S') {z}), ← ENNReal.ofReal_mul (exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (hM.measureReal_le_exp_mul_hammingDist S S' {z})

/-- **Theorem 19 of Dwork et al.**: an `ε`-differentially private algorithm on datasets with `n`
records (here `ι → 𝒳` with `n = |ι|`; neighbours differ in exactly one record) has
max-information at most `ε n` (in nats; the paper's `log₂ e · ε n` bits), for every distribution
of the dataset. The output type `Z` is not assumed finite; for a diffuse output law (e.g. the
Laplace mechanism) the conclusion holds vacuously (see the scope note in the module docstring). -/
theorem hasMaxInformation_of_isEpsDeltaDP [Finite 𝒳] [MeasurableSingletonClass 𝒳]
    [MeasurableSingletonClass Z] [IsMarkovKernel M] (hε : 0 ≤ ε)
    (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε 0) :
    HasMaxInformation M (ε * Fintype.card ι) := by
  refine hasMaxInformation_of_forall_le fun S S' z ↦ ?_
  refine (hM.apply_singleton_le_hammingDist S S' z).trans (mul_le_mul_left ?_ _)
  refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hε))
  exact_mod_cast hammingDist_le_card_fintype

/-- **Theorem 19 of Dwork et al.**, for datasets `S ∈ 𝒳ⁿ`: an `ε`-differentially private algorithm
satisfies `I∞(S; A(S)) ≤ ε n` for every distribution of `S`. The same scope remark as for
`hasMaxInformation_of_isEpsDeltaDP` applies. -/
theorem maxInformation_le_of_isEpsDeltaDP {n : ℕ} {M : Kernel (Fin n → 𝒳) Z} [Finite 𝒳]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass Z] [IsMarkovKernel M]
    (hε : 0 ≤ ε) (hM : IsEpsDeltaDP M (fun S S' ↦ hammingDist S S' = 1) ε 0)
    (μ : Measure (Fin n → 𝒳)) [IsProbabilityMeasure μ] : maxInformation μ M ≤ (ε * n : ℝ) := by
  simpa using hasMaxInformation_of_isEpsDeltaDP hε hM μ inferInstance

end DifferentialPrivacy

/-! ### Comparison with maximal leakage and mutual information -/

section Bridges

variable [Finite α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ]

/-- Multiplicative form of `maxLeakage_le_maxInformation`. -/
lemma maxLeakageSum_le_expMaxInformation : maxLeakageSum μ κ ≤ expMaxInformation μ κ := by
  calc maxLeakageSum μ κ ≤ ∑ y, expMaxInformation μ κ * (κ ∘ₘ μ) {y} :=
        Finset.sum_le_sum fun y _ ↦ iSup₂_le fun x hx ↦ le_expMaxInformation_mul hx y
    _ = expMaxInformation μ κ := by simp [← Finset.mul_sum, sum_measure_singleton]

/-- **Maximal leakage is at most max-information**, `L(X → Y) ≤ I∞(X; Y)` (Lemma 12 of
Esposito, Gastpar and Issa, arXiv:1912.01439v3). -/
theorem maxLeakage_le_maxInformation : (maxLeakage μ κ : EReal) ≤ maxInformation μ κ := by
  obtain ⟨x, hx⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  rw [maxLeakage, ← ENNReal.log_pos_real' (by linarith [one_le_toReal_maxLeakageSum (κ := κ) hx]),
    maxInformation_eq_log, ENNReal.log_le_log_iff]
  exact maxLeakageSum_le_expMaxInformation

omit [Fintype β] in
/-- **Mutual information is at most max-information**, `I(X; Y) ≤ I∞(X; Y)` (Dwork et al., after
Definition 10), as an inequality in `EReal`. -/
theorem mutualInfo_compProd_le_maxInformation [Finite β] :
    (mutualInfo (μ ⊗ₘ κ) : EReal) ≤ maxInformation μ κ := by
  have := Fintype.ofFinite β
  obtain ⟨x, hx⟩ := MeasureTheory.Measure.exists_measure_singleton_ne_zero μ
  refine (EReal.coe_ennreal_le_coe_ennreal_iff.2 mutualInfo_compProd_le_ofReal_maxLeakage).trans ?_
  rw [EReal.coe_ennreal_ofReal, max_eq_left (maxLeakage_nonneg hx)]
  exact maxLeakage_le_maxInformation

end Bridges

/-! ### The fixed-distribution form of Lemma 14 fails -/

section Counterexample

/-- `max_{x, y} P_XY(x, y) / (P_X(x) P_Y(y)) ≤ c` in real arithmetic: `P_{Y|X}(y | x) ≤
c ∑_{x'} P_{Y|X}(y | x') P_X(x')` for every `x` in the support of `X` and every `y`. -/
theorem expMaxInformation_le_ofReal_iff [Fintype α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [IsFiniteMeasure μ] [IsMarkovKernel κ] {c : ℝ} (hc : 0 ≤ c) :
    expMaxInformation μ κ ≤ ENNReal.ofReal c ↔
      ∀ x, μ.real {x} ≠ 0 → ∀ y, (κ x).real {y} ≤ c * ∑ x', (κ x').real {y} * μ.real {x'} := by
  rw [expMaxInformation_le_iff]
  refine forall_congr' fun x ↦ imp_congr (by simp [measureReal_def, ENNReal.toReal_eq_zero_iff])
    (forall_congr' fun y ↦ ?_)
  rw [comp_apply_singleton, ← ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun _ _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_sum fun _ _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp [measureReal_def, ENNReal.toReal_mul]

/-- **The fixed-distribution form of Lemma 14 of Dwork et al. fails** (see the notes on the paper
in the module docstring). For `S ∈ {0, 1, 2}` with `P[S = 0] = 1/10`, `P[S = 1] = P[S = 2] = 9/20`,
the deterministic algorithms `A(S) = [S = 2]`, `B(S, 0) = [S = 1]` and `B(S, 1) = 1` satisfy
`I∞(S; A(S)) ≤ log (20/9)` and `I∞(S; B(S, y)) ≤ log (20/9)` for both `y`, but the adaptive
composition `C(S) = B(S, A(S))` has `I∞(S; C(S)) > 2 log (20/9)` (in fact `= log 10`). This does
not contradict Lemma 14 (`HasMaxInformation.snd_compProd`), whose hypotheses quantify over every
prior; it refutes the fixed-prior version that the last step of the paper's proof would give. -/
theorem MaxInformation.exists_not_maxInformation_snd_compProd_le :
    ∃ (μ : Measure (Fin 3)) (A : Kernel (Fin 3) (Fin 2)) (B : Kernel (Fin 3 × Fin 2) (Fin 2)),
      IsProbabilityMeasure μ ∧ IsMarkovKernel A ∧ IsMarkovKernel B ∧
      maxInformation μ A ≤ (Real.log (20 / 9) : ℝ) ∧
      (∀ y, maxInformation μ (B.sectL y) ≤ (Real.log (20 / 9) : ℝ)) ∧
      ¬ maxInformation μ (A ⊗ₖ B).snd ≤ (Real.log (20 / 9) + Real.log (20 / 9) : ℝ) := by
  set p : Fin 3 → ℝ := ![1 / 10, 9 / 20, 9 / 20]
  have hp0 (x : Fin 3) : 0 ≤ p x := by fin_cases x <;> simp [p] <;> norm_num
  set μ : Measure (Fin 3) := Measure.sum fun x ↦ ENNReal.ofReal (p x) • Measure.dirac x
  have hμ (x : Fin 3) : μ.real {x} = p x := by
    rw [measureReal_def]
    simp only [μ, Measure.sum_smul_dirac_singleton]
    exact ENNReal.toReal_ofReal (hp0 x)
  have : IsProbabilityMeasure μ := ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp only [μ, Measure.sum_smul_dirac_singleton]
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hp0 x]
    simp [Fin.sum_univ_three, p]
    norm_num⟩
  set fA : Fin 3 → Fin 2 := ![0, 0, 1]
  set fB : Fin 3 × Fin 2 → Fin 2 := fun q ↦ if q.2 = 0 then ![0, 1, 0] q.1 else 1
  set A := Kernel.deterministic fA (measurable_of_finite _)
  set B := Kernel.deterministic fB (measurable_of_finite _)
  have hdet {X : Type} [MeasurableSpace X] (f : X → Fin 2) (hf : Measurable f) (x : X)
      (y : Fin 2) : (Kernel.deterministic f hf x).real {y} = if f x = y then 1 else 0 := by
    by_cases h : f x = y <;> simp [Kernel.deterministic_apply, measureReal_def, h]
  have hC (S : Fin 3) (z : Fin 2) :
      ((A ⊗ₖ B).snd S).real {z} = if fB (S, fA S) = z then 1 else 0 := by
    rw [measureReal_def, MaxInformation.snd_compProd_apply_singleton]
    fin_cases S <;> fin_cases z <;>
      simp [A, B, fA, fB, Kernel.deterministic_apply, Fin.sum_univ_two]
  have hlog : exp (Real.log (20 / 9)) = 20 / 9 := exp_log (by norm_num)
  refine ⟨μ, A, B, this, inferInstance, inferInstance, ?_, fun y ↦ ?_, ?_⟩
  · rw [maxInformation_le_iff, hlog, expMaxInformation_le_ofReal_iff (by norm_num)]
    intro x _ y
    simp only [A, hdet, hμ, Fin.sum_univ_three]
    fin_cases x <;> fin_cases y <;> simp [fA, p] <;> norm_num
  · rw [maxInformation_le_iff, hlog, expMaxInformation_le_ofReal_iff (by norm_num)]
    intro x _ z
    simp only [B, Kernel.sectL_apply, hdet, hμ, Fin.sum_univ_three]
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [fB, p] <;> norm_num
  · rw [maxInformation_le_iff, exp_add, hlog, expMaxInformation_le_ofReal_iff (by positivity)]
    push Not
    refine ⟨0, by simp [hμ, p], 0, ?_⟩
    simp only [hC, hμ, Fin.sum_univ_three]
    simp [fA, fB, p]
    norm_num

end Counterexample

end InformationTheory
