/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DPHamming.Basic
public import InfoLeakage.FDP.Basic
public import InfoLeakage.PointwiseLeakage.Basic
public import Mathlib.InformationTheory.Hamming

/-!
# Information privacy and local information privacy

F. du Pin Calmon and N. Fawaz (*Privacy against statistical inference*, Allerton 2012,
[arXiv:1210.2123](https://arxiv.org/abs/1210.2123), Definition 6) call a privacy mapping
`P_{Y|X}` *`ε`-information private* if observing any output changes the probability of any input
by at most a factor `e^ε`:
`e^{-ε} ≤ P_{X|Y=y}(x) / P_X(x) ≤ e^ε` for all `x ∈ supp P_X` and `y ∈ supp P_Y`.
For a fixed prior this is also *`ε`-local information privacy* (LIP): Definition 15 of
Saeidian–Cervia–Oechtering–Skoglund (*Pointwise maximal leakage*, arXiv:2205.04935), and
Definition 6 / equation (7) of B. Jiang, M. Li and R. Tandon (*Local information privacy and its
application to privacy-preserving data aggregation*, IEEE Trans. Dependable Secure Comput.,
[arXiv:2001.02385](https://arxiv.org/abs/2001.02385), v2) in the case where the secret is the
data itself (`G = X`).

We work with finite alphabets, a prior `μ` and a channel `κ`, as in
`InfoLeakage.PointwiseLeakage.Basic`. `IsInfoPrivate` constrains only inputs in `supp P_X` (where
the ratio is defined) and outputs in `supp P_Y`; it is meant for a countable (in the papers,
finite) output alphabet, and is vacuous for an atomless output law.

## Main definitions

* `IsInfoPrivate μ κ ε`: `ε`-information privacy (Definition 6 of du Pin Calmon–Fawaz).
* `PointwiseLeakage.measureEntropy P`: the Shannon entropy of a measure on a finite alphabet.
* `maximumInformationLeakage μ κ`: the maximum information leakage
  `max_{u ∈ supp P_U} H(S) - H(S | U = u)` (Definition 4 of du Pin Calmon–Fawaz).

## Paper-to-Lean map

du Pin Calmon–Fawaz (arXiv v1):
* Definitions 4 and 6: `maximumInformationLeakage`, `IsInfoPrivate`.
* Theorem 3: `IsInfoPrivate.isEpsDeltaDP` (`2ε`-differential privacy for any neighbouring relation
  between inputs in the support of the prior) and its literal form
  `IsInfoPrivate.isEpsDeltaDP_hammingDist` (databases differing in at most one entry, prior of full
  support); `IsInfoPrivate.mutualInfo_le` (average leakage `I(S; U) ≤ ε` nats `= ε / ln 2` bits).
* The claim of Section V that information privacy bounds the maximum information leakage is
  refuted by `exists_isInfoPrivate_log_two_lt_maximumInformationLeakage` (see the notes).

Saeidian–Cervia–Oechtering–Skoglund (arXiv v2):
* Definition 15 and the remark after Proposition 6 ("`ε`-LIP implies `ε`-PML"):
  `IsInfoPrivate.isEpsPML`.

Jiang–Li–Tandon (arXiv v2):
* Equation (7) (LIP in likelihood form): `isInfoPrivate_iff`. Equation (7) ranges over all
  inputs `x ∈ 𝒳`, `isInfoPrivate_iff` over `supp P_X`; they agree for priors of full support.
* Section 2.2.1: `ε`-LIP implies `2ε`-LDP, `IsInfoPrivate.isLocalDP` (for a prior of full support;
  `IsInfoPrivate.apply_le` on the support of any prior); `ε`-LDP implies `ε`-LIP,
  `isInfoPrivate_of_isLocalDP` (and `isInfoPrivate_of_forall_le`, with LDP only on the support).
* Section 2.2.3: `ε`-LIP implies `ε`-MIP and `ε`-MIL, `IsInfoPrivate.mutualInfo_le` and
  `IsInfoPrivate.maxLeakage_le`. Their Definition 2 maximizes over all `x ∈ 𝒳`, `maxLeakage`
  over `supp P_X`; they agree for priors of full support.
* Lemma 1 (post-processing), for `G = X`: `IsInfoPrivate.postprocess`.

## Notes on the papers

* du Pin Calmon–Fawaz, Section V (arXiv v1): the sentence before Theorem 3 says that
  `ε`-information privacy implies "maximum information leakage of at most `ε / ln 2` bits", i.e.
  `max_u H(S) - H(S | U = u) ≤ ε` nats for their Definition 4, and the proof of Theorem 3 starts
  from the identity `H(S) - H(S | U = u) = ∑_s p(s | u) p(u) log (p(s | u) / p(s))`, which does not
  hold. The claim about maximum information leakage is false:
  `exists_isInfoPrivate_log_two_lt_maximumInformationLeakage` gives a `log 2`-information
  private mapping whose maximum information leakage is at least `(3/4) log 3 > log 2`. It is the
  case `ε = log 2`, `N = 16` of the following family (not formalized in general): `p_S` with one
  atom of mass `1/2` and `N` atoms of mass `1/(2N)`, and two equally likely outputs with
  posteriors `(1 - e^{-ε}/2, e^{-ε}/(2N), …)` and `(e^{-ε}/2, (1 - e^{-ε}/2)/N, …)`, which is
  `ε`-information private with `H(S) - H(S | U = u₁) ≥ ((1 - e^{-ε})/2) log N`, unbounded in `N`.
  The statement of Theorem 3 itself, about the *average* leakage `I(S; U) ≤ ε / ln 2` bits, is
  true and is `IsInfoPrivate.mutualInfo_le`.
* du Pin Calmon–Fawaz, Theorem 3, assumes `supp p_U = 𝒰`; this hypothesis is not needed. Its
  differential privacy conclusion uses a prior of full support: Definition 6 quantifies over all
  `s ∈ 𝒮^n` a ratio with denominator `p_S(s)`, which presupposes `p_S(s) > 0`, although the
  paper does not say so. `IsInfoPrivate` only constrains inputs in the support (under a point
  mass prior every mapping satisfies it with `ε = 0`), so the literal statement
  `IsInfoPrivate.isEpsDeltaDP_hammingDist` assumes full support.

## Not formalized

* du Pin Calmon–Fawaz: Theorems 1, 2 and 4, Corollaries 1 and 2 (the convex programs and the
  counting-query example), and the general family of counterexamples above (only one instance).
* Jiang–Li–Tandon: LIP with a latent secret `G ≠ X`, worst-case and bounded-prior LIP
  (including "`ε`-WC-LIP iff `ε`-LDP"), Lemmas 2 and 3 (Pufferfish, differential
  identifiability), and the mechanism-design results of Sections 3–5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β} {ε : ℝ}

/-- **`ε`-information privacy** (Definition 6 of du Pin Calmon–Fawaz), also called `ε`-local
information privacy for a fixed prior (Definition 15 of Saeidian–Cervia–Oechtering–Skoglund;
Definition 6 and equation (7) of Jiang–Li–Tandon with `G = X`): for every input `x ∈ supp P_X`
and every output `y ∈ supp P_Y`, the posterior and the prior satisfy
`e^{-ε} ≤ P_{X|Y=y}(x) / P_X(x) ≤ e^ε`. Only atoms of `P_Y` are constrained, so the condition is
meant for countable (in the papers, finite) output alphabets; it is vacuous for an atomless output
law. -/
def IsInfoPrivate [Fintype α] (μ : Measure α) (κ : Kernel α β)
    (ε : ℝ) : Prop :=
  ∀ x, μ {x} ≠ 0 → ∀ y, (κ ∘ₘ μ) {y} ≠ 0 →
    ENNReal.ofReal (Real.exp (-ε)) ≤ posterior μ κ y {x} / μ {x} ∧
      posterior μ κ y {x} / μ {x} ≤ ENNReal.ofReal (Real.exp ε)

namespace PointwiseLeakage

/-- On a finite alphabet, a pointwise bound `P {y} ≤ c * Q {y}` extends to all events. -/
lemma measure_le_mul_of_forall_singleton [Finite γ] [MeasurableSingletonClass γ]
    {P Q : Measure γ} {c : ℝ≥0∞} (h : ∀ y, P {y} ≤ c * Q {y}) (E : Set γ) :
    P E ≤ c * Q E := by
  classical
  have := Fintype.ofFinite γ
  rw [← Set.coe_toFinset E, ← sum_measure_singleton, ← sum_measure_singleton, Finset.mul_sum]
  exact Finset.sum_le_sum fun y _ ↦ h y

end PointwiseLeakage

section Characterization

variable [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ]

open PointwiseLeakage

omit [MeasurableSingletonClass β] [IsMarkovKernel κ] in
/-- The posterior-to-prior ratio equals the likelihood ratio,
`P_{X|Y=y}(x) / P_X(x) = P_{Y|X}(y | x) / P_Y(y)`, on the support of `P_X`. -/
lemma PointwiseLeakage.posterior_apply_singleton_div {x : α} (hx : μ {x} ≠ 0) (y : β) :
    posterior μ κ y {x} / μ {x} = κ x {y} / (κ ∘ₘ μ) {y} := by
  rw [posterior_apply_singleton, ← mul_assoc, ENNReal.mul_div_cancel_right hx
    (measure_ne_top _ _), ENNReal.div_eq_inv_mul]

/-- `ε`-information privacy in multiplicative (likelihood) form, equation (7) of
Jiang–Li–Tandon: `e^{-ε} P_Y(y) ≤ P_{Y|X}(y | x) ≤ e^ε P_Y(y)` for every `x ∈ supp P_X` and every
output `y`. Equation (7) ranges over all inputs `x ∈ 𝒳`; the two agree for priors of full
support. -/
theorem isInfoPrivate_iff : IsInfoPrivate μ κ ε ↔ ∀ x, μ {x} ≠ 0 → ∀ y,
    ENNReal.ofReal (Real.exp (-ε)) * (κ ∘ₘ μ) {y} ≤ κ x {y} ∧
      κ x {y} ≤ ENNReal.ofReal (Real.exp ε) * (κ ∘ₘ μ) {y} := by
  refine forall₂_congr fun x hx ↦ ⟨fun h y ↦ ?_, fun h y hy ↦ ?_⟩
  · by_cases hy : (κ ∘ₘ μ) {y} = 0
    · simp [hy, apply_eq_zero_of_comp_eq_zero hx hy]
    · obtain ⟨h1, h2⟩ := h y hy
      rw [posterior_apply_singleton_div hx] at h1 h2
      exact ⟨(ENNReal.le_div_iff_mul_le (Or.inl hy) (Or.inl (measure_ne_top _ _))).1 h1,
        (ENNReal.div_le_iff hy (measure_ne_top _ _)).1 h2⟩
  · rw [posterior_apply_singleton_div hx]
    exact ⟨(ENNReal.le_div_iff_mul_le (Or.inl hy) (Or.inl (measure_ne_top _ _))).2 (h y).1,
      (ENNReal.div_le_iff hy (measure_ne_top _ _)).2 (h y).2⟩

/-- `ε`-local information privacy implies `ε`-PML (Saeidian–Cervia–Oechtering–Skoglund,
Section IV-B: "According to Definition 15, `ε`-LIP implies `ε`-PML"). -/
theorem IsInfoPrivate.isEpsPML (h : IsInfoPrivate μ κ ε) : IsEpsPML μ κ ε :=
  isEpsPML_iff_forall_le.2 fun x hx y ↦ (isInfoPrivate_iff.1 h x hx y).2

/-- `ε`-local information privacy implies `L(X → Y) ≤ ε` (Jiang–Li–Tandon, Section 2.2.3:
"`ε`-LIP also implies `ε`-MIL"). Their maximal leakage (Definition 2) maximizes over all inputs,
`maxLeakage` over `supp P_X`; the two agree for priors of full support. -/
theorem IsInfoPrivate.maxLeakage_le [Fintype β] (h : IsInfoPrivate μ κ ε) :
    maxLeakage μ κ ≤ ε :=
  h.isEpsPML.maxLeakage_le

/-- **Theorem 3** of du Pin Calmon–Fawaz (average leakage part): an `ε`-information private
mapping leaks at most `ε` nats (`ε / ln 2` bits) on average, `I(X; Y) ≤ ε`. This is also
"`ε`-LIP implies `ε`-MIP" of Jiang–Li–Tandon (Section 2.2.3). The hypothesis
`supp P_Y = 𝒴` of the paper is not needed. -/
theorem IsInfoPrivate.mutualInfo_le [Finite β] (h : IsInfoPrivate μ κ ε) :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal ε :=
  h.isEpsPML.mutualInfo_le

/-- An `ε`-information private mapping satisfies `P_{Y|X}(y | x) ≤ e^{2ε} P_{Y|X}(y | x')` for all
inputs `x, x'` in the support of the prior and all outputs `y`. -/
theorem IsInfoPrivate.apply_le (h : IsInfoPrivate μ κ ε) {x x' : α} (hx : μ {x} ≠ 0)
    (hx' : μ {x'} ≠ 0) (y : β) :
    κ x {y} ≤ ENNReal.ofReal (Real.exp (2 * ε)) * κ x' {y} := by
  have h_exp (a b : ℝ) : ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) =
      ENNReal.ofReal (Real.exp (a + b)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_add]
  have h1 := (isInfoPrivate_iff.1 h x hx y).2
  have h2 : (κ ∘ₘ μ) {y} ≤ ENNReal.ofReal (Real.exp ε) * κ x' {y} :=
    calc (κ ∘ₘ μ) {y}
        = ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (Real.exp (-ε)) * (κ ∘ₘ μ) {y}) := by
          rw [← mul_assoc, h_exp, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr; exact (isInfoPrivate_iff.1 h x' hx' y).1
  calc κ x {y} ≤ ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (Real.exp ε) * κ x' {y}) :=
        h1.trans (by gcongr)
    _ = ENNReal.ofReal (Real.exp (2 * ε)) * κ x' {y} := by rw [← mul_assoc, h_exp, two_mul]

/-- **Theorem 3** of du Pin Calmon–Fawaz (differential privacy part): an `ε`-information private
mapping is `2ε`-differentially private, `P(Y ∈ B | X = s) ≤ e^{2ε} P(Y ∈ B | X = s')` for every
event `B`, for every neighbouring relation `Adj` between inputs in the support of the prior (for
instance any relation, when the prior has full support; see
`IsInfoPrivate.isEpsDeltaDP_hammingDist` for the paper's Hamming adjacency). The paper's
hypothesis `supp P_Y = 𝒴` is not needed. -/
theorem IsInfoPrivate.isEpsDeltaDP [Finite β] (h : IsInfoPrivate μ κ ε) {Adj : α → α → Prop}
    (hAdj : ∀ ⦃s s'⦄, Adj s s' → μ {s} ≠ 0 ∧ μ {s'} ≠ 0) :
    IsEpsDeltaDP κ Adj (2 * ε) 0 := by
  intro s s' hss' E
  obtain ⟨hs, hs'⟩ := hAdj hss'
  have hE := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (measure_le_mul_of_forall_singleton (fun y ↦ h.apply_le hs hs' y) E)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hE
  simpa [measureReal_def] using hE

/-- `ε`-local information privacy implies `2ε`-local differential privacy (Jiang–Li–Tandon,
Section 2.2.1), for a prior of full support. -/
theorem IsInfoPrivate.isLocalDP (h : IsInfoPrivate μ κ ε) (hμ : ∀ x, μ {x} ≠ 0) :
    IsLocalDP (fun x y ↦ (κ x {y}).toReal) (2 * ε) := fun x x' y ↦ by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (h.apply_le (hμ x) (hμ x') y)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h'

/-- `ε`-local differential privacy implies `ε`-local information privacy (Jiang–Li–Tandon,
Section 2.2.1), with LDP only required between inputs in the support of the prior
(Definition 14 of Saeidian–Cervia–Oechtering–Skoglund). -/
theorem isInfoPrivate_of_forall_le (h : ∀ x x', μ {x} ≠ 0 → μ {x'} ≠ 0 → ∀ y,
    κ x {y} ≤ ENNReal.ofReal (Real.exp ε) * κ x' {y}) : IsInfoPrivate μ κ ε := by
  rw [isInfoPrivate_iff]
  intro x hx y
  have h_sum : (κ ∘ₘ μ) {y} = ∑ x', κ x' {y} * μ {x'} := comp_apply_singleton _ _ _
  have h_one (c : ℝ≥0∞) : ∑ x', c * μ {x'} = c := by
    rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
  constructor
  · have hP : (κ ∘ₘ μ) {y} ≤ ENNReal.ofReal (Real.exp ε) * κ x {y} := by
      rw [h_sum, ← h_one (ENNReal.ofReal (Real.exp ε) * κ x {y})]
      refine Finset.sum_le_sum fun x' _ ↦ ?_
      by_cases hx' : μ {x'} = 0
      · simp [hx']
      · exact mul_le_mul_left (h x' x hx' hx y) _
    calc ENNReal.ofReal (Real.exp (-ε)) * (κ ∘ₘ μ) {y}
        ≤ ENNReal.ofReal (Real.exp (-ε)) * (ENNReal.ofReal (Real.exp ε) * κ x {y}) := by gcongr
      _ = κ x {y} := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  · rw [← h_one (κ x {y}), h_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x' _ ↦ ?_
    by_cases hx' : μ {x'} = 0
    · simp [hx']
    · rw [← mul_assoc]
      exact mul_le_mul_left (h x x' hx hx' y) _

/-- `ε`-local differential privacy implies `ε`-local information privacy for every prior
(Jiang–Li–Tandon, Section 2.2.1). -/
theorem isInfoPrivate_of_isLocalDP (h : IsLocalDP (fun x y ↦ (κ x {y}).toReal) ε) :
    IsInfoPrivate μ κ ε :=
  isInfoPrivate_of_forall_le fun x x' _ _ y ↦ by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (κ x) {y}),
      ← ENNReal.ofReal_toReal (measure_ne_top (κ x') {y}),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (h x x' y)

/-- **Lemma 1** of Jiang–Li–Tandon (post-processing, with `G = X`): if `Y` is an `ε`-local
information private release of `X`, so is any post-processing `Z` of `Y`. -/
theorem IsInfoPrivate.postprocess [Finite β] [MeasurableSingletonClass γ]
    (h : IsInfoPrivate μ κ ε) (η : Kernel β γ) [IsMarkovKernel η] :
    IsInfoPrivate μ (η ∘ₖ κ) ε := by
  have := Fintype.ofFinite β
  rw [isInfoPrivate_iff] at h ⊢
  intro x hx z
  rw [Kernel.comp_apply_eq_sum _ _ _ (measurableSet_singleton z), ← Measure.comp_assoc,
    comp_apply_singleton (κ ∘ₘ μ) η z, Finset.mul_sum, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun y _ ↦ ?_, Finset.sum_le_sum fun y _ ↦ ?_⟩
  · rw [mul_left_comm]
    exact mul_le_mul_right (h x hx y).1 _
  · rw [mul_left_comm]
    exact mul_le_mul_right (h x hx y).2 _

end Characterization

section Hamming

/-- **Theorem 3** of du Pin Calmon–Fawaz (differential privacy part), literal form: for databases
`s = (s_1, …, s_n)` and a prior of full support (implicit in their Definition 6, whose ratio has
`p_S(s)` in the denominator for every `s`), an `ε`-information private mapping satisfies
`P(Y ∈ B | X = s) ≤ e^{2ε} P(Y ∈ B | X = s')` for all databases `s, s'` differing in at most one
entry and every event `B`. -/
theorem IsInfoPrivate.isEpsDeltaDP_hammingDist {ι 𝒮 : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype 𝒮] [DecidableEq 𝒮] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
    {μ : Measure (ι → 𝒮)} [IsProbabilityMeasure μ] {κ : Kernel (ι → 𝒮) β} [IsMarkovKernel κ]
    [Finite β] [MeasurableSingletonClass β] (h : IsInfoPrivate μ κ ε) (hμ : ∀ s, μ {s} ≠ 0) :
    IsEpsDeltaDP κ (fun s s' ↦ hammingDist s s' ≤ 1) (2 * ε) 0 :=
  h.isEpsDeltaDP fun s s' _ ↦ ⟨hμ s, hμ s'⟩

end Hamming

section MaxInformationLeakage

/-- The Shannon entropy `H(P) = ∑_x -P(x) log P(x)`, in nats, of a measure on a finite
alphabet. -/
noncomputable def PointwiseLeakage.measureEntropy [Fintype α] (P : Measure α) : ℝ :=
  ∑ x, Real.negMulLog (P.real {x})

open PointwiseLeakage

/-- The **maximum information leakage** of du Pin Calmon–Fawaz (Definition 4),
`max_{u ∈ supp P_U} H(S) - H(S | U = u)`, in nats, of a private variable `S ∼ μ` on a finite
alphabet through the output `U` of the mapping `κ`; `H(S | U = u)` is the entropy of the
posterior `P_{S|U=u}`. It is meant for a finite output alphabet (the supremum is over the
outcomes of positive probability). -/
noncomputable def maximumInformationLeakage [Fintype α] (μ : Measure α) (κ : Kernel α β) : ℝ :=
  ⨆ u : {u : β // (κ ∘ₘ μ) {u} ≠ 0}, (measureEntropy μ - measureEntropy (posterior μ κ u))

/-- **Information privacy does not bound the maximum information leakage**: a counterexample to
the claim of du Pin Calmon–Fawaz (Section V, the sentence before Theorem 3) that an
`ε`-information private mapping has maximum information leakage (Definition 4) at most `ε`
(`ε / ln 2` bits). Take `ε = log 2`, a secret `S` on 17 values with `P_S(0) = 1/2` and
`P_S(s) = 1/32` otherwise, and a binary output `U` with `P(U = true | S = 0) = 3/4` and
`P(U = true | S = s) = 1/4` otherwise. The mapping is `log 2`-information private (every
posterior-to-prior ratio is `1/2` or `3/2`), yet `H(S) - H(S | U = true) = (3/4) log 3 > log 2`. -/
theorem exists_isInfoPrivate_log_two_lt_maximumInformationLeakage :
    ∃ (μ : Measure (Fin 17)) (κ : Kernel (Fin 17) Bool), IsProbabilityMeasure μ ∧
      IsMarkovKernel κ ∧ IsInfoPrivate μ κ (Real.log 2) ∧
        Real.log 2 < maximumInformationLeakage μ κ := by
  classical
  -- The prior `p` and the channel `w`, as real weights.
  set p : Fin 17 → ℝ := fun s ↦ if s = 0 then 1 / 2 else 1 / 32
  set w : Fin 17 → Bool → ℝ := fun s u ↦ if (s = 0 ↔ u = true) then 3 / 4 else 1 / 4
  have hp0 (s : Fin 17) : 0 ≤ p s := by
    simp only [p]
    split_ifs <;> norm_num
  have hw0 (s : Fin 17) (u : Bool) : 0 ≤ w s u := by
    simp only [w]
    split_ifs <;> norm_num
  set μ : Measure (Fin 17) := Measure.sum fun s ↦ ENNReal.ofReal (p s) • Measure.dirac s
  set κ : Kernel (Fin 17) Bool := Kernel.ofFunOfCountable fun s ↦
    Measure.sum fun u ↦ ENNReal.ofReal (w s u) • Measure.dirac u
  have hμ (s : Fin 17) : μ {s} = ENNReal.ofReal (p s) := Measure.sum_smul_dirac_singleton
  have hκ (s : Fin 17) (u : Bool) : κ s {u} = ENNReal.ofReal (w s u) :=
    Measure.sum_smul_dirac_singleton
  have : IsProbabilityMeasure μ := ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hμ]
    rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ hp0 s, Fin.sum_univ_succ]
    simp [p, Fin.succ_ne_zero]
    norm_num⟩
  have : IsMarkovKernel κ := ⟨fun s ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hκ]
    rw [← ENNReal.ofReal_sum_of_nonneg fun u _ ↦ hw0 s u, Fintype.sum_bool]
    by_cases hs : s = 0 <;> simp [w, hs] <;> norm_num⟩⟩
  have hPU (u : Bool) : (κ ∘ₘ μ) {u} = ENNReal.ofReal (1 / 2) := by
    rw [comp_apply_singleton]
    simp_rw [hκ, hμ, ← ENNReal.ofReal_mul (hw0 _ _)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ mul_nonneg (hw0 _ _) (hp0 _), Fin.sum_univ_succ]
    congr 1
    cases u <;> simp [w, p, Fin.succ_ne_zero] <;> norm_num
  have h_exp : Real.exp (Real.log 2) = 2 := Real.exp_log two_pos
  have h_exp' : Real.exp (-Real.log 2) = 1 / 2 := by rw [Real.exp_neg, h_exp]; norm_num
  refine ⟨μ, κ, inferInstance, inferInstance, ?_, ?_⟩
  · rw [isInfoPrivate_iff]
    intro s _ u
    rw [hκ, hPU, h_exp, h_exp', ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    constructor <;> refine ENNReal.ofReal_le_ofReal ?_ <;>
      by_cases hs : s = 0 <;> cases u <;> simp [w, hs] <;> norm_num
  · have hpos : (κ ∘ₘ μ) {true} ≠ 0 := by
      rw [hPU]
      norm_num
    unfold maximumInformationLeakage
    refine lt_of_lt_of_le ?_ (le_ciSup (Set.finite_range _).bddAbove ⟨true, hpos⟩)
    -- The prior and the posterior given `U = true`, as real numbers.
    have hμ_zero : μ.real {0} = 1 / 2 := by
      rw [measureReal_def, hμ, ENNReal.toReal_ofReal (hp0 _)]
      simp [p]
    have hμ_succ (i : Fin 16) : μ.real {i.succ} = 1 / 32 := by
      rw [measureReal_def, hμ, ENNReal.toReal_ofReal (hp0 _)]
      simp [p, Fin.succ_ne_zero]
    have hpost (s : Fin 17) : (posterior μ κ true).real {s} = 2 * (w s true * p s) := by
      rw [measureReal_def, posterior_apply_singleton, hPU, hκ, hμ, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num),
        ENNReal.toReal_ofReal (hw0 _ _), ENNReal.toReal_ofReal (hp0 _)]
      norm_num
    have hpost_zero : (posterior μ κ true).real {0} = 3 / 4 := by
      rw [hpost]
      simp [w, p]
      norm_num
    have hpost_succ (i : Fin 16) : (posterior μ κ true).real {i.succ} = 1 / 64 := by
      rw [hpost]
      simp [w, p, Fin.succ_ne_zero]
      norm_num
    -- The entropies, in terms of `log 2` and `log 3`.
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have e1 : Real.negMulLog (1 / 2) = Real.log 2 / 2 := by
      rw [Real.negMulLog, one_div, Real.log_inv]
      ring
    have e2 : Real.negMulLog (1 / 32) = 5 * Real.log 2 / 32 := by
      rw [Real.negMulLog, one_div, Real.log_inv, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast
      ring
    have e3 : Real.negMulLog (3 / 4) = 3 * Real.log 2 / 2 - 3 * Real.log 3 / 4 := by
      rw [Real.negMulLog, Real.log_div (by norm_num) (by norm_num), h2]
      ring
    have e4 : Real.negMulLog (1 / 64) = 6 * Real.log 2 / 64 := by
      rw [Real.negMulLog, one_div, Real.log_inv, show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      push_cast
      ring
    have hlog : 4 * Real.log 2 < 3 * Real.log 3 := by
      have h := Real.log_lt_log (by norm_num) (show (2 : ℝ) ^ 4 < 3 ^ 3 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      exact_mod_cast h
    simp only [measureEntropy, Fin.sum_univ_succ (n := 16), hμ_zero, hμ_succ, hpost_zero,
      hpost_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e1, e2, e3,
      e4]
    push_cast
    linarith

end MaxInformationLeakage

end InformationTheory
