/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Metric privacy (`d_X`-privacy)

This file formalizes the general theory of K. Chatzikokolakis, M. E. Andrés, N. E. Bordenabe and
C. Palamidessi, *Broadening the scope of differential privacy using metrics*, PETS 2013,
LNCS 7981, pp. 82–102 (HAL hal-00767210v1, whose appendices contain the proofs; result numbers
follow it), cited below as [CABP], and the parts of M. E. Andrés, N. E. Bordenabe,
K. Chatzikokolakis and C. Palamidessi, *Geo-indistinguishability: differential privacy for
location-based systems*, CCS 2013 ([arXiv:1212.1984](https://arxiv.org/abs/1212.1984), v3),
cited as [ABCP], that hold for general metrics. The Laplace mechanisms and
geo-indistinguishability are in `InfoLeakage.MetricPrivacy.Laplace`.

A mechanism is a kernel `K : Kernel X Z` from secrets to outputs, on **arbitrary measurable
spaces**. Distinguishability is a function `d : X → X → ℝ≥0∞`; the paper takes an extended
metric, but the metric axioms are not needed for the results below unless stated (cf. footnote 4
of [CABP]). `K` is `d`-private if `K(x)(E) ≤ e^{d(x, x')} K(x')(E)` for all `x, x'` and events
`E` (Definition 1), the requirement being void when `d(x, x') = ∞`.

## Main definitions

* `IsMetricDP K d`: `d`-privacy (Definition 1 of [CABP]).
* `MetricDP.graphDist Adj`: the distance induced by a graph (Section 2 of [CABP]).
* `MetricDP.HammingAdj`: Hamming adjacency of databases `ι → V`.
* `MetricDP.IsExpansive`, `MetricDP.IsUniformlySensitive`: Definition 5 of [CABP].
* `MetricDP.bayes`, `MetricDP.restrictTo`: the posterior `Bayes(p, K, E)` of a finitely supported
  prior and the restriction `μ|_N` (Section 2 of [CABP]).
* `MetricDP.manhattanDist`: the Manhattan metric on databases (Section 5.1 of [CABP]).

## Main statements (paper result → Lean name)

* Definition 1, set form: `isMetricDP_iff_forall_measurableSet`, `IsMetricDP.measure_le`.
* Proposition 1 (smaller metric, stronger privacy): `IsMetricDP.mono`.
* Section 2, below (1) (`ε`-DP iff `ε d_h`-privacy, which contains group privacy):
  `isEpsDP_hammingAdj_iff` for Hamming adjacency on `ι → V`, with
  `MetricDP.graphDist_hammingAdj` (the Hamming graph distance is `hammingDist`); generalization
  to an arbitrary adjacency relation and its graph distance (`ε > 0`):
  `isEpsDP_iff_isMetricDP_graphDist`.
* Lemma 2 (tight chains, one direction as in the paper): `MetricDP.le_smul_of_tight_chain`.
* Theorem 3 (hiding functions; Theorem 3.1 of [ABCP]), direction `⟹`, finitely supported priors,
  symmetric `d`, pointwise posterior-ratio form: `IsMetricDP.bayes_comap_le`.
* Theorem 4 (informed adversary; Theorem 3.2 of [ABCP]), direction `⟹`, finitely supported priors
  and finite neighbourhoods, pointwise form: `IsMetricDP.restrictTo_bayes_le`. The `d_P` forms of
  Theorems 3 and 4 (bounds on all sets, via Lemma 1) are not formalized.
* Fact 5 (sensitivity): `IsMetricDP.comap_of_sensitive`, general form `IsMetricDP.comap`.
* Theorem 6 (uniform sensitivity gives the converse of Fact 5): `MetricDP.isMetricDP_comap_iff`.
* Proposition 3 (`d̃₁ ≤ d_h`, so `ε d̃₁`-privacy implies `ε`-DP):
  `MetricDP.manhattanDist_div_le_hammingDist`, `IsMetricDP.isEpsDP_of_manhattanDist`.
* [ABCP] Section 3.3 (independent obfuscation of a tuple of points), for two points:
  `IsMetricDP.parallelComp` (sum metric) and `IsMetricDP.parallelComp_self` (`2 d_∞`).
* Not numbered in the papers (standard): post-processing `IsMetricDP.comp`, `IsMetricDP.map`;
  sequential composition `IsMetricDP.prod` (`(d₁ + d₂)`-privacy).

## Implementation notes

`IsMetricDP K d` is stated as the inequality of measures `K x ≤ e^{d(x, x')} • K x'`, which
covers all sets `E ⊆ Z`. [CABP] phrases Definition 1 with the multiplicative distance
`d_P(K(x), K(x')) ≤ d(x, x')`; by Lemma 1 of [CABP] this is the two-sided ratio bound, which is
our one-sided bound for both orders of `x, x'` (equivalent for symmetric `d`).

The Bayesian characterizations use a real prior `p : X → ℝ`, `p ≥ 0`, supported in a finite set
`S`, and finite kernels (event probabilities `(K x).real E`); [CABP] allows discrete priors on an
arbitrary `X`. We prove the pointwise ratio bounds that make up the paper's proofs, assuming
that the denominators (the probability of the observation) are positive, as Bayes' rule needs.

For a general adjacency relation, `isEpsDP_iff_isMetricDP_graphDist` assumes `ε > 0`: with
`ε = 0` and a disconnected graph, `0 · ∞ = 0` in `ℝ≥0∞` would make `ε d`-privacy force
`K(x) ≤ K(x')` for disconnected `x, x'`. The Hamming graph is connected, and
`isEpsDP_hammingAdj_iff` holds for all `ε ≥ 0`.

## Notes on the paper

* [CABP], Section 2 (p. 6 of HAL v1), definition of a metric: the triangle inequality is printed
  as `d_X(x, z) ≤ d_X(x, y) + d_X(y, x)`; it should read `d_X(y, z)`. A typo with no effect.
* [CABP], Appendix C, proof of Proposition 3 (p. 28): `I = {i | x[i] ≠ x[i']}` and
  `d_V(x[i], x[i'])` should read `x'[i]`; the proof also uses `d_V(v, v) = 0` for `i ∉ I`. The
  proposition is true (`MetricDP.manhattanDist_div_le_hammingDist`).

## Not formalized

* The converses of Theorems 3 and 4 (maximally tight families) and Propositions 2, 9, 10.
* Section 4.2 onwards of [CABP]: Bayesian utility, optimal mechanisms (Theorems 8–13,
  Propositions 4–8), the counterexample of Figure 1, smart meters.
* [ABCP] Section 3.3 for more than two points; [ABCP] Sections 4.2–5 (discretization,
  truncation, Theorems 4.1–4.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {X Y Z W : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z} {mW : MeasurableSpace W}

/-- **`d`-privacy** (`d_X`-privacy, Definition 1 of Chatzikokolakis–Andrés–Bordenabe–Palamidessi):
a mechanism `K : Kernel X Z` satisfies `d`-privacy for a distinguishability function
`d : X → X → ℝ≥0∞` if `K(x)(E) ≤ e^{d(x, x')} K(x')(E)` for all secrets `x, x'` and all events
`E`, stated here as the inequality of measures `K x ≤ e^{d(x, x')} • K x'` (which covers all
sets `E ⊆ Z`, measurable or not, see `IsMetricDP.measure_le`). Following the paper, the
requirement is void when `d(x, x') = ∞` (extended metrics allow two secrets to be completely
distinguished). No metric axioms on `d` are needed for the definition. -/
def IsMetricDP (K : Kernel X Z) (d : X → X → ℝ≥0∞) : Prop :=
  ∀ ⦃x x'⦄, d x x' ≠ ∞ → K x ≤ ENNReal.ofReal (exp (d x x').toReal) • K x'

variable {K : Kernel X Z} {d d' : X → X → ℝ≥0∞}

/-- `d`-privacy on measurable events. -/
theorem isMetricDP_iff_forall_measurableSet : IsMetricDP K d ↔
    ∀ ⦃x x'⦄, d x x' ≠ ∞ → ∀ E : Set Z, MeasurableSet E →
      K x E ≤ ENNReal.ofReal (exp (d x x').toReal) * K x' E := by
  simp only [IsMetricDP, Measure.le_iff, smul_apply, smul_eq_mul]

/-- A `d`-private mechanism satisfies `K(x)(E) ≤ e^{d(x, x')} K(x')(E)` for every set `E`. -/
lemma IsMetricDP.measure_le (h : IsMetricDP K d) {x x' : X} (hd : d x x' ≠ ∞) (E : Set Z) :
    K x E ≤ ENNReal.ofReal (exp (d x x').toReal) * K x' E := by
  simpa using Measure.le_iff'.1 (h hd) E

namespace MetricDP

/-- The factor `e^t` for `t ∈ [0, ∞)`, as an element of `ℝ≥0∞`, is monotone in `t`. -/
lemma ofReal_exp_toReal_mono {s t : ℝ≥0∞} (hst : s ≤ t) (ht : t ≠ ∞) :
    ENNReal.ofReal (exp s.toReal) ≤ ENNReal.ofReal (exp t.toReal) :=
  ENNReal.ofReal_le_ofReal (exp_le_exp.2 (ENNReal.toReal_mono ht hst))

lemma ofReal_exp_toReal_add {s t : ℝ≥0∞} (hs : s ≠ ∞) (ht : t ≠ ∞) :
    ENNReal.ofReal (exp (s + t).toReal) =
      ENNReal.ofReal (exp s.toReal) * ENNReal.ofReal (exp t.toReal) := by
  rw [ENNReal.toReal_add hs ht, exp_add, ENNReal.ofReal_mul (exp_pos _).le]

end MetricDP

open MetricDP

/-- **Proposition 1** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi: if `d ≤ d'` pointwise,
then `d`-privacy implies `d'`-privacy. -/
theorem IsMetricDP.mono (h : IsMetricDP K d) (hdd' : ∀ x x', d x x' ≤ d' x x') :
    IsMetricDP K d' := fun x x' hd' ↦
  (h ((hdd' x x').trans_lt hd'.lt_top).ne).trans <| Measure.le_iff.2 fun E _ ↦ by
    simp only [smul_apply, smul_eq_mul]
    exact mul_le_mul_left (ofReal_exp_toReal_mono (hdd' x x') hd') _

/-- Every mechanism is `d`-private for `d ≡ ∞` (the requirement is void). -/
lemma isMetricDP_top (K : Kernel X Z) : IsMetricDP K fun _ _ ↦ ∞ := fun _ _ h ↦ absurd rfl h

/-- **Fact 5** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi, general form: if `H : Kernel Y Z`
is `d_Y`-private and the query `f : X → Y` satisfies `d_Y(f x, f x') ≤ d_X(x, x')`, then the
oblivious mechanism `H ∘ f` is `d_X`-private. -/
theorem IsMetricDP.comap {H : Kernel Y Z} {dY : Y → Y → ℝ≥0∞} (h : IsMetricDP H dY) {f : X → Y}
    (hf : Measurable f) (hfd : ∀ x x', dY (f x) (f x') ≤ d x x') :
    IsMetricDP (H.comap f hf) d := by
  intro x x' hd
  rw [Kernel.comap_apply, Kernel.comap_apply]
  refine (h ((hfd x x').trans_lt hd.lt_top).ne).trans <| Measure.le_iff.2 fun E _ ↦ ?_
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul_left (ofReal_exp_toReal_mono (hfd x x') hd) _

/-- **Fact 5** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi: if `f : X → Y` is `Δ`-sensitive
with respect to `d_X, d_Y` (Definition 4: `d_Y(f x, f x') ≤ Δ d_X(x, x')`) and `H` satisfies
`d_Y`-privacy, then `H ∘ f` satisfies `Δ d_X`-privacy. -/
theorem IsMetricDP.comap_of_sensitive {H : Kernel Y Z} {dY : Y → Y → ℝ≥0∞}
    (h : IsMetricDP H dY) {f : X → Y} (hf : Measurable f) {Δ : ℝ≥0}
    (hfd : ∀ x x', dY (f x) (f x') ≤ Δ * d x x') :
    IsMetricDP (H.comap f hf) fun x x' ↦ Δ * d x x' :=
  h.comap hf hfd

/-- **Post-processing**: if `K` is `d`-private, then so is `η ∘ₖ K` for every kernel `η`
(an arbitrary randomized mapping of the output). This is standard and used throughout the
paper, but not stated there as a numbered result. -/
theorem IsMetricDP.comp (h : IsMetricDP K d) (η : Kernel Z W) : IsMetricDP (η ∘ₖ K) d := by
  intro x x' hd
  refine Measure.le_iff.2 fun E hE ↦ ?_
  rw [smul_apply, smul_eq_mul, Kernel.comp_apply' _ _ _ hE, Kernel.comp_apply' _ _ _ hE,
    ← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' (h hd) le_rfl

/-- Post-processing by a measurable function. -/
theorem IsMetricDP.map (h : IsMetricDP K d) {φ : Z → W} (hφ : Measurable φ) :
    IsMetricDP (K.map φ) d := by
  rw [← Kernel.deterministic_comp_eq_map hφ]
  exact h.comp _

/-! ### Composition -/

namespace MetricDP

/-- Product measures multiply the factors of measure inequalities `μ ≤ a • μ'`, `ν ≤ b • ν'`. -/
lemma prod_le_smul {μ μ' : Measure Y} {ν ν' : Measure W} [SFinite ν']
    {a b : ℝ≥0∞} (hμ : μ ≤ a • μ') (hν : ν ≤ b • ν') : μ.prod ν ≤ (a * b) • μ'.prod ν' :=
  calc μ.prod ν ≤ (a • μ').prod (b • ν') := Measure.prod_mono hμ hν
    _ = (a * b) • μ'.prod ν' := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

end MetricDP

/-- **Sequential composition**: if `K₁` is `d₁`-private and `K₂` is `d₂`-private, then the
mechanism `x ↦ (K₁(x), K₂(x))` (independent runs on the same secret) is `(d₁ + d₂)`-private.
This is the metric form of the basic composition theorem of differential privacy; it is not a
numbered result of either paper. -/
theorem IsMetricDP.prod {K₁ : Kernel X Y} {K₂ : Kernel X W} [IsSFiniteKernel K₁]
    [IsSFiniteKernel K₂] {d₁ d₂ : X → X → ℝ≥0∞} (h₁ : IsMetricDP K₁ d₁)
    (h₂ : IsMetricDP K₂ d₂) : IsMetricDP (K₁ ×ₖ K₂) (d₁ + d₂) := by
  intro x x' hd
  obtain ⟨hd₁, hd₂⟩ := ENNReal.add_ne_top.1 hd
  rw [Kernel.prod_apply, Kernel.prod_apply, Pi.add_apply, Pi.add_apply,
    ofReal_exp_toReal_add hd₁ hd₂]
  exact MetricDP.prod_le_smul (h₁ hd₁) (h₂ hd₂)

/-- **Independent obfuscation of a pair of secrets** (Section 3.3 of Andrés–Bordenabe–
Chatzikokolakis–Palamidessi, "reporting the whole set", for two points): applying a
`d₁`-private `K₁` to `x₁` and, independently, a `d₂`-private `K₂` to `x₂` gives a mechanism on
pairs that is private for the sum distance `d₁(x₁, x₁') + d₂(x₂, x₂')`. -/
theorem IsMetricDP.parallelComp {X₁ X₂ Z₁ Z₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂]
    [MeasurableSpace Z₁] [MeasurableSpace Z₂] {K₁ : Kernel X₁ Z₁} {K₂ : Kernel X₂ Z₂}
    [IsSFiniteKernel K₁] [IsSFiniteKernel K₂] {d₁ : X₁ → X₁ → ℝ≥0∞} {d₂ : X₂ → X₂ → ℝ≥0∞}
    (h₁ : IsMetricDP K₁ d₁) (h₂ : IsMetricDP K₂ d₂) :
    IsMetricDP (K₁ ∥ₖ K₂) fun p p' ↦ d₁ p.1 p'.1 + d₂ p.2 p'.2 := by
  intro p p' hd
  obtain ⟨hd₁, hd₂⟩ := ENNReal.add_ne_top.1 hd
  rw [Kernel.parallelComp_apply, Kernel.parallelComp_apply, ofReal_exp_toReal_add hd₁ hd₂]
  exact MetricDP.prod_le_smul (h₁ hd₁) (h₂ hd₂)

/-- **Section 3.3 of Andrés–Bordenabe–Chatzikokolakis–Palamidessi** for `n = 2` points: if `K₀`
is `d`-private, then applying it independently to both points of a pair `(x₁, x₂)` is
`2 d_∞`-private, where `d_∞((x₁, x₂), (x₁', x₂')) = max (d(x₁, x₁')) (d(x₂, x₂'))`; for
`d = ε d₂` (Euclidean) this is the paper's "`nε`-geo-indistinguishability" with `n = 2`. -/
theorem IsMetricDP.parallelComp_self {K₀ : Kernel X Z} [IsSFiniteKernel K₀]
    (h : IsMetricDP K₀ d) :
    IsMetricDP (K₀ ∥ₖ K₀) fun p p' ↦ 2 * max (d p.1 p'.1) (d p.2 p'.2) :=
  (h.parallelComp h).mono fun p p' ↦ by
    rw [two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)

/-! ### Differential privacy is `ε d`-privacy for the graph distance -/

namespace MetricDP

variable {𝒟 : Type*} {Adj : 𝒟 → 𝒟 → Prop} {x x' : 𝒟} {k : ℕ}

/-- The distance induced by the graph `(𝒟, Adj)` (Section 2 of Chatzikokolakis–Andrés–
Bordenabe–Palamidessi): the least `k` such that `x` and `x'` are joined by a chain of `k`
neighbouring (or identical) steps (`IsKNeighbour Adj k x x'`), and `∞` if there is none. -/
noncomputable def graphDist (Adj : 𝒟 → 𝒟 → Prop) (x x' : 𝒟) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (_ : IsKNeighbour Adj k x x'), (k : ℝ≥0∞)

lemma graphDist_le (h : IsKNeighbour Adj k x x') : graphDist Adj x x' ≤ k :=
  iInf₂_le k h

lemma graphDist_le_one (h : Adj x x') : graphDist Adj x x' ≤ 1 := by
  simpa using graphDist_le (.succ (.zero x) (Or.inl h))

/-- A finite graph distance is attained by a chain. -/
lemma exists_isKNeighbour_of_graphDist_ne_top (h : graphDist Adj x x' ≠ ∞) :
    ∃ k, IsKNeighbour Adj k x x' ∧ graphDist Adj x x' = k := by
  classical
  have hex : ∃ k, IsKNeighbour Adj k x x' := by
    by_contra hne
    exact h (by simp [graphDist, not_exists.1 hne])
  exact ⟨Nat.find hex, Nat.find_spec hex, le_antisymm (graphDist_le (Nat.find_spec hex))
    (le_iInf₂ fun k hk ↦ Nat.cast_le.2 (Nat.find_min' hex hk))⟩

/-- Monotonicity of `μ ↦ a • μ` in the scalar. -/
lemma smul_le_smul_of_le {a b : ℝ≥0∞} (hab : a ≤ b) (μ : Measure Z) : a • μ ≤ b • μ :=
  Measure.le_iff.2 fun E _ ↦ by
    simp only [smul_apply, smul_eq_mul]
    exact mul_le_mul_left hab _

end MetricDP

open MetricDP

/-- Group privacy for a pure `ε`-DP finite kernel, as an inequality of measures: datasets joined
by `k` neighbouring steps satisfy `M x ≤ e^{kε} M x'`. -/
lemma MetricDP.le_smul_of_isEpsDP_of_isKNeighbour {𝒟 : Type*} [MeasurableSpace 𝒟]
    {M : Kernel 𝒟 Z} [IsFiniteKernel M] {Adj : 𝒟 → 𝒟 → Prop} {ε : ℝ} (h : IsEpsDP M Adj ε)
    (hε : 0 ≤ ε) {k : ℕ} {x x' : 𝒟} (hk : IsKNeighbour Adj k x x') :
    M x ≤ ENNReal.ofReal (exp (k * ε)) • M x' :=
  isEpsDP_iff_le_smul.1 (h.group hε k) hk

/-- **Differential privacy as metric privacy for an arbitrary adjacency** (a generalization of
Section 2 of Chatzikokolakis–Andrés–Bordenabe–Palamidessi, below equation (1), which states it
for Hamming adjacency, see `isEpsDP_hammingAdj_iff`): for an arbitrary neighbouring relation
`Adj`, a finite kernel is `ε`-DP iff it is `ε d_Adj`-private, where `d_Adj` is the distance
induced by the graph `(𝒟, Adj)` (`graphDist`). The direction `⟹` is group privacy along a
shortest chain. Here `ε > 0`: for `ε = 0` the direction `⟹` fails between disconnected
datasets, since `0 · ∞ = 0` in `ℝ≥0∞`. -/
theorem isEpsDP_iff_isMetricDP_graphDist {𝒟 : Type*} [MeasurableSpace 𝒟] {M : Kernel 𝒟 Z}
    [IsFiniteKernel M] {Adj : 𝒟 → 𝒟 → Prop} {ε : ℝ≥0} (hε : 0 < ε) :
    IsEpsDP M Adj ε ↔ IsMetricDP M fun x x' ↦ ε * graphDist Adj x x' := by
  refine ⟨fun h x x' hd ↦ ?_, fun h ↦ isEpsDP_iff_le_smul.2 fun x x' hA ↦ ?_⟩
  · beta_reduce at hd ⊢
    have hg : graphDist Adj x x' ≠ ∞ := fun hg ↦ hd <| by
      rw [hg, ENNReal.mul_top (by exact_mod_cast hε.ne')]
    obtain ⟨k, hk, hgk⟩ := exists_isKNeighbour_of_graphDist_ne_top hg
    rw [hgk, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast, mul_comm]
    exact MetricDP.le_smul_of_isEpsDP_of_isKNeighbour h ε.2 hk
  · have hle : (ε : ℝ≥0∞) * graphDist Adj x x' ≤ ε := by
      simpa using mul_le_mul_right (graphDist_le_one hA) (ε : ℝ≥0∞)
    refine (h (hle.trans_lt ENNReal.coe_lt_top).ne).trans (smul_le_smul_of_le ?_ _)
    simpa using ofReal_exp_toReal_mono hle ENNReal.coe_ne_top

/-! ### Standard differential privacy: the Hamming metric -/

namespace MetricDP

variable {ι V : Type*} [Fintype ι] [DecidableEq V]

/-- Adjacency of databases `x, x' : ι → V` (records indexed by `ι`, Section 2 of
Chatzikokolakis–Andrés–Bordenabe–Palamidessi, with `ι = 1..n`): `x ∼_h x'` iff they differ in
exactly one record. -/
def HammingAdj (x x' : ι → V) : Prop :=
  hammingDist x x' = 1

/-- Along a chain of `k` Hamming-adjacent steps, the Hamming distance is at most `k`. -/
lemma hammingDist_le_of_isKNeighbour {k : ℕ} {x x' : ι → V}
    (h : IsKNeighbour HammingAdj k x x') : hammingDist x x' ≤ k := by
  induction h with
  | zero => simp
  | @succ k S T U _ hTU ih =>
    refine (hammingDist_triangle S T U).trans ?_
    rcases hTU with hTU | rfl
    · rw [show hammingDist T U = 1 from hTU]
      omega
    · simpa using ih.trans k.le_succ

/-- Databases at Hamming distance `n` are joined by a chain of `n` adjacent steps (change one
differing record at a time). -/
lemma isKNeighbour_hammingDist (x x' : ι → V) :
    IsKNeighbour HammingAdj (hammingDist x x') x x' := by
  classical
  suffices ∀ n (x' : ι → V), hammingDist x x' = n → IsKNeighbour HammingAdj n x x' from
    this _ x' rfl
  intro n
  induction n with
  | zero =>
    intro x' hx'
    rw [hammingDist_eq_zero.1 hx']
    exact .zero x'
  | succ n ih =>
    intro x' hx'
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
      by_contra! hc
      exact absurd (hammingDist_eq_zero.2 (funext hc)) (by omega)
    set y := Function.update x' i (x i) with hy
    have h₁ : hammingDist x y = n := by
      have : ({j | x j ≠ y j} : Finset ι) = ({j | x j ≠ x' j} : Finset ι).erase i := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp [hy]
        · simp [hy, hj]
      rw [hammingDist, this, Finset.card_erase_of_mem (by simpa using hi), ← hammingDist, hx']
      rfl
    have h₂ : HammingAdj y x' := by
      have : ({j | y j ≠ x' j} : Finset ι) = {i} := by
        ext j
        by_cases hj : j = i
        · subst hj
          simpa [hy] using hi
        · simp [hy, hj]
      rw [HammingAdj, hammingDist, this, Finset.card_singleton]
    exact .succ (ih y h₁) (Or.inl h₂)

/-- The distance induced by the Hamming graph `(V^ι, ∼_h)` is the Hamming distance
(Section 2 of Chatzikokolakis–Andrés–Bordenabe–Palamidessi). -/
theorem graphDist_hammingAdj (x x' : ι → V) :
    graphDist HammingAdj x x' = hammingDist x x' :=
  le_antisymm (graphDist_le (isKNeighbour_hammingDist x x'))
    (le_iInf₂ fun _ hk ↦ Nat.cast_le.2 (hammingDist_le_of_isKNeighbour hk))

end MetricDP

/-- **Standard differential privacy is `ε d_h`-privacy** (Section 2 of Chatzikokolakis–Andrés–
Bordenabe–Palamidessi, below equation (1); Section 3: "differential privacy … can be retrieved
as `X = Vⁿ`, `d_X = ε d_h`"): a finite kernel `M` on databases `ι → V` is `ε`-differentially
private for Hamming adjacency (equation (1)) iff `M(x)(Z) ≤ e^{ε d_h(x, x')} M(x')(Z)` for all
databases `x, x'`. The direction `⟹` contains group privacy. Here `ε ≥ 0` is arbitrary. -/
theorem isEpsDP_hammingAdj_iff {ι V : Type*} [Fintype ι] [DecidableEq V] [MeasurableSpace V]
    {M : Kernel (ι → V) Z} [IsFiniteKernel M] (ε : ℝ≥0) :
    IsEpsDP M MetricDP.HammingAdj ε ↔
      IsMetricDP M fun x x' ↦ ε * (hammingDist x x' : ℝ≥0∞) := by
  refine ⟨fun h x x' _ ↦ ?_, fun h ↦ isEpsDP_iff_le_smul.2 fun x x' hA ↦ ?_⟩
  · beta_reduce
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast, mul_comm]
    exact MetricDP.le_smul_of_isEpsDP_of_isKNeighbour h ε.2
      (MetricDP.isKNeighbour_hammingDist x x')
  · have hA' : hammingDist x x' = 1 := hA
    simpa [hA'] using h (x := x) (x' := x') (by simp [hA'])

/-! ### Tight chains and uniform sensitivity -/

namespace MetricDP

/-- The `d`-private inequality propagates along a chain `c 0, c 1, …, c n`: if it holds for all
consecutive pairs and the length `∑_{i < n} d(c i, c (i + 1))` of the chain is finite, then
`K(c 0) ≤ e^{length} K(c n)`. -/
lemma le_smul_of_chain {c : ℕ → X} {n : ℕ}
    (hfin : ∑ i ∈ Finset.range n, d (c i) (c (i + 1)) ≠ ∞)
    (h : ∀ i < n, d (c i) (c (i + 1)) ≠ ∞ →
      K (c i) ≤ ENNReal.ofReal (exp (d (c i) (c (i + 1))).toReal) • K (c (i + 1))) :
    K (c 0) ≤ ENNReal.ofReal (exp (∑ i ∈ Finset.range n, d (c i) (c (i + 1))).toReal) •
      K (c n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ] at hfin ⊢
    obtain ⟨h₁, h₂⟩ := ENNReal.add_ne_top.1 hfin
    refine (ih h₁ fun i hi ↦ h i (by omega)).trans ?_
    rw [ofReal_exp_toReal_add h₁ h₂, ← smul_smul]
    exact Measure.le_iff.2 fun E hE ↦ by
      simpa [smul_apply, smul_eq_mul] using
        mul_le_mul_right (Measure.le_iff.1 (h n n.lt_succ_self h₂) E hE) _

end MetricDP

/-- **Lemma 2** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi: if `c 0 = x, …, c n = x'` is a
tight chain (`∑_{i < n} d(c i, c (i + 1)) = d(x, x')`) and `K` satisfies the `d`-privacy
inequality for all consecutive elements of the chain, then it satisfies it for `x, x'`. Like the
paper's statement, this is one-directional (it bounds `K(x)` by `K(x')`); the bound in the other
direction follows by applying it to the reversed chain, which is tight when `d` is symmetric. -/
theorem MetricDP.le_smul_of_tight_chain {c : ℕ → X} {n : ℕ} {x x' : X} (hc₀ : c 0 = x)
    (hcn : c n = x') (htight : ∑ i ∈ Finset.range n, d (c i) (c (i + 1)) = d x x')
    (h : ∀ i < n, d (c i) (c (i + 1)) ≠ ∞ →
      K (c i) ≤ ENNReal.ofReal (exp (d (c i) (c (i + 1))).toReal) • K (c (i + 1)))
    (hd : d x x' ≠ ∞) : K x ≤ ENNReal.ofReal (exp (d x x').toReal) • K x' := by
  subst hc₀ hcn
  rw [← htight] at hd ⊢
  exact MetricDP.le_smul_of_chain hd h

/-- Two query values `y, y'` are `Δ`-expansive for `f : X → Y` (Definition 5 of
Chatzikokolakis–Andrés–Bordenabe–Palamidessi) if `d_Y(y, y') = Δ d_X(x, x')` for some
`x ∈ f⁻¹(y)`, `x' ∈ f⁻¹(y')`. -/
def MetricDP.IsExpansive (f : X → Y) (dX : X → X → ℝ≥0∞) (dY : Y → Y → ℝ≥0∞) (Δ : ℝ≥0)
    (y y' : Y) : Prop :=
  ∃ x x', f x = y ∧ f x' = y' ∧ dY y y' = Δ * dX x x'

/-- `f : X → Y` is uniformly `Δ`-sensitive with respect to `d_X, d_Y` (Definition 5 of
Chatzikokolakis–Andrés–Bordenabe–Palamidessi): it is `Δ`-sensitive (Definition 4) and any two
`y, y' : Y` are joined by a tight chain `c 0 = y, …, c n = y'` whose consecutive elements are
`Δ`-expansive. -/
def MetricDP.IsUniformlySensitive (f : X → Y) (dX : X → X → ℝ≥0∞) (dY : Y → Y → ℝ≥0∞)
    (Δ : ℝ≥0) : Prop :=
  (∀ x x', dY (f x) (f x') ≤ Δ * dX x x') ∧
    ∀ y y', ∃ (n : ℕ) (c : ℕ → Y), c 0 = y ∧ c n = y' ∧
      ∑ i ∈ Finset.range n, dY (c i) (c (i + 1)) = dY y y' ∧
      ∀ i < n, MetricDP.IsExpansive f dX dY Δ (c i) (c (i + 1))

/-- **Theorem 6** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi: if the query `f` is
uniformly `Δ`-sensitive with respect to `d_X, d_Y`, then `H` satisfies `d_Y`-privacy if and only
if the oblivious mechanism `H ∘ f` satisfies `Δ d_X`-privacy. -/
theorem MetricDP.isMetricDP_comap_iff {H : Kernel Y Z} {dY : Y → Y → ℝ≥0∞} {f : X → Y}
    (hf : Measurable f) {Δ : ℝ≥0} (hu : MetricDP.IsUniformlySensitive f d dY Δ) :
    IsMetricDP H dY ↔ IsMetricDP (H.comap f hf) fun x x' ↦ Δ * d x x' := by
  refine ⟨fun h ↦ h.comap_of_sensitive hf hu.1, fun h y y' hd ↦ ?_⟩
  obtain ⟨n, c, hc₀, hcn, htight, hexp⟩ := hu.2 y y'
  refine MetricDP.le_smul_of_tight_chain hc₀ hcn htight (fun i hi hdi ↦ ?_) hd
  obtain ⟨x, x', hx, hx', hdx⟩ := hexp i hi
  rw [hdx] at hdi ⊢
  have := h (x := x) (x' := x') hdi
  rwa [Kernel.comap_apply, Kernel.comap_apply, hx, hx'] at this

/-! ### Bayesian characterizations (direction `⟹`) -/

/-- The real form of `d`-privacy for a finite kernel. -/
lemma IsMetricDP.measureReal_le [IsFiniteKernel K] (h : IsMetricDP K d) {x x' : X}
    (hd : d x x' ≠ ∞) (E : Set Z) : (K x).real E ≤ exp (d x x').toReal * (K x').real E := by
  have := ENNReal.toReal_mono (by finiteness) (h.measure_le hd E)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at this

namespace MetricDP

/-- The posterior `σ = Bayes(p, K, E)` (Section 2 of Chatzikokolakis–Andrés–Bordenabe–
Palamidessi), `σ(x) = p(x) K(x)(E) / ∑_{x'} p(x') K(x')(E)`, of a prior `p` supported in the
finite set `S` (the sum runs over `S`), after observing the event `E`. -/
noncomputable def bayes (S : Finset X) (p : X → ℝ) (K : Kernel X Z) (E : Set Z) (x : X) : ℝ :=
  p x * (K x).real E / ∑ x' ∈ S, p x' * (K x').real E

/-- The restriction `μ|_N(x) = μ(x) / μ(N)` of a finitely supported distribution `μ` to a
finite set `N` (Section 2 of Chatzikokolakis–Andrés–Bordenabe–Palamidessi, `p|_N(x) = p(x|N)`;
meaningful for `x ∈ N`). -/
noncomputable def restrictTo (N : Finset X) (μ : X → ℝ) (x : X) : ℝ :=
  μ x / ∑ x' ∈ N, μ x'

lemma restrictTo_bayes {S N : Finset X} {p : X → ℝ} {E : Set Z} (hNS : N ⊆ S)
    (hp : ∀ x, 0 ≤ p x) (hpos : 0 < ∑ x' ∈ N, p x' * (K x').real E) (x : X) :
    restrictTo N (bayes S p K E) x = p x * (K x).real E / ∑ x' ∈ N, p x' * (K x').real E := by
  have hT : 0 < ∑ x' ∈ S, p x' * (K x').real E :=
    hpos.trans_le <| Finset.sum_le_sum_of_subset_of_nonneg hNS fun i _ _ ↦
      mul_nonneg (hp i) measureReal_nonneg
  unfold restrictTo bayes
  rw [← Finset.sum_div, div_div_div_cancel_right₀ hT.ne']

end MetricDP

open MetricDP

/-- **Theorem 4** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi (Theorem 3.2 of
Andrés–Bordenabe–Chatzikokolakis–Palamidessi for geo-indistinguishability), direction `⟹`,
for finitely supported priors: if `K` is `d`-private, then for every finite neighbourhood `N`
of diameter at most `D` (`d(x, x') ≤ D` on `N`), every prior `p` supported in a finite set
`S ⊇ N` and every event `E` with `σ(N) > 0`, the informed adversary's restricted posterior and
prior satisfy `e^{-D} p|_N(x) ≤ σ|_N(x) ≤ e^D p|_N(x)` for all `x ∈ N`, where
`σ = Bayes(p, K, E)`. This pointwise bound is the content of the paper's proof. The paper's
conclusion `d_P(p|_N, σ|_N) ≤ D` (a bound on all subsets of `N`, via Lemma 1) is not formalized,
nor is the converse for maximally tight families of neighbourhoods. -/
theorem IsMetricDP.restrictTo_bayes_le [IsFiniteKernel K] (h : IsMetricDP K d) {S N : Finset X}
    (hNS : N ⊆ S) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) {E : Set Z} {D : ℝ≥0}
    (hD : ∀ x ∈ N, ∀ x' ∈ N, d x x' ≤ D) (hpos : 0 < ∑ x' ∈ N, p x' * (K x').real E)
    {x : X} (hx : x ∈ N) :
    exp (-D) * restrictTo N p x ≤ restrictTo N (bayes S p K E) x ∧
      restrictTo N (bayes S p K E) x ≤ exp D * restrictTo N p x := by
  have hle {u v : X} (hu : u ∈ N) (hv : v ∈ N) : (K u).real E ≤ exp D * (K v).real E := by
    have hd : d u v ≠ ∞ := ((hD u hu v hv).trans_lt ENNReal.coe_lt_top).ne
    refine (h.measureReal_le hd E).trans (mul_le_mul_of_nonneg_right ?_ measureReal_nonneg)
    exact exp_le_exp.2 (by simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (hD u hu v hv))
  have hpN : 0 < ∑ x' ∈ N, p x' := by
    by_contra! h0
    have h0' : ∀ i ∈ N, p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hp i).1 (le_antisymm h0 (Finset.sum_nonneg
        fun i _ ↦ hp i))
    exact hpos.ne' (Finset.sum_eq_zero fun i hi ↦ by simp [h0' i hi])
  rw [restrictTo_bayes hNS hp hpos, restrictTo]
  set a := (K x).real E
  set Sa := ∑ x' ∈ N, p x' * (K x').real E
  set Sp := ∑ x' ∈ N, p x'
  -- `a Sp ≤ e^D Sa` and `Sa ≤ e^D a Sp`
  have h₁ : a * Sp ≤ exp D * Sa := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ by
      nlinarith [hle hx hi, hp i]
  have h₂ : Sa ≤ exp D * a * Sp := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ by
      nlinarith [hle hi hx, hp i]
  have hpx := hp x
  constructor
  · rw [← mul_div_assoc, div_le_div_iff₀ hpN hpos]
    have : exp (-D) * Sa ≤ a * Sp := by
      have := mul_le_mul_of_nonneg_left h₂ (exp_pos (-(D : ℝ))).le
      rwa [← mul_assoc, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul] at this
    nlinarith
  · rw [← mul_div_assoc, div_le_div_iff₀ hpos hpN]
    nlinarith

namespace MetricDP

private lemma div_le_sq_mul_div {q a b Ta Tb c : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hTa : 0 < Ta) (hTb : 0 < Tb) (hc : 0 ≤ c) (h₁ : b ≤ c * a) (h₂ : Ta ≤ c * Tb) :
    q * b / Tb ≤ c ^ 2 * (q * a / Ta) := by
  rw [← mul_div_assoc, div_le_div_iff₀ hTb hTa]
  have := mul_le_mul h₁ h₂ hTa.le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left this hq]

end MetricDP

/-- **Theorem 3** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi (Theorem 3.1 of
Andrés–Bordenabe–Chatzikokolakis–Palamidessi for geo-indistinguishability), direction `⟹`,
for finitely supported priors and symmetric `d` (as the paper's metrics are): if `K` is
`d`-private and the hiding function `φ` moves every secret by at most `D` (`d(x, φ x) ≤ D`, the
paper's `d_X(φ) = sup_x d_X(x, φ x)`), then for every prior `p` supported in a finite set `S`
and every event `E` of positive probability under `K` (its probability under `K ∘ φ` is then
positive too), the posteriors `σ₁ = Bayes(p, K, E)` and `σ₂ = Bayes(p, K ∘ φ, E)` satisfy
`σ₂(x) ≤ e^{2D} σ₁(x)` and `σ₁(x) ≤ e^{2D} σ₂(x)` for every `x`. This pointwise bound is the
content of the paper's proof. The paper's conclusion `d_P(σ₁, σ₂) ≤ 2D` (a bound on all sets,
via Lemma 1) is not formalized, nor is the converse for maximally tight families of hiding
functions. -/
theorem IsMetricDP.bayes_comap_le [IsFiniteKernel K] (h : IsMetricDP K d)
    (hsymm : ∀ x x', d x x' = d x' x) {φ : X → X} (hφ : Measurable φ) {D : ℝ≥0}
    (hD₁ : ∀ x, d x (φ x) ≤ D) (S : Finset X) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) {E : Set Z}
    (h₁ : 0 < ∑ x ∈ S, p x * (K x).real E) (x : X) :
    bayes S p (K.comap φ hφ) E x ≤ exp (2 * D) * bayes S p K E x ∧
      bayes S p K E x ≤ exp (2 * D) * bayes S p (K.comap φ hφ) E x := by
  have hle {u v : X} (huv : d u v ≤ D) : (K u).real E ≤ exp D * (K v).real E := by
    have hd : d u v ≠ ∞ := (huv.trans_lt ENNReal.coe_lt_top).ne
    refine (h.measureReal_le hd E).trans (mul_le_mul_of_nonneg_right ?_ measureReal_nonneg)
    exact exp_le_exp.2 (by simpa using ENNReal.toReal_mono ENNReal.coe_ne_top huv)
  have hsum₁ : ∑ x ∈ S, p x * (K x).real E ≤ exp D * ∑ x ∈ S, p x * (K (φ x)).real E := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by nlinarith [hle (hD₁ i), hp i]
  have hD₂ (x : X) : d (φ x) x ≤ D := by rw [hsymm]; exact hD₁ x
  have hsum₂ : ∑ x ∈ S, p x * (K (φ x)).real E ≤ exp D * ∑ x ∈ S, p x * (K x).real E := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by nlinarith [hle (hD₂ i), hp i]
  have h₂ : 0 < ∑ x ∈ S, p x * (K (φ x)).real E := by
    by_contra! h0
    nlinarith [exp_pos (D : ℝ)]
  have hexp : exp (2 * D) = exp D ^ 2 := by rw [← exp_nat_mul]; norm_num
  simp only [bayes, Kernel.comap_apply]
  rw [hexp]
  exact ⟨div_le_sq_mul_div (hp x) measureReal_nonneg h₁ h₂ (exp_pos _).le (hle (hD₂ x)) hsum₁,
    div_le_sq_mul_div (hp x) measureReal_nonneg h₂ h₁ (exp_pos _).le (hle (hD₁ x)) hsum₂⟩

/-! ### The (normalized) Manhattan metric on databases -/

namespace MetricDP

variable {ι V : Type*} [Fintype ι]

/-- The Manhattan metric `d₁(x, x') = ∑_i d_V(x[i], x'[i])` on databases `x, x' : ι → V`
induced by a distance `d_V` on the universe of values (Section 5.1 of Chatzikokolakis–Andrés–
Bordenabe–Palamidessi). The normalized Manhattan metric of the paper is `d₁ / d_V(V)`. -/
noncomputable def manhattanDist (dV : V → V → ℝ≥0∞) (x x' : ι → V) : ℝ≥0∞ :=
  ∑ i, dV (x i) (x' i)

/-- **Proposition 3** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi, metric inequality: the
normalized Manhattan metric is at most the Hamming metric, `d₁ / M ≤ d_h`, whenever `d_V` vanishes
on the diagonal and `M` bounds `d_V` (the paper takes `M = d_V(V)`, the diameter of `V`). -/
theorem manhattanDist_div_le_hammingDist [DecidableEq V] {dV : V → V → ℝ≥0∞}
    (hself : ∀ v, dV v v = 0) {M : ℝ≥0∞} (hM : ∀ v v', dV v v' ≤ M) (x x' : ι → V) :
    manhattanDist dV x x' / M ≤ hammingDist x x' := by
  refine ENNReal.div_le_of_le_mul ?_
  calc manhattanDist dV x x' ≤ ∑ i, if x i ≠ x' i then M else 0 :=
        Finset.sum_le_sum fun i _ ↦ by
          by_cases h : x i = x' i
          · simp [h, hself]
          · simpa [h] using hM (x i) (x' i)
    _ = hammingDist x x' * M := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hammingDist]

end MetricDP

open MetricDP

/-- **Proposition 3** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi: `ε d̃₁`-privacy for the
normalized Manhattan metric `d̃₁ = d₁ / d_V(V)` implies `ε d_h`-privacy, hence (for a finite
kernel) standard `ε`-differential privacy (`isEpsDP_hammingAdj_iff`). Here `M` is any upper bound
on `d_V` (the paper's `d_V(V)`), and `d_V` vanishes on the diagonal. -/
theorem IsMetricDP.isEpsDP_of_manhattanDist {ι V : Type*} [Fintype ι] [DecidableEq V]
    [MeasurableSpace V] {M' : Kernel (ι → V) Z} [IsFiniteKernel M'] {dV : V → V → ℝ≥0∞}
    (hself : ∀ v, dV v v = 0) {M : ℝ≥0∞} (hM : ∀ v v', dV v v' ≤ M) {ε : ℝ≥0}
    (h : IsMetricDP M' fun x x' ↦ ε * (manhattanDist dV x x' / M)) :
    IsEpsDP M' HammingAdj ε :=
  (isEpsDP_hammingAdj_iff ε).2 <| h.mono fun x x' ↦
    mul_le_mul_right (manhattanDist_div_le_hammingDist hself hM x x') _

end InformationTheory
