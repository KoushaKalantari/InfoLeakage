/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.AdvancedComposition.Basic
public import InfoLeakage.ForMathlib.MeasurableSum
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Privacy filters and odometers: basic composition with adaptively chosen parameters

This file formalizes the framework of composition with adaptively chosen privacy parameters and
its basic-composition theorem from

* R. Rogers, A. Roth, J. Ullman and S. Vadhan, *Privacy odometers and filters: pay-as-you-go
  composition*, NeurIPS 2016, arXiv:1605.08294 (result numbers follow arXiv v3).

In round `n` of the game, an adversary chooses, as a function of the outputs of the earlier
rounds (its *history*), a privacy parameter `ε n h` and an `ε n h`-DP mechanism, which is then run
on the secret input. Since the parameters are random, the composed game is not `ε`-DP for any
fixed `ε`; the paper introduces two ways to control its privacy loss. A *privacy filter* is a
stopping rule that halts the game before a global budget `ε_g` is exceeded; a *privacy odometer*
is a running bound on the realized privacy loss.

## Setting and modelling choices

* Output alphabets are countable with measurable singletons (the paper allows arbitrary ranges).
* As in Theorem 3.4, the mechanisms are pure DP (`δ_i = 0`); Lemma 3.3, which reduces the
  `(ε, δ)` case to this one, is not formalized.
* An adversary (`PrivacyFilter.Adversary`) is a family of history-indexed kernels
  `mech n : Kernel (𝒟 × (Fin n → H)) Y` together with the history-indexed parameters
  `eps n : (Fin n → H) → ℝ`, such that each mechanism `S ↦ mech n (S, h)` is `eps n h`-DP for a
  neighbouring relation `Adj` on `𝒟`. The game of Algorithm 2 (`AdaptParamComp`), in which the
  adversary also chooses the pair of neighbouring datasets and the mechanism in each round, is the
  case `𝒟 = Bool`, `Adj = (· ≠ ·)`: the adversary's choice in round `n` is then encoded by the two
  output distributions `mech n (b, h) = M_n(x_{n,b})`, `b ∈ {0, 1}`, and every pair of
  `ε`-indistinguishable distributions arises from such a choice. The definitions
  `IsPrivacyFilter` and `IsPrivacyOdometer` quantify over these adversaries.
* The adversary's choices are deterministic functions of the history. Informally (this
  reduction is not formalized), this covers a randomized adversary with countably many coin
  values whose coins `R_A` are part of the view, as in the paper: conditionally on `R_A = r` the
  game is that of a deterministic adversary `A_r`, so `P[V^b = (r, v)] = P[R_A = r] P[V_r^b = v]`,
  the privacy loss of `(r, v)` is that of `v` for `A_r`, and the probability of each bad event
  (point-wise or odometer) is the `P[R_A = r]`-weighted average of the probabilities of the
  corresponding events for the `A_r`, hence at most `δ_g`.
* The paper's `COMP_{ε_g,δ_g} : ℝ^{2k}_{≥0} → {HALT, CONT}` sees `(ε₁, 0, …, ε_k, 0)` in the pure
  case; here a filter is a predicate `C : (Fin k → ℝ) → Prop` on the vector of the `k` parameters
  (`C e` means `CONT`). Before round `i` the filter is queried on `(ε₀, …, ε_i, 0, …, 0)`
  (`PrivacyFilter.paddedEps`). Once it answers `HALT`, this round and all later ones output `⊥`,
  which is `Sum.inr ()` in the output alphabet `Y ⊕ Unit` of the filtered game (Algorithm 3).
* Point-wise indistinguishability (Definition 2.2) and the odometer event `|Loss(v)| > c` are
  stated in multiplicative form, `e^ε ν{z} < μ{z}`; for outcomes of positive probability this is
  exactly `log (μ{z} / ν{z}) > ε` (including the value `+∞` when `ν{z} = 0`), and outcomes of
  probability zero do not affect the probability of the event.
* The instance `MeasurableSingletonClass (Y ⊕ Unit)`, missing from Mathlib, is
  `Sum.instMeasurableSingletonClass` from `InfoLeakage.ForMathlib.MeasurableSum`.

## Main definitions

* `PrivacyFilter.Adversary`: an adversary of the adaptive-parameter composition game.
* `PrivacyFilter.adaptParamComp`: the view of Algorithm 2, `AdaptParamComp(A, k, ·)`.
* `PrivacyFilter.privacyFilterComp`: the view of Algorithm 3, `PrivacyFilterComp(A, k, ·; COMP)`.
* `PrivacyFilter.IsPointwiseIndist`: `(ε, δ)`-point-wise indistinguishability (Definition 2.2).
* `PrivacyFilter.IsPrivacyFilter`: a valid privacy filter (Definition 3.1, pure-DP adversaries).
* `PrivacyFilter.IsPrivacyOdometer`: a valid privacy odometer (Definition 3.2, pure-DP adversaries,
  real-valued odometers).
* `PrivacyFilter.basicFilter`: the filter of Theorem 3.4, `HALT` iff `∑ εᵢ > ε_g`.

## Main statements

* `PrivacyFilter.adaptiveCompose_apply_singleton_le`: in an adaptive composition with
  history-dependent parameters, `P[V⁰ = v] ≤ exp (∑ᵢ εᵢ(v_{<i})) P[V¹ = v]` for every view `v`
  (the inequality `|Loss(v)| ≤ ∑ᵢ εᵢ(v_{<i})` in the proof of Theorem 3.4).
* `PrivacyFilter.isPrivacyOdometer_sum`: **Theorem 3.4, first part**: `∑ εᵢ` is a valid privacy
  odometer for every `δ_g ≥ 0`.
* `PrivacyFilter.isEpsDP_privacyFilterComp_basicFilter`: for every adversary, the game run with
  the basic filter is `ε_g`-DP.
* `PrivacyFilter.isPrivacyFilter_basicFilter`: **Theorem 3.4, second part**: the basic filter is
  a valid privacy filter for all `ε_g, δ_g ≥ 0`.

As in the paper's proof, the views are in fact `(ε_g, 0)`-point-wise indistinguishable, and the
odometer event is empty. Nonnegativity of the per-round parameters `εᵢ` is not needed.

## Paper result → Lean name

* Definition 2.2 → `PrivacyFilter.IsPointwiseIndist`
* Algorithm 2 → `PrivacyFilter.adaptParamComp`; Algorithm 3 → `PrivacyFilter.privacyFilterComp`
* Definition 3.1 → `PrivacyFilter.IsPrivacyFilter`
* Definition 3.2 → `PrivacyFilter.IsPrivacyOdometer`
* Theorem 3.4 → `PrivacyFilter.isPrivacyOdometer_sum`, `PrivacyFilter.isPrivacyFilter_basicFilter`

The advanced-composition filter (Theorem 5.1), the odometers of Section 6 and the separation
between filters and odometers rely on martingale concentration and are not formalized.

## Notes on the paper

* Definition 3.1 (arXiv v3, page 9) quantifies over "all outcome sets `S`", but point-wise
  indistinguishability involves no outcome set; the quantifier is vacuous and harmless.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

namespace PrivacyFilter

open AdvancedComposition

variable {𝒟 H Y Z : Type*} [MeasurableSpace 𝒟] [MeasurableSpace H] [MeasurableSpace Y]
  [MeasurableSpace Z]

/-! ### Adaptive composition with history-dependent parameters -/

/-- The `k`-fold adaptive composition gives an output tuple `v` the probability
`∏_{n < k} N_n(S, (v₀, …, v_{n-1}))(v_n)`. -/
private lemma adaptiveCompose_apply_singleton [MeasurableSingletonClass Z]
    (N : (n : ℕ) → Kernel (𝒟 × (Fin n → Z)) Z) [∀ n, IsMarkovKernel (N n)] (k : ℕ) (S : 𝒟)
    (v : Fin k → Z) :
    adaptiveCompose N k S {v} = ∏ n : Fin k, N n (S, Fin.take n n.isLt.le v) {v n} := by
  induction k with
  | zero =>
    rw [adaptiveCompose_zero, Kernel.const_apply,
      Measure.dirac_apply_of_mem (Set.mem_singleton_iff.2 (Subsingleton.elim _ _))]
    simp
  | succ k ih =>
    have hpre : (fun p : (Fin k → Z) × Z ↦ (Fin.snoc p.1 p.2 : Fin (k + 1) → Z)) ⁻¹' {v} =
        {Fin.init v} ×ˢ {v (Fin.last k)} := by
      ext ⟨p, z⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
      constructor
      · rintro rfl
        simp
      · rintro ⟨rfl, rfl⟩
        exact Fin.snoc_init_self v
    rw [adaptiveCompose_succ, Kernel.map_apply' _ (measurable_snoc k) _
      (measurableSet_singleton v), hpre, Kernel.compProd_apply_prod (measurableSet_singleton _)
      (measurableSet_singleton _), lintegral_singleton, ih, Fin.prod_univ_castSucc, mul_comm]
    rfl

/-- **The privacy loss of an adaptive composition is at most the sum of the realized
parameters** (the inequality `|Loss(v)| ≤ ∑ᵢ εᵢ(v_{<i})` in the proof of Theorem 3.4 of
Rogers–Roth–Ullman–Vadhan). If, in every round `n` and for every history `x`, the round-`n`
output distributions on the inputs `S` and `S'` satisfy `P[N_n(S, x) = z] ≤ e^{ε n x}
P[N_n(S', x) = z]`, then every view `v` of the `k`-fold adaptive composition satisfies
`P[V(S) = v] ≤ exp (∑_{n < k} ε n (v₀, …, v_{n-1})) P[V(S') = v]`. -/
theorem adaptiveCompose_apply_singleton_le [MeasurableSingletonClass Z]
    (N : (n : ℕ) → Kernel (𝒟 × (Fin n → Z)) Z) [∀ n, IsMarkovKernel (N n)]
    (ε : (n : ℕ) → (Fin n → Z) → ℝ) {S S' : 𝒟}
    (h : ∀ n (x : Fin n → Z) (z : Z),
      N n (S, x) {z} ≤ ENNReal.ofReal (exp (ε n x)) * N n (S', x) {z})
    (k : ℕ) (v : Fin k → Z) :
    adaptiveCompose N k S {v} ≤
      ENNReal.ofReal (exp (∑ n : Fin k, ε n (Fin.take n n.isLt.le v))) *
        adaptiveCompose N k S' {v} := by
  rw [adaptiveCompose_apply_singleton, adaptiveCompose_apply_singleton, exp_sum,
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (exp_pos _).le, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod fun n _ ↦ h _ _ _

/-! ### Adversaries and the composition game -/

/-- An **adversary of the adaptive-parameter composition game** (Algorithm 2 of
Rogers–Roth–Ullman–Vadhan), for pure-DP mechanisms. In round `n`, given the history
`h : Fin n → H` of the earlier outputs, it chooses a privacy parameter `eps n h` and a mechanism
`S ↦ mech n (S, h)` with outputs in `Y` that is `eps n h`-DP for the neighbouring relation `Adj`.
The game of the paper is the case `𝒟 = Bool`, `Adj = (· ≠ ·)` (see the module documentation). -/
structure Adversary (𝒟 H Y : Type*) [MeasurableSpace 𝒟] [MeasurableSpace H] [MeasurableSpace Y]
    (Adj : 𝒟 → 𝒟 → Prop) where
  /-- The privacy parameter chosen in round `n` as a function of the history. -/
  eps : (n : ℕ) → (Fin n → H) → ℝ
  /-- The mechanism run in round `n`, as a function of the input and the history. -/
  mech : (n : ℕ) → Kernel (𝒟 × (Fin n → H)) Y
  /-- The mechanisms are Markov kernels. -/
  isMarkovKernel_mech : ∀ n, IsMarkovKernel (mech n)
  /-- The mechanism chosen in round `n` after history `h` is `eps n h`-DP. -/
  isEpsDP_mech : ∀ n h, IsEpsDP ((mech n).sectL h) Adj (eps n h)

attribute [instance] Adversary.isMarkovKernel_mech

variable {Adj : 𝒟 → 𝒟 → Prop}

/-- The round-`n` output distributions of an adversary on neighbouring inputs satisfy the
`e^ε` bound on every event. -/
lemma Adversary.apply_le (A : Adversary 𝒟 H Y Adj) {S S' : 𝒟} (hS : Adj S S') (n : ℕ)
    (h : Fin n → H) (E : Set Y) :
    A.mech n (S, h) E ≤ ENNReal.ofReal (exp (A.eps n h)) * A.mech n (S', h) E :=
  Measure.le_iff'.1 (isEpsDP_iff_le_smul.1 (A.isEpsDP_mech n h) hS) E

/-- The view `V^b` of the **adaptive-parameter composition game** `AdaptParamComp(A, k, b)`
(Algorithm 2 of Rogers–Roth–Ullman–Vadhan): the `k`-fold adaptive composition of the
adversary's mechanisms, as a kernel from the input `b` (or dataset) to the tuple of outputs. -/
noncomputable def adaptParamComp (A : Adversary 𝒟 Y Y Adj) (k : ℕ) : Kernel 𝒟 (Fin k → Y) :=
  adaptiveCompose A.mech k

instance (A : Adversary 𝒟 Y Y Adj) (k : ℕ) : IsMarkovKernel (adaptParamComp A k) :=
  isMarkovKernel_adaptiveCompose _ k

/-- The vector `(ε₀(v_{<0}), …, ε_{k-1}(v_{<k-1}))` of the parameters realized along a view
`v`. -/
def realizedEps (ε : (n : ℕ) → (Fin n → H) → ℝ) {k : ℕ} (v : Fin k → H) : Fin k → ℝ :=
  fun n ↦ ε n (Fin.take n n.isLt.le v)

/-- **Privacy loss along a view of the adaptive-parameter game** (proof of Theorem 3.4 of
Rogers–Roth–Ullman–Vadhan): for neighbouring `S, S'` and every view `v`,
`P[V(S) = v] ≤ exp (∑ᵢ εᵢ(v_{<i})) P[V(S') = v]`. -/
theorem adaptParamComp_apply_singleton_le [MeasurableSingletonClass Y]
    (A : Adversary 𝒟 Y Y Adj) {S S' : 𝒟} (hS : Adj S S') (k : ℕ) (v : Fin k → Y) :
    adaptParamComp A k S {v} ≤
      ENNReal.ofReal (exp (∑ n, realizedEps A.eps v n)) * adaptParamComp A k S' {v} :=
  adaptiveCompose_apply_singleton_le A.mech A.eps (fun n x _ ↦ A.apply_le hS n x _) k v

/-! ### Privacy odometers -/

/-- A **valid privacy odometer** (Definition 3.2 of Rogers–Roth–Ullman–Vadhan), for adversaries
with pure-DP mechanisms with outputs in `Y` and real-valued odometers `C`: for every adversary of
the `k`-round game, with probability at most `δ_g` over `v ∼ V⁰` the privacy loss
`Loss(v) = log (P[V⁰ = v] / P[V¹ = v])` satisfies `|Loss(v)| > C(ε₁(v), …, ε_k(v))`. The event
`|Loss(v)| > c` is written as `e^c P[V¹ = v] < P[V⁰ = v] ∨ e^c P[V⁰ = v] < P[V¹ = v]`, which
agrees with it on the outcomes of positive `V⁰`-probability. The output alphabet `Y` is countable
with measurable singletons (without them, `{v}` could have outer measure `1` for several `v` and
the condition would be meaningless). -/
@[nolint unusedArguments]
def IsPrivacyOdometer (Y : Type*) [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y]
    (k : ℕ) (C : (Fin k → ℝ) → ℝ) (δg : ℝ) : Prop :=
  ∀ A : Adversary Bool Y Y (· ≠ ·),
    (adaptParamComp A k false).real {v | ENNReal.ofReal (exp (C (realizedEps A.eps v))) *
        adaptParamComp A k true {v} < adaptParamComp A k false {v} ∨
      ENNReal.ofReal (exp (C (realizedEps A.eps v))) * adaptParamComp A k false {v} <
        adaptParamComp A k true {v}} ≤ δg

/-- **Theorem 3.4 of Rogers–Roth–Ullman–Vadhan, odometer part**: for every `δ_g ≥ 0`, the sum
`∑ᵢ εᵢ` of the realized parameters is a valid privacy odometer (for every countable output
alphabet `Y` with measurable singletons and every number of rounds `k`). In fact the event
`|Loss(v)| > ∑ᵢ εᵢ(v)` is empty. -/
theorem isPrivacyOdometer_sum [Countable Y] [MeasurableSingletonClass Y] (k : ℕ) {δg : ℝ}
    (hδg : 0 ≤ δg) :
    IsPrivacyOdometer Y k (fun e ↦ ∑ i, e i) δg := by
  intro A
  refine (measureReal_mono (s₂ := ∅) (fun v hv ↦ ?_) (by simp)).trans (by simpa using hδg)
  rcases hv with hv | hv
  · exact ((adaptParamComp_apply_singleton_le A (by decide : false ≠ true) k v).not_gt hv).elim
  · exact ((adaptParamComp_apply_singleton_le A (by decide : true ≠ false) k v).not_gt hv).elim

/-! ### Privacy filters -/

/-- **`(ε, δ)`-point-wise indistinguishability** (Definition 2.2 of Rogers–Roth–Ullman–Vadhan),
for probability measures on a countable alphabet with measurable singletons: with probability at
least `1 - δ` over `z ∼ μ`, `log (μ{z} / ν{z}) ≤ ε`, and with probability at least `1 - δ` over
`z ∼ ν`, `log (ν{z} / μ{z}) ≤ ε`. The event `log (μ{z} / ν{z}) > ε` is written
`e^ε ν{z} < μ{z}`, which agrees with it on the outcomes of positive `μ`-probability.

This differs from the literal text of Definition 2.2, which bounds `log (μ{z} / ν{z}) ≤ ε` both
under `z ∼ μ` and under `z ∼ ν`: here the ratio is reversed under `ν`, which is the two-sided
form of Kasiviswanathan–Smith [KS14]. For `ε ≥ 0` the two readings agree inside Definition 3.1,
which quantifies over both orders `(b, 1 - b)`: the literal clause under `ν` then follows from
the clause under `μ`, as `ν(E) ≤ e^{-ε} μ(E)` on the event `E = {z | e^ε ν{z} < μ{z}}`. -/
@[nolint unusedArguments]
def IsPointwiseIndist [Countable Z] [MeasurableSingletonClass Z] (μ ν : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ε δ : ℝ) : Prop :=
  μ.real {z | ENNReal.ofReal (exp ε) * ν {z} < μ {z}} ≤ δ ∧
    ν.real {z | ENNReal.ofReal (exp ε) * μ {z} < ν {z}} ≤ δ

/-- The vector `(ε₀, …, ε_i, 0, …, 0) : Fin k → ℝ` of the parameters chosen in rounds `0, …, i`
along the history `h` of length `n ≥ i`, padded with zeros; the parameter of round `j` is
evaluated on the first `j` entries of `h`. Before running round `i`, the filter of
Algorithm 3 of Rogers–Roth–Ullman–Vadhan is queried on this vector. -/
def paddedEps (ε : (n : ℕ) → (Fin n → H) → ℝ) (k : ℕ) {n : ℕ} (h : Fin n → H) (i : ℕ) :
    Fin k → ℝ :=
  fun j ↦ if hj : (j : ℕ) ≤ i ∧ (j : ℕ) ≤ n then ε j (Fin.take j hj.2 h) else 0

/-- The game with filter `C` is still running in round `n` after the history `h`: the filter
answered `CONT` in each of the rounds `0, …, n`. -/
def Runs {k : ℕ} (C : (Fin k → ℝ) → Prop) (ε : (n : ℕ) → (Fin n → H) → ℝ) {n : ℕ}
    (h : Fin n → H) : Prop :=
  ∀ i ≤ n, C (paddedEps ε k h i)

open scoped Classical in
/-- The kernel of round `n` of the **game with a privacy filter** (Algorithm 3 of
Rogers–Roth–Ullman–Vadhan): if the filter `C` has answered `CONT` in all rounds up to `n`, run the
adversary's mechanism (outputs `Sum.inl y`); otherwise output `⊥ = Sum.inr ()`. The adversary
sees the filtered history in `Y ⊕ Unit`; while the game runs, this history contains no `⊥`, so
its choices on histories containing `⊥` are never used. -/
noncomputable def filterRound [Countable Y] [MeasurableSingletonClass Y] {k : ℕ}
    (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj) (C : (Fin k → ℝ) → Prop) (n : ℕ) :
    Kernel (𝒟 × (Fin n → Y ⊕ Unit)) (Y ⊕ Unit) :=
  Kernel.piecewise (s := Set.univ ×ˢ {h | Runs C A.eps h})
    (MeasurableSet.univ.prod (Set.to_countable _).measurableSet)
    ((A.mech n).map Sum.inl) (Kernel.const _ (Measure.dirac (Sum.inr ())))

instance [Countable Y] [MeasurableSingletonClass Y] {k : ℕ} (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj)
    (C : (Fin k → ℝ) → Prop) (n : ℕ) : IsMarkovKernel (filterRound A C n) := by
  unfold filterRound
  have := Kernel.IsMarkovKernel.map (A.mech n) (measurable_inl (β := Unit))
  infer_instance

/-- The view `V_F^b` of the **game with a privacy filter** `PrivacyFilterComp(A, k, b; COMP)`
(Algorithm 3 of Rogers–Roth–Ullman–Vadhan), as a kernel from the input to the `k` outputs in
`Y ⊕ Unit`, where `Sum.inr ()` is `⊥`. -/
noncomputable def privacyFilterComp [Countable Y] [MeasurableSingletonClass Y] {k : ℕ}
    (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj) (C : (Fin k → ℝ) → Prop) :
    Kernel 𝒟 (Fin k → Y ⊕ Unit) :=
  adaptiveCompose (filterRound A C) k

instance [Countable Y] [MeasurableSingletonClass Y] {k : ℕ} (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj)
    (C : (Fin k → ℝ) → Prop) : IsMarkovKernel (privacyFilterComp A C) :=
  isMarkovKernel_adaptiveCompose _ k

/-- A **valid privacy filter** (Definition 3.1 of Rogers–Roth–Ullman–Vadhan) for adversaries
with pure-DP mechanisms with outputs in `Y`: for every adversary of the `k`-round game and both
values of `b`, the views `V_F^b` and `V_F^{1-b}` of the game with filter `C` are
`(ε_g, δ_g)`-point-wise indistinguishable. -/
def IsPrivacyFilter (Y : Type*) [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y]
    {k : ℕ} (C : (Fin k → ℝ) → Prop) (εg δg : ℝ) : Prop :=
  ∀ (A : Adversary Bool (Y ⊕ Unit) Y (· ≠ ·)) (b : Bool),
    IsPointwiseIndist (privacyFilterComp A C b) (privacyFilterComp A C (!b)) εg δg

/-- The **basic-composition filter** of Theorem 3.4 of Rogers–Roth–Ullman–Vadhan:
`COMP_{ε_g}(ε₁, …, ε_k) = HALT` iff `∑ᵢ εᵢ > ε_g`; here `basicFilter k εg e` means `CONT`. -/
def basicFilter (k : ℕ) (εg : ℝ) : (Fin k → ℝ) → Prop :=
  fun e ↦ ∑ j, e j ≤ εg

omit [MeasurableSpace H] in
/-- If the game runs in round `n`, it ran in every earlier round `m ≤ n`: the filter's answers
before round `m` only depend on the first `m` entries of the history. -/
lemma Runs.take {k : ℕ} {C : (Fin k → ℝ) → Prop} {ε : (n : ℕ) → (Fin n → H) → ℝ} {n m : ℕ}
    {h : Fin n → H} (hm : m ≤ n) (hh : Runs C ε h) : Runs C ε (Fin.take m hm h) := by
  intro i hi
  convert hh i (hi.trans hm) using 1
  ext j
  simp only [paddedEps]
  by_cases hj : (j : ℕ) ≤ i
  · rw [dite_eq_left ⟨hj, hj.trans hi⟩, dite_eq_left ⟨hj, (hj.trans hi).trans hm⟩]
    rfl
  · rw [dite_eq_right fun h' ↦ hj h'.1, dite_eq_right fun h' ↦ hj h'.1]

open scoped Classical in
/-- The parameter effectively used in round `n` of the game with filter `C` after the history
`h`: `ε n h` while the game runs, and `0` once the filter has answered `HALT`. -/
noncomputable def filteredEps {k : ℕ} (C : (Fin k → ℝ) → Prop)
    (ε : (n : ℕ) → (Fin n → H) → ℝ) (n : ℕ) (h : Fin n → H) : ℝ :=
  if Runs C ε h then ε n h else 0

omit [MeasurableSpace H] in
lemma filteredEps_of_runs {k : ℕ} {C : (Fin k → ℝ) → Prop} {ε : (n : ℕ) → (Fin n → H) → ℝ}
    {n : ℕ} {h : Fin n → H} (hh : Runs C ε h) : filteredEps C ε n h = ε n h := by
  simp [filteredEps, hh]

omit [MeasurableSpace H] in
lemma filteredEps_of_not_runs {k : ℕ} {C : (Fin k → ℝ) → Prop}
    {ε : (n : ℕ) → (Fin n → H) → ℝ} {n : ℕ} {h : Fin n → H} (hh : ¬ Runs C ε h) :
    filteredEps C ε n h = 0 := by
  simp [filteredEps, hh]

omit [MeasurableSpace H] in
/-- **The basic filter keeps the realized privacy loss within budget**: along every view `v` of
the game with the basic filter, the parameters of the rounds actually run sum to at most `ε_g`.
If some round runs, the rounds that run are those up to the last running round `m`, and the
filter's answer `CONT` before round `m` says precisely that their parameters sum to at most
`ε_g`. -/
theorem sum_filteredEps_basicFilter_le {k : ℕ} {εg : ℝ} (hεg : 0 ≤ εg)
    (ε : (n : ℕ) → (Fin n → H) → ℝ) (v : Fin k → H) :
    ∑ n, realizedEps (filteredEps (basicFilter k εg) ε) v n ≤ εg := by
  classical
  simp only [realizedEps]
  by_cases hex : ∃ n : Fin k, Runs (basicFilter k εg) ε (Fin.take n n.isLt.le v)
  · set s := Finset.univ.filter fun n : Fin k ↦
      Runs (basicFilter k εg) ε (Fin.take n n.isLt.le v) with hs
    have hne : s.Nonempty := by
      obtain ⟨n, hn⟩ := hex
      exact ⟨n, by simpa [hs] using hn⟩
    set m := s.max' hne
    have hm : Runs (basicFilter k εg) ε (Fin.take m m.isLt.le v) := by
      simpa [hs] using s.max'_mem hne
    have hiff (n : Fin k) :
        Runs (basicFilter k εg) ε (Fin.take n n.isLt.le v) ↔ (n : ℕ) ≤ m := by
      refine ⟨fun hn ↦ Fin.le_iff_val_le_val.1 (s.le_max' n (by simpa [hs] using hn)),
        fun hn ↦ ?_⟩
      exact Runs.take hn hm
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) (hm m le_rfl)
    simp only [paddedEps]
    by_cases hj : (j : ℕ) ≤ m
    · rw [filteredEps_of_runs ((hiff j).2 hj), dite_eq_left ⟨hj, hj⟩]
      rfl
    · rw [filteredEps_of_not_runs fun h ↦ hj ((hiff j).1 h), dite_eq_right fun h ↦ hj h.1]
  · simp only [not_exists] at hex
    rw [Finset.sum_eq_zero fun n _ ↦ filteredEps_of_not_runs (hex n)]
    exact hεg

/-- In each round of the game with filter `C`, the output distributions on neighbouring inputs
satisfy the pointwise bound with the effective parameter `filteredEps`: the adversary's
`ε`-bound while the game runs, and `e⁰ = 1` once it outputs `⊥`. -/
lemma filterRound_apply_singleton_le [Countable Y] [MeasurableSingletonClass Y] {k : ℕ}
    (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj) (C : (Fin k → ℝ) → Prop) {S S' : 𝒟} (hS : Adj S S')
    (n : ℕ) (x : Fin n → Y ⊕ Unit) (z : Y ⊕ Unit) :
    filterRound A C n (S, x) {z} ≤
      ENNReal.ofReal (exp (filteredEps C A.eps n x)) * filterRound A C n (S', x) {z} := by
  by_cases hx : Runs C A.eps x
  · simp only [filterRound, Kernel.piecewise_apply, Set.mem_prod, Set.mem_univ,
      Set.mem_ofPred_eq, hx, and_self, ite_true, filteredEps_of_runs hx]
    rw [Kernel.map_apply' _ measurable_inl _ (measurableSet_singleton z),
      Kernel.map_apply' _ measurable_inl _ (measurableSet_singleton z)]
    exact A.apply_le hS n x _
  · simp [filterRound, Kernel.piecewise_apply, hx, filteredEps_of_not_runs hx]

/-- **The game with the basic filter has privacy loss at most `ε_g` on every view** (proof of
Theorem 3.4 of Rogers–Roth–Ullman–Vadhan): for neighbouring `S, S'`, `ε_g ≥ 0` and every view
`v`, `P[V_F(S) = v] ≤ e^{ε_g} P[V_F(S') = v]`. -/
theorem privacyFilterComp_basicFilter_apply_singleton_le [Countable Y]
    [MeasurableSingletonClass Y] {k : ℕ} (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj) {εg : ℝ}
    (hεg : 0 ≤ εg) {S S' : 𝒟} (hS : Adj S S') (v : Fin k → Y ⊕ Unit) :
    privacyFilterComp A (basicFilter k εg) S {v} ≤
      ENNReal.ofReal (exp εg) * privacyFilterComp A (basicFilter k εg) S' {v} :=
  (adaptiveCompose_apply_singleton_le _ _ (filterRound_apply_singleton_le A _ hS) k v).trans <|
    mul_le_mul_left (ENNReal.ofReal_le_ofReal <| exp_le_exp.2 <|
      sum_filteredEps_basicFilter_le hεg A.eps v) _

/-- **The game with the basic filter is `ε_g`-DP**, a strengthening taken from the proof of
Theorem 3.4 of Rogers–Roth–Ullman–Vadhan (not the statement of that theorem, which is
`isPrivacyFilter_basicFilter`): for every adversary with pure-DP mechanisms, whose parameters
are chosen adaptively, the view of the game with the basic filter `HALT iff ∑ εᵢ > ε_g` is
`ε_g`-DP for `ε_g ≥ 0`, for an arbitrary neighbouring relation. -/
theorem isEpsDP_privacyFilterComp_basicFilter [Countable Y] [MeasurableSingletonClass Y]
    {k : ℕ} (A : Adversary 𝒟 (Y ⊕ Unit) Y Adj) {εg : ℝ} (hεg : 0 ≤ εg) :
    IsEpsDP (privacyFilterComp A (basicFilter k εg)) Adj εg := by
  refine isEpsDP_iff_forall_singleton.2 fun S S' hS v ↦ ?_
  simpa using DP.measureReal_le_of_measure_le le_rfl (by
    simpa using privacyFilterComp_basicFilter_apply_singleton_le A hεg hS v)

/-- **Theorem 3.4 of Rogers–Roth–Ullman–Vadhan, filter part**: for all `ε_g, δ_g ≥ 0`, the
basic-composition filter `COMP_{ε_g,δ_g}(ε₁, 0, …, ε_k, 0) = HALT iff ∑ᵢ εᵢ > ε_g` is a valid
privacy filter (for adversaries with pure-DP mechanisms with outputs in a countable alphabet
`Y`, and every number of rounds `k`). In fact the views are `(ε_g, 0)`-point-wise
indistinguishable. -/
theorem isPrivacyFilter_basicFilter [Countable Y] [MeasurableSingletonClass Y] (k : ℕ)
    {εg δg : ℝ} (hεg : 0 ≤ εg) (hδg : 0 ≤ δg) :
    IsPrivacyFilter Y (basicFilter k εg) εg δg := by
  intro A b
  have hb : b ≠ !b := by cases b <;> decide
  refine ⟨(measureReal_mono (s₂ := ∅) (fun v hv ↦ ?_) (by simp)).trans (by simpa using hδg),
    (measureReal_mono (s₂ := ∅) (fun v hv ↦ ?_) (by simp)).trans (by simpa using hδg)⟩
  · exact ((privacyFilterComp_basicFilter_apply_singleton_le A hεg hb v).not_gt hv).elim
  · exact ((privacyFilterComp_basicFilter_apply_singleton_le A hεg hb.symm v).not_gt hv).elim

end PrivacyFilter

end InformationTheory
