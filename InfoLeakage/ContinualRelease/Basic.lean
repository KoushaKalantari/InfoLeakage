/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.DP.Laplace
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Log

/-!
# Differential privacy under continual observation: counting a binary stream

We formalize the privacy of the continual counting mechanisms of T.-H. H. Chan, E. Shi and
D. Song, *Private and continual release of statistics*, ACM Trans. Inf. Syst. Secur. 14(3),
Article 26, 2011 (doi:10.1145/2043621.2043626; ICALP 2010; IACR ePrint 2010/076; there is no
arXiv version). Result numbers refer to the journal version. The tree-based counter was found
independently by C. Dwork, M. Naor, T. Pitassi and G. N. Rothblum, *Differential privacy under
continual observation*, STOC 2010, who also introduced the event-level adjacency used here
(Chan–Shi–Song, Remark 2.7).

A mechanism receives a stream `σ ∈ {0, 1}^T` and must output, at every time `t`, an estimate of
the count `c(t) = ∑_{i ≤ t} σ(i)`. Two streams are adjacent if they differ at exactly one time
(event-level privacy). Following the paper's "p-sum view" (Section 3.2), each mechanism releases
noisy partial sums `Σ I + Lap(b)` with i.i.d. Laplace noise, and the estimates are computed from
them; privacy of the estimates is then post-processing (`IsEpsDeltaDP.map`). The noisy p-sums are
an instance of the vector Laplace mechanism `laplaceMechanismPi` on `ℝ^ι`: outputs live in a
general measurable space (`Fin T → ℝ` with its Borel structure), not in a finite alphabet.

## Main definitions

* `ContinualRelease.BinStream T`: binary streams of length `T`; `ContinualRelease.count`
  (Definition 2.1); `ContinualRelease.Adjacent` (event-level adjacency, Definition 2.6);
  `ContinualRelease.pSum` (Definition 3.2).
* `ContinualRelease.pSumMechanism I b`: release the p-sums `Σ I_k`, `k ∈ ι`, with i.i.d. `Lap(b)`
  noise.
* `ContinualRelease.simpleCountingI`, `ContinualRelease.simpleCountingII`: Simple Counting
  Mechanisms I and II (Section 3.1).
* `ContinualRelease.twoLevelMechanism`: the Two-Level Counting Mechanism (Algorithm 1).
* `ContinualRelease.lowbit n = 2 ^ ν₂(n)`, `ContinualRelease.binInterval`: the p-sum created at
  each time by the Binary Mechanism; `ContinualRelease.binaryPSums`: all of them, noised;
  `ContinualRelease.binEstimate`: the estimate `B(t)` (Algorithm 2, Equation (4));
  `ContinualRelease.binaryMechanism`: the Binary Mechanism (Algorithm 2).

## Main statements (paper result → Lean name)

* Observation 1 (privacy part; the paper states it informally): if every item lies in at most
  `x` p-sums, `Lap(x / ε)` noise gives `ε`-DP and `Lap(1 / ε)` noise gives `x ε`-DP:
  `isEpsDP_pSumMechanism_of_card_le`, `isEpsDP_pSumMechanism_one_div`; general scale
  `isEpsDP_pSumMechanism`.
* Section 3.1, Simple Counting Mechanism I: `T ε`-DP with `Lap(1 / ε)` noise
  (`isEpsDP_simpleCountingI_one_div`; the paper says `O(T ε)`), `ε`-DP with `Lap(T / ε)` noise
  (`isEpsDP_simpleCountingI`), and per-step error `b ln (1 / δ)` with probability `≥ 1 - δ`
  (`simpleCountingI_real_le_abs_sub`; the paper says `O(1 / ε)`, resp. `O(T / ε)`).
* Theorem 3.1 (privacy part), Simple Counting Mechanism II: `isEpsDP_simpleCountingII`.
* Theorem 3.3 (privacy part), Two-Level Mechanism with block size `B ≥ 1` (the paper's setting;
  the statement also holds for `B = 0`, where there are no blocks and the mechanism behaves as
  Simple Counting Mechanism II): `isEpsDP_twoLevelMechanism`. Exactness of its estimate on exact
  p-sums, `D(t) = c(t)`: `twoLevelEstimate_pSum`.
* Theorem 3.5 (privacy of the Binary Mechanism), with the noise corrected to
  `Lap((⌊log₂ T⌋ + 1) / ε)`: `isEpsDP_binaryMechanism` (estimates `B(1), …, B(T)`) and
  `isEpsDP_binaryPSums` (all noisy p-sums). The key count, "each item is in at most
  `⌊log₂ T⌋ + 1` p-sums": `card_binInterval_le`. This noise is optimal for every `T`, so the
  noise of Algorithm 2 is too small: `not_isEpsDP_binaryMechanism`, and at the powers of two
  `not_isEpsDP_binaryMechanism_two_pow` (see the notes below).
* Exactness of the Binary Mechanism's estimate (stated in Section 3.4, not numbered): on exact
  p-sums, `B(t) = c(t)`: `binEstimate_pSum`.

## Implementation notes

* Everything is `T`-bounded (Definition 2.3): streams `Fin T → Bool`, outputs `Fin T → ℝ`. The
  unbounded statements over `ℝ^ℕ` (Simple Counting Mechanism II is unbounded in the paper) and
  Section 4 (unbounded mechanisms) are not formalized.
* Lean times are `0`-indexed: `σ s` is the item at paper time `s + 1`; the p-sum created at Lean
  time `t` is the paper's `Σ[n - 2^i + 1, n]` with `n = t + 1`, `2^i = lowbit n`.
* The stateful Algorithm 2 is modelled through its p-sum view: release the `T` noisy p-sums (one
  created per time step, with fresh noise) and output `B(n)` = the sum of the noisy p-sums along
  the chain `n, n - lowbit n, …`, i.e. the noisy p-sum of size `2^j` created at time
  `2^j ⌊n / 2^j⌋`, for each `j` with `Bin_j(n) = 1`; these are exactly the `α̂_j` that
  Equation (4) reads at time `n`. This equivalence with the pseudocode is not proved in Lean.
* Not formalized: Lemma 2.8 and Corollary 2.9 (sums of Laplace variables), hence the utility parts
  of Theorems 3.1, 3.3 and 3.6, and Corollary 3.4.

## Notes on the paper

* **Theorem 3.5 is false as stated; the error is a constant-factor off-by-one** (journal
  version, Section 3.4: Algorithm 2 on p. 26:10 sets `ε' ← ε / log T`, and the privacy paragraph
  on p. 26:12 says "the item `σ(t)` can be in at most `log T` p-sums ... at most 1 p-sum of size
  `2^j`, where `j ≤ log T`"). The sizes `2^j` with `j ≤ log₂ T` give `⌊log₂ T⌋ + 1` p-sums, not
  `log T`, so with `log = log₂` Algorithm 2 is `((⌊log₂ T⌋ + 1) / log₂ T) ε`-DP, at most a factor
  `2` off for `T ≥ 2` (`isEpsDP_binaryMechanism` with `ε` rescaled), and no better:
  `not_isEpsDP_binaryMechanism` shows that for every `T ≥ 1` no noise scale below
  `(⌊log₂ T⌋ + 1) / ε` gives `ε`-DP. Hence `log T / ε` fails for every `T ≥ 2`, with
  `log = log₂` or `log = ln`; restricting to powers of two does not help, since for `T = 2^k`
  the threshold is `(k + 1) / ε > k / ε` (`not_isEpsDP_binaryMechanism_two_pow`). (For `T = 1`,
  `log T = 0` and `ε'` is undefined.) The paper's own Section 4 shows the slack: Theorem 4.1
  (p. 26:13) gives `(∑_{i ≤ K} 1 / a_i) ε`-DP with `K = log₂ T + O(1)`, and Remark 4.3 calls the
  choice `a_i = log T` the time-bounded Binary Mechanism, for which this is
  `(log₂ T + O(1)) ε / log T`, not `ε`. Dwork–Naor–Pitassi–Rothblum's counter uses the noise
  scale `ξ = (1 + log T) / ε`. Theorem 3.5 is true with `ε' = ε / (⌊log₂ T⌋ + 1)`
  (`isEpsDP_binaryMechanism`), which changes only constants in Theorem 3.6. We did not check the
  ePrint version.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace InformationTheory

namespace ContinualRelease

variable {T : ℕ}

/-! ### Streams, counts and event-level adjacency -/

/-- A binary stream of length `T` (Chan–Shi–Song, Section 2.1, the length-`T` prefix
`σ_T ∈ {0, 1}^T`). Times are `0`-indexed: `σ s` is the item that arrives at time `s + 1` of the
paper. -/
abbrev BinStream (T : ℕ) : Type := Fin T → Bool

/-- The item `σ(s) ∈ {0, 1}` as a real number. -/
def item (σ : BinStream T) (s : Fin T) : ℝ := (σ s).toNat

/-- **Chan–Shi–Song, Definition 2.1** (continual counting query): the number `c_σ(t)` of `1`s
among the items arriving up to (Lean) time `t`, i.e. up to time `t + 1` of the paper. -/
noncomputable def count (σ : BinStream T) (t : Fin T) : ℝ := ∑ s ∈ Iic t, item σ s

/-- **Chan–Shi–Song, Definition 2.6** (event-level adjacency; Dwork–Naor–Pitassi–Rothblum's
event-level neighbouring streams): two streams are adjacent if they differ at exactly one time. -/
def Adjacent (σ σ' : BinStream T) : Prop :=
  ∃ t, σ t ≠ σ' t ∧ ∀ s, s ≠ t → σ s = σ' s

/-- **Chan–Shi–Song, Definition 3.2** (p-sum): the partial sum `Σ I = ∑_{s ∈ I} σ(s)` of the
items in a set of times `I` (the paper's p-sums are sums over intervals `[i, j]` of consecutive
times; all the mechanisms below use intervals). -/
noncomputable def pSum (σ : BinStream T) (I : Finset (Fin T)) : ℝ := ∑ s ∈ I, item σ s

/-! ### The p-sum framework (Observation 1, privacy part) -/

variable {ι : Type*} [Fintype ι]

/-- The mechanism that releases the noisy p-sums `Σ I_k + γ_k`, `k ∈ ι`, with i.i.d. noise
`γ_k ∼ Lap(b)` (the "p-sum view" of the counting mechanisms of Chan–Shi–Song, Section 3.2). It is
the Laplace mechanism (`laplaceMechanismPi`) applied to the vector of p-sums. -/
noncomputable def pSumMechanism (I : ι → Finset (Fin T)) (b : ℝ) :
    Kernel (BinStream T) (ι → ℝ) :=
  laplaceMechanismPi (fun σ k ↦ pSum σ (I k)) b

lemma isMarkovKernel_pSumMechanism (I : ι → Finset (Fin T)) {b : ℝ} (hb : 0 < b) :
    IsMarkovKernel (pSumMechanism I b) :=
  isMarkovKernel_laplaceMechanismPi (measurable_of_finite _) hb

lemma abs_item_sub_item {σ σ' : BinStream T} {t : Fin T} (h : σ t ≠ σ' t) :
    |item σ t - item σ' t| = 1 := by
  revert h
  unfold item
  cases σ t <;> cases σ' t <;> simp

/-- Flipping one item changes the vector of p-sums by exactly the number of p-sums containing it
in `ℓ₁`; in particular by at most `x` if every item lies in at most `x` of the `I_k`. -/
lemma sum_abs_pSum_sub_le (I : ι → Finset (Fin T)) {x : ℝ}
    (hI : ∀ s, (#{k | s ∈ I k} : ℝ) ≤ x) {σ σ' : BinStream T} (h : Adjacent σ σ') :
    ∑ k, |pSum σ (I k) - pSum σ' (I k)| ≤ x := by
  obtain ⟨t, hne, heq⟩ := h
  have key (k : ι) : |pSum σ (I k) - pSum σ' (I k)| = if t ∈ I k then 1 else 0 := by
    have hs : ∀ s ∈ I k, item σ s - item σ' s = if s = t then item σ t - item σ' t else 0 := by
      intro s _
      split_ifs with hst
      · rw [hst]
      · simp [item, heq s hst]
    rw [pSum, pSum, ← sum_sub_distrib, sum_congr rfl hs, sum_ite_eq']
    split_ifs
    · exact abs_item_sub_item hne
    · simp
  simp_rw [key]
  rw [sum_boole]
  exact hI t

/-- **Chan–Shi–Song, Observation 1** (privacy part, made precise): if every item lies in at most
`x` of the p-sums `I_k`, then releasing all of them with i.i.d. `Lap(b)` noise is
`ε`-differentially private for event-level adjacency as soon as `x ≤ ε b`. -/
theorem isEpsDP_pSumMechanism (I : ι → Finset (Fin T)) {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hI : ∀ s, (#{k | s ∈ I k} : ℝ) ≤ ε * b) : IsEpsDP (pSumMechanism I b) Adjacent ε := by
  have := isEpsDeltaDP_laplaceMechanismPi (Adj := Adjacent) (measurable_of_finite _) hε
    (mul_pos hε hb) fun σ σ' h ↦ sum_abs_pSum_sub_le I hI h
  rwa [mul_div_cancel_left₀ _ hε.ne'] at this

/-- **Chan–Shi–Song, Observation 1** (privacy part): if every item lies in at most `x ≥ 1` of the
p-sums `I_k`, then releasing all of them with i.i.d. `Lap(x / ε)` noise is `ε`-differentially
private for event-level adjacency. -/
theorem isEpsDP_pSumMechanism_of_card_le (I : ι → Finset (Fin T)) {ε : ℝ} (hε : 0 < ε) {x : ℕ}
    (hx : 0 < x) (hI : ∀ s, #{k | s ∈ I k} ≤ x) :
    IsEpsDP (pSumMechanism I (x / ε)) Adjacent ε :=
  isEpsDP_pSumMechanism I hε (by positivity) fun s ↦ by
    rw [mul_div_cancel₀ _ hε.ne']
    exact_mod_cast hI s

/-- **Chan–Shi–Song, Observation 1** (privacy part, second form): if every item lies in at most
`x` of the p-sums `I_k`, then releasing all of them with i.i.d. `Lap(1 / ε)` noise is
`x ε`-differentially private for event-level adjacency. -/
theorem isEpsDP_pSumMechanism_one_div (I : ι → Finset (Fin T)) {ε : ℝ} (hε : 0 < ε) {x : ℕ}
    (hx : 0 < x) (hI : ∀ s, #{k | s ∈ I k} ≤ x) :
    IsEpsDP (pSumMechanism I (1 / ε)) Adjacent (x * ε) := by
  convert isEpsDP_pSumMechanism_of_card_le I (ε := x * ε) (by positivity) hx hI using 2
  field_simp

/-! ### The simple counting mechanisms -/

lemma not_adjacent_of_eq_zero (σ σ' : BinStream 0) : ¬Adjacent σ σ' := by
  rintro ⟨t, -⟩
  exact t.elim0

/-- **Chan–Shi–Song, Simple Counting Mechanism I** (Section 3.1), `T`-bounded: at every time `t`
it releases the noisy count `α_t = c(t) + γ_t`, with i.i.d. `γ_t ∼ Lap(b)`. In the p-sum view,
`α_t` is the noisy p-sum `Σ[1, t]` (`simpleCountingI_apply`). -/
noncomputable def simpleCountingI (T : ℕ) (b : ℝ) : Kernel (BinStream T) (Fin T → ℝ) :=
  pSumMechanism (fun t : Fin T ↦ Iic t) b

/-- The output law of Simple Counting Mechanism I: independent `Lap(c(t), b)` coordinates. -/
lemma simpleCountingI_apply {b : ℝ} (hb : 0 < b) (σ : BinStream T) :
    simpleCountingI T b σ = Measure.pi fun t ↦ laplaceMeasure (count σ t) b :=
  laplaceMechanismPi_apply (measurable_of_finite _) hb σ

lemma card_mem_Iic_le (s : Fin T) : #{t : Fin T | s ∈ Iic t} ≤ T := by
  simpa using card_filter_le (univ : Finset (Fin T)) fun t ↦ s ∈ Iic t

/-- **Chan–Shi–Song, Section 3.1**, Simple Counting Mechanism I with noise `Lap(1 / ε)` is
`T ε`-differentially private (the paper states `O(T ε)`). -/
theorem isEpsDP_simpleCountingI_one_div {ε : ℝ} (hε : 0 < ε) :
    IsEpsDP (simpleCountingI T (1 / ε)) Adjacent (T * ε) := by
  rcases T.eq_zero_or_pos with rfl | hT
  · exact fun σ σ' h ↦ absurd h (not_adjacent_of_eq_zero σ σ')
  · exact isEpsDP_pSumMechanism_one_div _ hε hT card_mem_Iic_le

/-- **Chan–Shi–Song, Section 3.1**, Simple Counting Mechanism I with `ε' = ε / T`, i.e. noise
`Lap(T / ε)`, is `ε`-differentially private. -/
theorem isEpsDP_simpleCountingI {ε : ℝ} (hε : 0 < ε) :
    IsEpsDP (simpleCountingI T (T / ε)) Adjacent ε := by
  rcases T.eq_zero_or_pos with rfl | hT
  · exact fun σ σ' h ↦ absurd h (not_adjacent_of_eq_zero σ σ')
  · exact isEpsDP_pSumMechanism_of_card_le _ hε hT card_mem_Iic_le

/-- **Chan–Shi–Song, Section 3.1** (error of Simple Counting Mechanism I, made precise): at every
time `t`, the released `α_t` satisfies `P[|α_t - c(t)| ≥ b ln (1 / δ)] ≤ δ` for `δ ∈ (0, 1]`. With
`b = T / ε` (the `ε`-DP choice) this is the paper's informal "error `O(T / ε)`", and with
`b = 1 / ε` its "error `O(1 / ε)`", each with probability at least `1 - δ`. -/
theorem simpleCountingI_real_le_abs_sub {b : ℝ} (hb : 0 < b) (σ : BinStream T) (t : Fin T)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (simpleCountingI T b σ).real {y | Real.log (1 / δ) * b ≤ |y t - count σ t|} ≤ δ := by
  have := fun t ↦ isProbabilityMeasure_laplaceMeasure (count σ t) hb
  rw [simpleCountingI_apply hb, ← Set.preimage_ofPred_eq (p := fun z ↦ Real.log (1 / δ) * b ≤
      |z - count σ t|) (f := fun y : Fin T → ℝ ↦ y t),
    (measurePreserving_eval _ t).measureReal_preimage
      (measurableSet_le measurable_const (by fun_prop)).nullMeasurableSet,
    laplaceMeasure_real_le_abs_sub _ hb (Real.log_nonneg (one_le_one_div hδ₀ hδ₁)),
    Real.log_div one_ne_zero hδ₀.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hδ₀]

/-- The noisy items `α_t = σ(t) + γ_t`, with i.i.d. `γ_t ∼ Lap(b)`: the "sanitized" stream of
Simple Counting Mechanism II (the noisy p-sums `Σ[t, t]`). -/
noncomputable def noisyItems (T : ℕ) (b : ℝ) : Kernel (BinStream T) (Fin T → ℝ) :=
  pSumMechanism (fun t : Fin T ↦ {t}) b

/-- The prefix sums `t ↦ ∑_{s ≤ t} y_s` of a vector `y`. -/
def prefixSum (y : Fin T → ℝ) (t : Fin T) : ℝ := ∑ s ∈ Iic t, y s

@[fun_prop]
lemma measurable_prefixSum : Measurable (prefixSum (T := T)) := by
  unfold prefixSum
  fun_prop

/-- The prefix sums of the exact items are the counts. -/
lemma prefixSum_item (σ : BinStream T) : prefixSum (item σ) = count σ := rfl

/-- **Chan–Shi–Song, Simple Counting Mechanism II** (Section 3.1), `T`-bounded: it adds i.i.d.
`Lap(b)` noise to every item, `α_t = σ(t) + γ_t`, and outputs `M(σ)(t) = ∑_{i ≤ t} α_i`. -/
noncomputable def simpleCountingII (T : ℕ) (b : ℝ) : Kernel (BinStream T) (Fin T → ℝ) :=
  (noisyItems T b).map prefixSum

/-- **Chan–Shi–Song, Theorem 3.1** (privacy part), for the `T`-bounded mechanism: Simple
Counting Mechanism II with noise `Lap(1 / ε)` is `ε`-differentially private. (The paper's
mechanism is unbounded, with outputs in `ℝ^ℕ`; here it is run on streams of any fixed length
`T`. The utility part of Theorem 3.1 is not formalized.) -/
theorem isEpsDP_simpleCountingII {ε : ℝ} (hε : 0 < ε) :
    IsEpsDP (simpleCountingII T (1 / ε)) Adjacent ε := by
  have : IsMarkovKernel (noisyItems T (1 / ε)) :=
    isMarkovKernel_pSumMechanism (fun t : Fin T ↦ {t}) (one_div_pos.2 hε)
  have h : IsEpsDP (noisyItems T (1 / ε)) Adjacent ε := by
    have h := isEpsDP_pSumMechanism_one_div (fun t : Fin T ↦ {t}) hε one_pos
      fun s ↦ card_le_one.2 fun a ha b hb ↦ by
        simp only [mem_filter, mem_singleton] at ha hb
        rw [← ha.2, hb.2]
    rwa [Nat.cast_one, one_mul] at h
  exact h.map measurable_prefixSum

/-! ### Sums over times as sums over naturals -/

/-- Extend a vector indexed by `Fin T` by zero to `ℕ`. -/
def extendZero (y : Fin T → ℝ) (n : ℕ) : ℝ := if h : n < T then y ⟨n, h⟩ else 0

lemma extendZero_of_lt {y : Fin T → ℝ} {n : ℕ} (h : n < T) : extendZero y n = y ⟨n, h⟩ := by
  simp [extendZero, h]

/-- Sums over `J : Finset (Fin T)` as sums over the corresponding naturals. -/
private lemma sum_eq_sum_map_extendZero (J : Finset (Fin T)) (y : Fin T → ℝ) :
    ∑ s ∈ J, y s = ∑ n ∈ J.map Fin.valEmbedding, extendZero y n := by
  rw [sum_map]
  exact sum_congr rfl fun s _ ↦ (extendZero_of_lt s.isLt).symm

/-- The count as a sum over the naturals `0, …, t`. -/
private lemma count_eq_sum_range (σ : BinStream T) (t : Fin T) :
    count σ t = ∑ n ∈ range (t + 1), extendZero (item σ) n := by
  rw [count, sum_eq_sum_map_extendZero, Fin.map_valEmbedding_Iic, Nat.range_succ_eq_Iic]

/-! ### The Two-Level Counting Mechanism -/

/-- The p-sums of the Two-Level Counting Mechanism with block size `B` (Chan–Shi–Song,
Algorithm 1): the single items `α_t = Σ[t, t]` (`Sum.inl t`) and the blocks
`β_q = Σ[(q - 1) B + 1, q B]` for `q = 1, …, ⌊T / B⌋` (`Sum.inr q`, `0`-indexed: the Lean times
`s` with `q B ≤ s < (q + 1) B`). -/
def twoLevelInterval (B : ℕ) : Fin T ⊕ Fin (T / B) → Finset (Fin T)
  | .inl t => {t}
  | .inr q => {s | (q : ℕ) * B ≤ s ∧ (s : ℕ) < (q + 1) * B}

/-- In the Two-Level Mechanism each item lies in at most two p-sums: its own `α_t` and at most
one block `β_q` (Chan–Shi–Song, proof of Theorem 3.3). -/
lemma card_twoLevelInterval_le (B : ℕ) (s : Fin T) : #{k | s ∈ twoLevelInterval B k} ≤ 2 := by
  rw [card_filter, Fintype.sum_sum_type]
  have h₁ : ∑ t : Fin T, (if s ∈ twoLevelInterval B (.inl t) then 1 else 0) = 1 := by
    simp [twoLevelInterval]
  have h₂ : ∑ q : Fin (T / B), (if s ∈ twoLevelInterval B (.inr q) then 1 else 0) ≤ 1 := by
    rw [← card_filter]
    refine card_le_one.2 fun q₁ hq₁ q₂ hq₂ ↦ ?_
    simp only [mem_filter, mem_univ, true_and, twoLevelInterval] at hq₁ hq₂
    exact Fin.ext ((Nat.div_eq_of_lt_le hq₁.1 hq₁.2).symm.trans (Nat.div_eq_of_lt_le hq₂.1 hq₂.2))
  omega

/-- The estimate of the Two-Level Mechanism (Chan–Shi–Song, Algorithm 1, Equation (1)): at paper
time `n = t + 1 = q B + r` with `0 ≤ r < B`, `D(n) = ∑_{i ≤ q} β_i + ∑_{i = q B + 1}^{n} α_i`. -/
noncomputable def twoLevelEstimate (B : ℕ) (y : Fin T ⊕ Fin (T / B) → ℝ) (t : Fin T) : ℝ :=
  ∑ q ∈ {q : Fin (T / B) | (q : ℕ) < (t + 1) / B}, y (.inr q) +
    ∑ s ∈ {s : Fin T | (t + 1) / B * B ≤ s ∧ s ≤ t}, y (.inl s)

@[fun_prop]
lemma measurable_twoLevelEstimate (B : ℕ) : Measurable (twoLevelEstimate (T := T) B) := by
  unfold twoLevelEstimate
  fun_prop

/-- **Correctness of the Two-Level Mechanism's estimates**: applied to the exact p-sums, the
estimate is the exact count, `D(t) = c(t)` (Chan–Shi–Song, Algorithm 1, Equation (1)). Hence the
error of `D(t)` is the sum of the noises of the p-sums that it adds up. -/
theorem twoLevelEstimate_pSum (B : ℕ) (σ : BinStream T) (t : Fin T) :
    twoLevelEstimate B (fun k ↦ pSum σ (twoLevelInterval B k)) t = count σ t := by
  set x := extendZero (item σ)
  set Q := ((t : ℕ) + 1) / B with hQ_def
  have hQ : Q ≤ T / B := Nat.div_le_div_right t.isLt
  have hQB : Q * B ≤ t + 1 := Nat.div_mul_le_self _ _
  have hblock (q : Fin (T / B)) : pSum σ (twoLevelInterval B (.inr q)) =
      ∑ n ∈ Ico (q * B) ((q + 1) * B), x n := by
    have hqT : ((q : ℕ) + 1) * B ≤ T :=
      (Nat.mul_le_mul_right B (Nat.succ_le_of_lt q.isLt)).trans (Nat.div_mul_le_self T B)
    rw [pSum, sum_eq_sum_map_extendZero]
    congr 1
    ext n
    simp only [twoLevelInterval, mem_map, mem_filter, mem_univ, true_and,
      Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨s, h, rfl⟩
      exact h
    · intro h
      exact ⟨⟨n, by omega⟩, h, rfl⟩
  have hblocks (Q' : ℕ) : ∑ q ∈ range Q', ∑ n ∈ Ico (q * B) ((q + 1) * B), x n =
      ∑ n ∈ range (Q' * B), x n := by
    induction Q' with
    | zero => simp
    | succ Q' ih =>
      rw [sum_range_succ, ih, sum_range_add_sum_Ico _ (Nat.mul_le_mul_right B Q'.le_succ)]
  have hmapQ : ({q : Fin (T / B) | (q : ℕ) < Q} : Finset _).map Fin.valEmbedding = range Q := by
    ext m
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  have hqsum : ∑ q ∈ {q : Fin (T / B) | (q : ℕ) < Q}, pSum σ (twoLevelInterval B (.inr q)) =
      ∑ n ∈ range (Q * B), x n := by
    rw [← hblocks Q, ← hmapQ, sum_map]
    exact sum_congr rfl fun q _ ↦ hblock q
  have htail : ∑ s ∈ {s : Fin T | Q * B ≤ s ∧ s ≤ t}, pSum σ (twoLevelInterval B (.inl s)) =
      ∑ n ∈ Ico (Q * B) (t + 1), x n := by
    simp only [twoLevelInterval, pSum, sum_singleton]
    rw [sum_eq_sum_map_extendZero]
    congr 1
    ext n
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨s, ⟨h₁, h₂⟩, rfl⟩
      exact ⟨h₁, Nat.lt_succ_of_le h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨n, by omega⟩, ⟨h₁, Nat.le_of_lt_succ h₂⟩, rfl⟩
  simp only [twoLevelEstimate]
  rw [hqsum, htail, sum_range_add_sum_Ico _ hQB, count_eq_sum_range]

/-- **The Two-Level Counting Mechanism** `D` with block size `B` (Chan–Shi–Song, Algorithm 1),
`T`-bounded: release the noisy items `α_t` and the noisy blocks `β_q`, each with fresh `Lap(b)`
noise, and output `D(t)` (`twoLevelEstimate`) at every time `t`. Algorithm 1 uses
`b = 1 / ε`. -/
noncomputable def twoLevelMechanism (T B : ℕ) (b : ℝ) : Kernel (BinStream T) (Fin T → ℝ) :=
  (pSumMechanism (twoLevelInterval B) b).map (twoLevelEstimate B)

/-- **Chan–Shi–Song, Theorem 3.3** (privacy part): for block size `B ≥ 1` (the paper's setting),
the Two-Level Counting Mechanism with noise `Lap(1 / ε)` is `2ε`-differentially private
(`T`-bounded). The statement also holds for `B = 0`, where `T / 0 = 0` leaves no blocks and the
mechanism behaves as Simple Counting Mechanism II. The utility part of Theorem 3.3 is not
formalized. -/
theorem isEpsDP_twoLevelMechanism (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsEpsDP (twoLevelMechanism T B (1 / ε)) Adjacent (2 * ε) := by
  have := isMarkovKernel_pSumMechanism (twoLevelInterval (T := T) B) (one_div_pos.2 hε)
  have h := isEpsDP_pSumMechanism_one_div (twoLevelInterval (T := T) B) hε two_pos
    (card_twoLevelInterval_le B)
  push_cast at h
  exact h.map (measurable_twoLevelEstimate B)

/-! ### The Binary Mechanism -/

/-- `lowbit n = 2 ^ ν₂(n)`, the largest power of two dividing `n ≠ 0` (and `lowbit 0 = 1`). At
time `n` the Binary Mechanism creates a p-sum of `2^i = lowbit n` items, where
`i = min {j | Bin_j(n) ≠ 0}` (Chan–Shi–Song, Algorithm 2). -/
def lowbit (n : ℕ) : ℕ := 2 ^ padicValNat 2 n

lemma lowbit_dvd (n : ℕ) : lowbit n ∣ n := by
  rw [lowbit, Nat.padicValNat_def]
  exact pow_multiplicity_dvd 2 n

lemma lowbit_pos (n : ℕ) : 0 < lowbit n := by
  unfold lowbit
  positivity

lemma lowbit_le {n : ℕ} (hn : 0 < n) : lowbit n ≤ n := Nat.le_of_dvd hn (lowbit_dvd n)

lemma lowbit_two_pow (j : ℕ) : lowbit (2 ^ j) = 2 ^ j := by
  rw [lowbit, Nat.padicValNat_def, multiplicity_eq_of_dvd_of_not_dvd (k := j) dvd_rfl
    fun h ↦ by simpa using Nat.pow_dvd_pow_iff_le_right one_lt_two |>.1 h]

/-- The (Lean) times of the items of the p-sum that the Binary Mechanism creates at Lean time
`t`, i.e. at paper time `n = t + 1`: the `lowbit n` most recent items, the paper's
`Σ[n - 2^i + 1, n]` with `2^i = lowbit n` (Chan–Shi–Song, Algorithm 2, Equation (2)). -/
def binInterval (t : Fin T) : Finset (Fin T) :=
  {s | (t : ℕ) + 1 - lowbit (t + 1) ≤ s ∧ s ≤ t}

lemma mem_binInterval {s t : Fin T} :
    s ∈ binInterval t ↔ (t : ℕ) + 1 - lowbit (t + 1) ≤ s ∧ s ≤ t := by
  simp [binInterval]

/-- Two multiples of `L` in an interval `(s, s + L]` are equal. -/
private lemma eq_of_dvd_of_mem_Ioc {L m₁ m₂ s : ℕ} (h₁ : L ∣ m₁) (h₂ : L ∣ m₂) (hs₁ : s < m₁)
    (hm₁ : m₁ ≤ s + L) (hs₂ : s < m₂) (hm₂ : m₂ ≤ s + L) : m₁ = m₂ := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨c, rfl⟩ := h₂
  have hac : a < c + 1 := lt_of_mul_lt_mul_left (a := L) (by rw [mul_add_one]; omega)
    (Nat.zero_le L)
  have hca : c < a + 1 := lt_of_mul_lt_mul_left (a := L) (by rw [mul_add_one]; omega)
    (Nat.zero_le L)
  rw [show a = c by omega]

/-- **Each item enters at most `⌊log₂ T⌋ + 1` p-sums of the Binary Mechanism** (Chan–Shi–Song,
Section 3.4, proof of Theorem 3.5): at most one of size `2^j` for each `j ≤ ⌊log₂ T⌋`. -/
theorem card_binInterval_le (s : Fin T) : #{t | s ∈ binInterval t} ≤ Nat.log 2 T + 1 := by
  calc #{t | s ∈ binInterval t} ≤ #(range (Nat.log 2 T + 1)) := by
        refine card_le_card_of_injOn (fun t : Fin T ↦ padicValNat 2 (t + 1)) (fun t _ ↦ ?_)
          fun t₁ h₁ t₂ h₂ h ↦ ?_
        · have : 2 ^ padicValNat 2 (t + 1) ≤ T := (lowbit_le t.val.succ_pos).trans t.isLt
          simpa [Nat.lt_succ_iff] using Nat.le_log_of_pow_le one_lt_two this
        · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_binInterval] at h₁ h₂
          have hl : lowbit (t₁ + 1) = lowbit (t₂ + 1) := congrArg (2 ^ ·) h
          have h₁' := lowbit_le t₁.val.succ_pos
          have h₂' := lowbit_le t₂.val.succ_pos
          refine Fin.ext (Nat.succ_injective (eq_of_dvd_of_mem_Ioc (L := lowbit (t₂ + 1))
            (hl ▸ lowbit_dvd _) (lowbit_dvd _) (s := s) ?_ ?_ ?_ ?_)) <;> omega
    _ = Nat.log 2 T + 1 := card_range _

/-- The released vector of the Binary Mechanism in the p-sum view (Chan–Shi–Song, Section 3.4):
the noisy p-sum `Σ̂[n - lowbit n + 1, n] = Σ[n - lowbit n + 1, n] + γ_n` created at each time
`n ∈ [T]`, with i.i.d. noise `γ_n ∼ Lap(b)` (Algorithm 2, Equation (3), with `b = 1 / ε'`). -/
noncomputable def binaryPSums (T : ℕ) (b : ℝ) : Kernel (BinStream T) (Fin T → ℝ) :=
  pSumMechanism binInterval b

/-- **Chan–Shi–Song, Theorem 3.5** (privacy of the Binary Mechanism), p-sum form, with the noise
corrected to `Lap((⌊log₂ T⌋ + 1) / ε)` (see the notes on the paper in the module docstring):
releasing all the noisy p-sums of the Binary Mechanism is `ε`-differentially private for
event-level adjacency. -/
theorem isEpsDP_binaryPSums {ε : ℝ} (hε : 0 < ε) :
    IsEpsDP (binaryPSums T ((Nat.log 2 T + 1) / ε)) Adjacent ε := by
  have := isEpsDP_pSumMechanism_of_card_le (binInterval (T := T)) hε (Nat.succ_pos _)
    card_binInterval_le
  push_cast at this
  exact this

/-- `binSum y n`: the sum of `y (m - 1)` over the binary decomposition chain
`m = n, n - lowbit n, …` of `n` down to `0` (for `n = ∑_j Bin_j(n) 2^j`, the chain visits
`2^j ⌊n / 2^j⌋` for each `j` with `Bin_j(n) = 1`). -/
noncomputable def binSum (y : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => y n + binSum y (n + 1 - lowbit (n + 1))
decreasing_by exact Nat.sub_lt n.succ_pos (lowbit_pos _)

lemma binSum_congr {y y' : ℕ → ℝ} {n : ℕ} (h : ∀ m < n, y m = y' m) :
    binSum y n = binSum y' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [binSum]
    | succ n =>
      have hlt : n + 1 - lowbit (n + 1) < n + 1 := Nat.sub_lt n.succ_pos (lowbit_pos _)
      rw [binSum, binSum, h n n.lt_succ_self,
        ih _ hlt fun m hm ↦ h m (hm.trans hlt)]

/-- With exact p-sums, `binSum` recovers the prefix sum: the intervals
`(m - lowbit m, m]` along the chain of `n` partition `(0, n]`. -/
lemma binSum_sum_Ico (x : ℕ → ℝ) (n : ℕ) :
    binSum (fun m ↦ ∑ s ∈ Ico (m + 1 - lowbit (m + 1)) (m + 1), x s) n =
      ∑ s ∈ range n, x s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [binSum]
    | succ n =>
      rw [binSum, ih _ (Nat.sub_lt n.succ_pos (lowbit_pos _)), add_comm,
        sum_range_add_sum_Ico _ (Nat.sub_le _ _)]

lemma measurable_binSum_extendZero (n : ℕ) :
    Measurable fun y : Fin T → ℝ ↦ binSum (extendZero y) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [binSum]
    | succ n =>
      simp only [binSum]
      refine Measurable.add ?_ (ih _ (Nat.sub_lt n.succ_pos (lowbit_pos _)))
      unfold extendZero
      split_ifs
      · exact measurable_pi_apply _
      · exact measurable_const

/-- **Chan–Shi–Song, Algorithm 2, Equation (4)**, in the p-sum view: given the released noisy
p-sums `y` (indexed by creation time), the estimate `B(n)` at paper time `n = t + 1` is the sum
of the noisy p-sums along the binary decomposition of `n`, i.e. of the noisy p-sum of size `2^j`
created at time `2^j ⌊n / 2^j⌋`, for each `j` with `Bin_j(n) = 1`. -/
noncomputable def binEstimate (y : Fin T → ℝ) (t : Fin T) : ℝ := binSum (extendZero y) (t + 1)

@[fun_prop]
lemma measurable_binEstimate : Measurable (binEstimate (T := T)) :=
  Measurable.of_eval fun t ↦ measurable_binSum_extendZero (t + 1)

/-- **Correctness of the Binary Mechanism's estimates**: applied to the exact p-sums, the
estimate is the exact count, `B(t) = c(t)`. Hence the error of the Binary Mechanism at time `t`
is the sum of the noises along the binary decomposition of `t`. -/
theorem binEstimate_pSum (σ : BinStream T) (t : Fin T) :
    binEstimate (fun t' ↦ pSum σ (binInterval t')) t = count σ t := by
  have hmap (m : ℕ) (hm : m < T) : (binInterval (⟨m, hm⟩ : Fin T)).map Fin.valEmbedding =
      Ico (m + 1 - lowbit (m + 1)) (m + 1) := by
    ext n
    simp only [mem_map, mem_binInterval, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨s, ⟨h₁, h₂⟩, rfl⟩
      exact ⟨h₁, Nat.lt_succ_of_le h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨n, by omega⟩, ⟨h₁, Nat.le_of_lt_succ h₂⟩, rfl⟩
  rw [binEstimate, count_eq_sum_range, ← binSum_sum_Ico]
  refine binSum_congr fun m hm ↦ ?_
  have hmT : m < T := hm.trans_le t.isLt
  rw [extendZero_of_lt hmT, pSum, sum_eq_sum_map_extendZero, hmap m hmT]

/-- **The Binary Mechanism** `B` (Chan–Shi–Song, Algorithm 2), in the p-sum view: release the
noisy p-sums (`binaryPSums`) and output at every time `t ∈ [T]` the estimate `B(t)`
(`binEstimate`). -/
noncomputable def binaryMechanism (T : ℕ) (b : ℝ) : Kernel (BinStream T) (Fin T → ℝ) :=
  (binaryPSums T b).map binEstimate

/-- **Chan–Shi–Song, Theorem 3.5** (privacy of the Binary Mechanism), with the noise corrected to
`Lap((⌊log₂ T⌋ + 1) / ε)` (see the notes on the paper in the module docstring): the `T`-bounded
Binary Mechanism, which outputs the estimated counts `(B(1), …, B(T))`, is `ε`-differentially
private for event-level adjacency. -/
theorem isEpsDP_binaryMechanism {ε : ℝ} (hε : 0 < ε) :
    IsEpsDP (binaryMechanism T ((Nat.log 2 T + 1) / ε)) Adjacent ε := by
  have : IsMarkovKernel (binaryPSums T ((Nat.log 2 T + 1) / ε)) :=
    isMarkovKernel_pSumMechanism _ (by positivity)
  exact (isEpsDP_binaryPSums hε).map measurable_binEstimate


/-- One-sided tail of the Laplace distribution: `P[Y ≥ c] = e^{-(c - μ)/b} / 2` for
`Y ∼ Lap(μ, b)` and `c ≥ μ`. -/
lemma laplaceMeasure_Ici {μ b c : ℝ} (hb : 0 < b) (hc : μ ≤ c) :
    laplaceMeasure μ b (Set.Ici c) = ENNReal.ofReal (Real.exp (-((c - μ) / b)) / 2) := by
  rw [laplaceMeasure, withDensity_apply _ measurableSet_Ici]
  unfold laplacePDF
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_laplacePDFReal μ hb).integrableOn
    (ae_of_all _ fun y ↦ (laplacePDFReal_pos hb y).le)]
  congr 1
  have h : ∫ y in Set.Ici c, laplacePDFReal μ b y =
      ∫ y in Set.Ici c, (2 * b)⁻¹ * Real.exp (μ / b) * Real.exp (-b⁻¹ * y) := by
    refine setIntegral_congr_fun measurableSet_Ici fun y hy ↦ ?_
    have hy' : μ ≤ y := hc.trans hy
    rw [laplacePDFReal, abs_of_nonneg (sub_nonneg.2 hy'), mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [h, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (neg_lt_zero.2 (inv_pos.2 hb))]
  rw [show -((c - μ) / b) = μ / b + -b⁻¹ * c by field_simp; ring, Real.exp_add]
  field_simp

/-- At the times `n` that are powers of two (`lowbit n = n`), the estimate is the noisy p-sum
created at that time: `B(2^j) = Σ̂[1, 2^j]`. -/
lemma binEstimate_of_lowbit_eq {y : Fin T → ℝ} {t : Fin T} (h : lowbit (t + 1) = t + 1) :
    binEstimate y t = y t := by
  rw [binEstimate, binSum, h, Nat.sub_self, extendZero_of_lt t.isLt]
  simp [binSum]

/-- **The noise of `isEpsDP_binaryMechanism` is optimal; Theorem 3.5 of Chan–Shi–Song is false
as stated** (a constant-factor off-by-one; see the notes on the paper): for every `T ≥ 1`, the
Binary Mechanism with i.i.d. `Lap(b)` noise is not `ε`-differentially private when
`b < (⌊log₂ T⌋ + 1) / ε`. In particular the noise `Lap(log T / ε)` of Algorithm 2
(`ε' = ε / log T`) fails for every `T ≥ 2`, for `log = log₂` and for `log = ln`; with `log₂`
the true privacy level is `((⌊log₂ T⌋ + 1) / log₂ T) ε ≤ 2ε` (`isEpsDP_binaryMechanism`).
The witnesses are the stream with a single `1` at time `1` and the zero stream: the item at
time `1` lies in the p-sums `Σ[1, 2^j]`, `2^j ≤ T`, which are the estimates `B(2^j)`, and the
event `{B(2^j) ≥ 1 for all 2^j ≤ T}` has probabilities `2^{-m}` and `e^{-m / b} 2^{-m}`,
`m = ⌊log₂ T⌋ + 1`. -/
theorem not_isEpsDP_binaryMechanism (hT : 0 < T) {ε b : ℝ} (hb : 0 < b)
    (hεb : ε * b < Nat.log 2 T + 1) : ¬IsEpsDP (binaryMechanism T b) Adjacent ε := by
  intro h
  set P : Finset (Fin T) := {t | lowbit (t + 1) = t + 1} with hP
  have hcard : Nat.log 2 T + 1 ≤ #P := by
    have hpow (j : ℕ) (hj : j ∈ range (Nat.log 2 T + 1)) : 1 ≤ 2 ^ j ∧ 2 ^ j ≤ T :=
      ⟨Nat.one_le_two_pow, (Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.1 (mem_range.1 hj))).trans
        (Nat.pow_log_le_self 2 hT.ne')⟩
    calc Nat.log 2 T + 1 = #(range (Nat.log 2 T + 1)) := (card_range _).symm
      _ ≤ #P := by
        refine card_le_card_of_injOn (fun j ↦ (⟨(2 ^ j - 1) % T, Nat.mod_lt _ hT⟩ : Fin T))
          (fun j hj ↦ ?_) fun i hi j hj hij ↦ ?_
        · have := hpow j hj
          simp only [hP, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
            Nat.mod_eq_of_lt (show 2 ^ j - 1 < T by omega), Nat.sub_add_cancel this.1]
          exact lowbit_two_pow j
        · have := hpow i hi
          have := hpow j hj
          simp only [Fin.mk.injEq, Nat.mod_eq_of_lt (show 2 ^ i - 1 < T by omega),
            Nat.mod_eq_of_lt (show 2 ^ j - 1 < T by omega)] at hij
          exact Nat.pow_right_injective le_rfl (show 2 ^ i = 2 ^ j by omega)
  let t₀ : Fin T := ⟨0, hT⟩
  let σ : BinStream T := fun s ↦ decide (s = t₀)
  let σ' : BinStream T := fun _ ↦ false
  have hadj : Adjacent σ σ' := ⟨t₀, by simp [σ, σ'], fun s hs ↦ by simp [σ, σ', hs]⟩
  let S : Fin T → Set ℝ := fun t ↦ if t ∈ P then Set.Ici 1 else Set.univ
  have hS : MeasurableSet (Set.univ.pi S) := MeasurableSet.univ_pi fun t ↦ by
    simp only [S]
    split_ifs
    exacts [measurableSet_Ici, MeasurableSet.univ]
  have hpre : binEstimate ⁻¹' Set.univ.pi S = Set.univ.pi S := by
    ext y
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    refine forall_congr' fun t ↦ ?_
    by_cases ht : t ∈ P
    · rw [binEstimate_of_lowbit_eq (by simpa [hP] using ht)]
    · simp [S, ht]
  have := fun μ : ℝ ↦ isProbabilityMeasure_laplaceMeasure μ hb
  have hlaw (τ : BinStream T) (c : ℝ) (hc : c ≤ 1) (hτ : ∀ t ∈ P, pSum τ (binInterval t) = c) :
      binaryMechanism T b τ (Set.univ.pi S) =
        ENNReal.ofReal (Real.exp (-((1 - c) / b)) / 2) ^ #P := by
    rw [binaryMechanism, Kernel.map_apply' _ measurable_binEstimate _ hS, hpre, binaryPSums,
      pSumMechanism, laplaceMechanismPi_apply (measurable_of_finite _) hb, Measure.pi_pi,
      ← prod_const, ← univ_inter P, ← prod_ite_mem]
    refine prod_congr rfl fun t _ ↦ ?_
    by_cases ht : t ∈ P
    · simp only [S, ht, ↓reduceIte, hτ t ht]
      exact laplaceMeasure_Ici hb hc
    · simp [S, ht]
  have hσ (t : Fin T) (ht : t ∈ P) : pSum σ (binInterval t) = 1 := by
    have hmem : t₀ ∈ binInterval t := by
      simp only [hP, mem_filter, mem_univ, true_and] at ht
      exact mem_binInterval.2 ⟨by simp [ht, t₀], Nat.zero_le _⟩
    rw [pSum, sum_congr rfl fun s _ ↦ show item σ s = if s = t₀ then 1 else 0 by
      by_cases hs : s = t₀ <;> simp [item, σ, hs], sum_ite_eq']
    simp [hmem]
  have : IsMarkovKernel (binaryPSums T b) := isMarkovKernel_pSumMechanism _ hb
  have : IsMarkovKernel (binaryMechanism T b) :=
    Kernel.IsMarkovKernel.map _ measurable_binEstimate
  have key := h.measure_le hadj (Set.univ.pi S)
  rw [hlaw σ 1 le_rfl hσ, hlaw σ' 0 zero_le_one fun t _ ↦ by simp [pSum, item, σ'],
    ENNReal.ofReal_zero, add_zero, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos ε).le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have hlt : Real.exp ε * Real.exp (#P * -(1 / b)) < 1 := by
    rw [← Real.exp_add, Real.exp_lt_one_iff]
    have : ε < #P / b :=
      (lt_div_iff₀ hb).2 (by exact_mod_cast hεb.trans_le (by exact_mod_cast hcard))
    have h' : (#P : ℝ) * -(1 / b) = -(#P / b) := by ring
    linarith
  simp only [sub_self, zero_div, neg_zero, Real.exp_zero, sub_zero, div_pow,
    ← Real.exp_nat_mul, one_pow] at key
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)] at key
  linarith

/-- **Theorem 3.5 of Chan–Shi–Song fails at every power of two `T = 2^k` with `k ≥ 1`**: for every
`k` (including `k = 0`), the Binary Mechanism on `T = 2^k` with i.i.d. `Lap(b)` noise of positive
scale `b` is not `ε`-differentially private when `b < (k + 1) / ε`. For `k ≥ 1` and `ε > 0`, this
applies to Algorithm 2's `b = log₂ T / ε = k / ε > 0`. For `k = 0` (`T = 1`) Algorithm 2 gives no
counterexample: its `ε' = ε / log T` is undefined, and `b = k / ε = 0` violates `0 < b`; only
the positive-scale lower bound is claimed there. -/
theorem not_isEpsDP_binaryMechanism_two_pow (k : ℕ) {ε b : ℝ} (hb : 0 < b)
    (hεb : ε * b < k + 1) : ¬IsEpsDP (binaryMechanism (2 ^ k) b) Adjacent ε :=
  not_isEpsDP_binaryMechanism (by positivity) hb (by rwa [Nat.log_pow one_lt_two])

end ContinualRelease

end InformationTheory
