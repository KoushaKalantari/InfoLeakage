/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.InformationTheory.Hamming

/-!
# Reconstruction attacks from noisy subset sums

This file formalizes the exponential-adversary reconstruction attack of I. Dinur and K. Nissim,
*Revealing information while preserving privacy*, PODS 2003, pp. 202–210
([doi:10.1145/773153.773173](https://doi.org/10.1145/773153.773173)), Section 3.1, in the form of
Theorem 8.1 of C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Found.
Trends Theor. Comput. Sci. 9(3–4), 2014, Section 8.1, together with a partial, quantitative
formalization of the remark of Dwork–Roth (p. 163) that differential privacy prevents blatant
non-privacy (partial because blatant non-privacy is formalized only in its always-success and
almost-sure variants; see the implementation notes).

A database is a bit vector `d ∈ {0,1}^n`, here `d : ι → Bool` for a finite index type `ι` (the
rows; `ι = Fin n` in the papers). A *statistical* (subset-sum) query is a set `S` of rows, with
exact answer `a_S(d) = ∑_{i ∈ S} d_i`. A mechanism answers the query `S` with a real number
`r S`, and the transcript `r : Finset ι → ℝ` collects its answers to all `2^n` queries. The answers
are *within perturbation `E`* if `|r S - a_S(d)| ≤ E` for every `S` (Dinur–Nissim, Definition 2;
"distortion of magnitude bounded by `E`" in Dwork–Roth).

The attack issues all `2^n` queries and outputs any candidate `c ∈ {0,1}^n` that is not ruled out,
i.e. that also satisfies `|r S - a_S(c)| ≤ E` for every `S`. The true database is never ruled out,
and every candidate that is not ruled out is within Hamming distance `4E` of it.

## Main definitions

* `subsetSumQuery d S`: the exact answer `∑_{i ∈ S} d_i` to the query `S`, as a real number.
* `IsWithinPerturbation E d r`: every answer of the transcript `r` is within `E` of the exact
  answer on `d` (Dinur–Nissim, Definition 2).
* `reconstructionAttack E r`: the exponential adversary, which outputs a candidate database that
  is not ruled out by the transcript `r` (one exists whenever `r` comes from a mechanism within
  perturbation `E`).
* `IsBlatantlyNonPrivate M`: an *always-success* variant of blatant non-privacy (Dwork–Roth,
  Definition 8.1) for a family of mechanisms given by the nonempty sets `M n d` of transcripts
  they may produce on databases `d ∈ {0,1}^n`: some adversary reconstructs every database up to
  `o(n)` entries from *every* such transcript.
* `IsBlatantlyNonPrivateAE K`: the *almost-sure* variant for randomized mechanisms given by Markov
  kernels `K n`: some measurable adversary reconstructs every database up to `o(n)` entries
  almost surely.

Both predicates demand reconstruction with failure probability zero. They are therefore
**stronger** than non-privacy in the sense of Definition 3 of Dinur–Nissim, which only asks for
success with probability `1 - neg(n)`, and than the high-probability attacks discussed by
Dwork–Roth (see the implementation notes).

## Main statements

* `hammingDist_le_of_isWithinPerturbation`: two databases that are both consistent with the same
  transcript up to perturbation `E` are at Hamming distance at most `4E` (the combinatorial core
  of both proofs).
* `hammingDist_reconstructionAttack_le`: **Theorem 8.1 of Dwork–Roth**: against a mechanism within
  perturbation `E`, the attack reconstructs the database up to `4E` positions;
  `exists_reconstruction_adversary` is the existential form of the theorem as stated.
* `hammingDist_reconstructionAttack_lt_div`: the remark after Theorem 8.1 of Dwork–Roth: noise
  bounded by `n / 401` lets the adversary reconstruct more than `99%` of the entries.
* `isBlatantlyNonPrivate_of_isLittleO`: **Theorem 2 of Dinur–Nissim**, deterministic form: a
  family of mechanisms within perturbation `o(n)` is blatantly non-private.
* `IsBlatantlyNonPrivate.exists_eventually_lt`: always-success blatant non-privacy gives the
  reconstruction required by Definition 3 of Dinur–Nissim, in a stronger form: for every constant
  `ε > 0`, eventually in `n`, fewer than `εn` entries are wrong (with probability one rather than
  `1 - neg(n)`, and by the same adversary for every `ε`).
* `not_isBlatantlyNonPrivate_const`: sanity check, a mechanism with constant answers is not
  blatantly non-private.
* `ae_hammingDist_reconstructionAttack_le`, `isBlatantlyNonPrivateAE_of_isLittleO`: the same two
  results for randomized mechanisms (kernels) whose answers are almost surely within perturbation.
* `not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP`: for fixed `ε` and `δ < 1`, a family of
  `(ε, δ)`-differentially private mechanisms is not blatantly non-private in the almost-sure
  sense. Since `IsBlatantlyNonPrivateAE` is stronger than Dinur–Nissim non-privacy, this does not
  by itself exclude reconstruction attacks that fail with small positive probability.
* `IsEpsDeltaDP.exists_card_mul_one_sub_le_sum_hammingDist`: an `(ε, δ)`-differentially private
  randomized reconstruction of an `n`-bit database errs, on some database, in at least
  `n (1 - δ) / (1 + e^ε)` entries in expectation.
* `card_mul_one_sub_le_of_isEpsDeltaDP`, `le_perturbation_of_isEpsDeltaDP`: if an
  `(ε, δ)`-differentially private mechanism answers all subset-sum queries within perturbation
  `E ≥ 0` with probability at least `1 - β` on every database, then
  `n (1 - δ) ≤ (1 + e^ε)(4E + βn)`, i.e. `E ≥ (n / 4)((1 - δ) / (1 + e^ε) - β)`: the perturbation
  is linear in `n` for fixed `ε`, `δ`, `β` with `β (1 + e^ε) < 1 - δ`.

## Correspondence with the papers

* Dinur–Nissim, Definition 1 (statistical query and its exact answer `a_q`): `subsetSumQuery`.
* Dinur–Nissim, Definition 2 (within `E` perturbation): `IsWithinPerturbation`.
* Dinur–Nissim, Theorem 2 / Dwork–Roth, Theorem 8.1: `hammingDist_le_of_isWithinPerturbation`,
  `hammingDist_reconstructionAttack_le`, `exists_reconstruction_adversary`, and the asymptotic
  form `isBlatantlyNonPrivate_of_isLittleO`; for randomized mechanisms,
  `ae_hammingDist_reconstructionAttack_le` and `isBlatantlyNonPrivateAE_of_isLittleO`.
* Dwork–Roth, Definition 8.1 (blatant non-privacy), **partial**: `IsBlatantlyNonPrivate`
  (always-success variant) and `IsBlatantlyNonPrivateAE` (almost-sure variant). Definition 8.1
  does not fix a success probability, and the surrounding discussion includes attacks that
  succeed only with high probability; those are not covered by either predicate.
* Dinur–Nissim, Definition 3 (non-privacy), **partial**:
  `IsBlatantlyNonPrivate.exists_eventually_lt` shows that the always-success predicate implies
  the reconstruction required by Definition 3
  (with failure probability zero instead of `neg(n)`, and without the running time `t(n)`). The
  converse fails, so Definition 3 itself, with its negligible failure probability, is not
  formalized.
* Dwork–Roth, the remark after Theorem 8.1 (`n / 401`, `99%`):
  `hammingDist_reconstructionAttack_lt_div`.
* Dwork–Roth, the remark after the proof of Theorem 8.2 (p. 163: "if differential privacy is
  meaningful then lower bounds for preventing blatant non-privacy will also apply to any mechanism
  ensuring differential privacy"), **partial**: `not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP`,
  `IsEpsDeltaDP.exists_card_mul_one_sub_le_sum_hammingDist`,
  `card_mul_one_sub_le_of_isEpsDeltaDP`, `le_perturbation_of_isEpsDeltaDP`. The monograph makes
  this remark informally; the statements and constants are derived here. The non-privacy
  conclusion `not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP` only rules out the almost-sure variant
  of blatant non-privacy, which is a weaker privacy guarantee than ruling out reconstruction with
  negligible failure probability; that stronger form is not formalized here.

## Implementation notes

* A mechanism is modelled through the answers it returns, not through its internals: Dinur–Nissim
  allow the database algorithm to be randomized and to keep an internal state, and Dwork–Roth an
  arbitrary interactive or non-interactive mechanism. Since the bound `E` on the perturbation is
  assumed to hold for *every* answer, the attack succeeds on every transcript the mechanism can
  produce. Accordingly, a family of mechanisms is given either by the nonempty sets `M n d` of
  transcripts it can produce on `d` (`IsBlatantlyNonPrivate`), or by Markov kernels `K n` with
  the bounds holding almost surely (`IsBlatantlyNonPrivateAE`), for the fixed order in which the
  adversary issues the queries.
* **Success probability.** Both blatant non-privacy predicates require the adversary to succeed
  with probability one, whereas Definition 3 of Dinur–Nissim allows failure probability
  `neg(n)`. The notions are distinct: a mechanism that releases the exact subset sums with
  probability `1 - 2^{-n}`, and otherwise one fixed transcript shared by every database, is
  non-private in the sense of Dinur–Nissim, but satisfies neither predicate (on the shared
  transcript the adversary's output is the same for every database, so on some database it errs
  in all `n` entries with positive probability). For the positive results
  (`isBlatantlyNonPrivate_of_isLittleO`, `isBlatantlyNonPrivateAE_of_isLittleO`) the stronger
  predicates give stronger conclusions; for the negative result
  `not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP` they give a weaker one.
* Running time is not formalized: the adversary is a function of the transcript of all `2^n`
  answers, which is what makes it exponential (the `exp(n)` of Dinur–Nissim, Theorem 2).
* Answers and the perturbation bound are real numbers; nothing requires them to be integers.
* For the differential-privacy statements, a mechanism is a Markov kernel from databases to
  transcripts, neighbouring databases differ in exactly one entry, and `(ε, δ)`-DP is
  `IsEpsDeltaDP` of `InfoLeakage.FDP.Basic`. The lower bound on the expected error is the standard
  averaging argument: for each entry `i` and database `d`, differential privacy between `d` and `d`
  with entry `i` flipped bounds the probability of guessing `dᵢ` correctly by `e^ε` times the
  probability of guessing wrongly on the flipped database, plus `δ`; summing over all entries and
  all `2^n` databases (flipping entry `i` is a bijection) gives the bound. An almost sure bound
  `f n = o(n)` on the error would bound this expectation by `f n`, which is impossible for large
  `n`. The perturbation bound follows because the reconstruction attack is a (measurable)
  post-processing of the answers.

## Notes on the paper

* Dinur–Nissim, proof of Theorem 2 (Section 3.1, p. 205 of the PODS version): the sets are
  defined as `q₀ = {i | dᵢ = 1, cᵢ = 0}` and `q₁ = {i | dᵢ = 0, cᵢ = 1}`, but the next sentence
  says "at least one of the disjoint sets `q₁, q₂` has size `2E + 1` or more"; this should read
  `q₀, q₁`. Moreover, "size `2E + 1` or more" follows from `|q₀| + |q₁| > 4E` only when `2E` is
  an integer (it fails, e.g., for `E = 0.6` with sizes `2` and `1`; `E` is not assumed integral);
  the proof only uses the correct consequence `|q₁| > 2E` (w.l.o.g.), stated in the next sentence.
  The theorem and the proof are correct with this reading.
-/

@[expose] public section

open Finset Filter Asymptotics MeasureTheory ProbabilityTheory Real

namespace InformationTheory

variable {ι : Type*}

/-! ### Subset-sum queries and perturbation -/

/-- The exact answer `a_S(d) = ∑_{i ∈ S} d_i` to the statistical (subset-sum) query `S` on the
database `d ∈ {0,1}^ι` (Definition 1 of Dinur–Nissim; the count of `1`s among the rows in `S`). -/
def subsetSumQuery (d : ι → Bool) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, ((d i).toNat : ℝ)

/-- The transcript `r : Finset ι → ℝ` of answers to all subset-sum queries is **within
perturbation `E`** of the database `d` if `|r S - ∑_{i ∈ S} d_i| ≤ E` for every query `S`
(Definition 2 of Dinur–Nissim). For a candidate database `c`, `IsWithinPerturbation E c r` says
that `c` is not ruled out by `r` in the attack of Theorem 8.1 of Dwork–Roth. -/
def IsWithinPerturbation (E : ℝ) (d : ι → Bool) (r : Finset ι → ℝ) : Prop :=
  ∀ S, |r S - subsetSumQuery d S| ≤ E

namespace Reconstruction

variable [Fintype ι]

/-- The Hamming distance between `c` and `d` as a combination of four subset sums: on the rows
`I₀` where `d` is `0`, `∑_{I₀} (cᵢ - dᵢ)` counts the disagreements in `I₀`; on the rows `I₁` where
`d` is `1`, `∑_{I₁} (dᵢ - cᵢ)` counts those in `I₁`. -/
lemma hammingDist_eq (c d : ι → Bool) :
    (hammingDist c d : ℝ) =
      (subsetSumQuery c {i | d i = false} - subsetSumQuery d {i | d i = false}) +
        (subsetSumQuery d {i | d i = true} - subsetSumQuery c {i | d i = true}) := by
  simp only [hammingDist, subsetSumQuery, card_filter, sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  cases c i <;> cases d i <;> simp

end Reconstruction

variable [Fintype ι] {E : ℝ} {c d : ι → Bool} {r : Finset ι → ℝ}

/-- **The combinatorial core of Theorem 8.1 of Dwork–Roth** (and of Theorem 2 of Dinur–Nissim):
if the transcript `r` is within perturbation `E` of both `c` and `d`, then `c` and `d` differ in at
most `4E` positions. -/
theorem hammingDist_le_of_isWithinPerturbation (hc : IsWithinPerturbation E c r)
    (hd : IsWithinPerturbation E d r) : (hammingDist c d : ℝ) ≤ 4 * E := by
  have key (S : Finset ι) : |subsetSumQuery c S - subsetSumQuery d S| ≤ 2 * E := by
    calc |subsetSumQuery c S - subsetSumQuery d S|
        = |(r S - subsetSumQuery d S) - (r S - subsetSumQuery c S)| := by ring_nf
      _ ≤ |r S - subsetSumQuery d S| + |r S - subsetSumQuery c S| := abs_sub _ _
      _ ≤ 2 * E := by linarith [hc S, hd S]
  rw [Reconstruction.hammingDist_eq]
  linarith [le_abs_self (subsetSumQuery c {i | d i = false} - subsetSumQuery d {i | d i = false}),
    neg_abs_le (subsetSumQuery c {i | d i = true} - subsetSumQuery d {i | d i = true}),
    key {i | d i = false}, key {i | d i = true}]

/-! ### The reconstruction attack -/

open scoped Classical in
/-- The **exponential reconstruction adversary** of Theorem 8.1 of Dwork–Roth (the algorithm in
the proof of Theorem 2 of Dinur–Nissim): given the answers `r` to all `2^n` subset-sum queries,
output a candidate database `c` that is not ruled out, i.e. with `|r S - ∑_{i ∈ S} c_i| ≤ E` for
every `S` (and the all-zero database if every candidate is ruled out, which cannot happen when
`r` is within perturbation `E` of the true database). -/
noncomputable def reconstructionAttack (E : ℝ) (r : Finset ι → ℝ) : ι → Bool :=
  if h : ∃ c, IsWithinPerturbation E c r then h.choose else fun _ ↦ false

/-- If some candidate is consistent with the transcript, the attack outputs a consistent
candidate. -/
lemma isWithinPerturbation_reconstructionAttack (hd : IsWithinPerturbation E d r) :
    IsWithinPerturbation E (reconstructionAttack E r) r := by
  have h : ∃ c, IsWithinPerturbation E c r := ⟨d, hd⟩
  rw [reconstructionAttack, dite_eq_left h]
  exact h.choose_spec

/-- **Theorem 8.1 of Dwork–Roth** (Theorem 2 of Dinur–Nissim, non-asymptotic form): if the
mechanism's answers `r` to all subset-sum queries are within perturbation `E` of the database `d`,
the reconstruction adversary outputs a database that differs from `d` in at most `4E` positions. -/
theorem hammingDist_reconstructionAttack_le (hd : IsWithinPerturbation E d r) :
    (hammingDist (reconstructionAttack E r) d : ℝ) ≤ 4 * E :=
  hammingDist_le_of_isWithinPerturbation (isWithinPerturbation_reconstructionAttack hd) hd

/-- **Theorem 8.1 of Dwork–Roth**, as stated: against any mechanism whose distortion is bounded by
`E`, there is an adversary (depending only on `E`, not on the database) that reconstructs the
database to within `4E` positions from the answers to all subset-sum queries. -/
theorem exists_reconstruction_adversary (E : ℝ) :
    ∃ A : (Finset ι → ℝ) → ι → Bool, ∀ (d : ι → Bool) (r : Finset ι → ℝ),
      IsWithinPerturbation E d r → (hammingDist (A r) d : ℝ) ≤ 4 * E :=
  ⟨reconstructionAttack E, fun _ _ ↦ hammingDist_reconstructionAttack_le⟩

/-- The remark after Theorem 8.1 of Dwork–Roth: if the noise is always bounded by `n / 401`, where
`n ≥ 1` is the number of rows, the adversary gets fewer than `n / 100` entries wrong, that is, it
reconstructs more than `99%` of them. (The non-strict bound `≤ n / 100` already holds for noise
bounded by `n / 400`, by `hammingDist_reconstructionAttack_le`.) -/
theorem hammingDist_reconstructionAttack_lt_div [Nonempty ι] (hd : IsWithinPerturbation E d r)
    (hE : E ≤ Fintype.card ι / 401) :
    (hammingDist (reconstructionAttack E r) d : ℝ) < Fintype.card ι / 100 := by
  have := hammingDist_reconstructionAttack_le hd
  have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  linarith

/-! ### Blatant non-privacy -/

/-- A family of mechanisms answering subset-sum queries on databases `d ∈ {0,1}^n`, given by the
nonempty sets `M n d` of transcripts (answers to all subset-sum queries) they can produce on `d`,
is **blatantly non-private, always-success variant** (of Definition 8.1 of Dwork–Roth) if an
adversary can construct from the transcript a candidate database that agrees with the real one in
all but `o(n)` entries: there are adversaries `A n` and a function `f = o(n)` such that
`‖A n r - d‖₀ ≤ f n` for every `n`, every database `d` and every transcript `r ∈ M n d`.
Nonemptiness (a mechanism always answers) rules out the vacuous case; see
`not_isBlatantlyNonPrivate_const` for a mechanism that is not blatantly non-private.

Success is required on *every* transcript, so this is stronger than non-privacy in the sense of
Definition 3 of Dinur–Nissim, which allows the attack to fail with probability `neg(n)`. -/
def IsBlatantlyNonPrivate (M : ∀ n : ℕ, (Fin n → Bool) → Set (Finset (Fin n) → ℝ)) : Prop :=
  (∀ n (d : Fin n → Bool), (M n d).Nonempty) ∧
    ∃ A : ∀ n : ℕ, (Finset (Fin n) → ℝ) → Fin n → Bool, ∃ f : ℕ → ℝ,
      f =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
        ∀ n (d : Fin n → Bool), ∀ r ∈ M n d, (hammingDist (A n r) d : ℝ) ≤ f n

/-- **Theorem 2 of Dinur–Nissim** (deterministic form, without the running time): a family of
mechanisms whose answers to all subset-sum queries are within perturbation `E n = o(n)` is
blatantly non-private; the exponential adversary `reconstructionAttack (E n)` reconstructs all but
`4 E n` entries. The bound `exp(n)` on the adversary's running time in the theorem is not
formalized (the adversary is a function of all `2^n` answers). For randomized mechanisms given by
kernels, see `isBlatantlyNonPrivateAE_of_isLittleO`. -/
theorem isBlatantlyNonPrivate_of_isLittleO
    {M : ∀ n : ℕ, (Fin n → Bool) → Set (Finset (Fin n) → ℝ)} {E : ℕ → ℝ}
    (hE : E =o[atTop] (fun n : ℕ ↦ (n : ℝ))) (hne : ∀ n (d : Fin n → Bool), (M n d).Nonempty)
    (hM : ∀ n (d : Fin n → Bool), ∀ r ∈ M n d, IsWithinPerturbation (E n) d r) :
    IsBlatantlyNonPrivate M :=
  ⟨hne, fun n ↦ reconstructionAttack (E n), fun n ↦ 4 * E n, hE.const_mul_left 4,
    fun n d r hr ↦ hammingDist_reconstructionAttack_le (hM n d r hr)⟩

/-- Always-success blatant non-privacy gives the reconstruction demanded by **Definition 3 of
Dinur–Nissim** (non-privacy), in a stronger form: one family of adversaries such that, for every
constant `ε > 0` and all sufficiently large `n`, the output differs from the database in fewer
than `εn` entries, for every database and every transcript the mechanism can produce (failure
probability zero rather than `neg(n)`; running time not formalized). The converse does not hold:
Definition 3 allows a negligible failure probability, which `IsBlatantlyNonPrivate` does not. -/
theorem IsBlatantlyNonPrivate.exists_eventually_lt
    {M : ∀ n : ℕ, (Fin n → Bool) → Set (Finset (Fin n) → ℝ)} (hM : IsBlatantlyNonPrivate M) :
    ∃ A : ∀ n : ℕ, (Finset (Fin n) → ℝ) → Fin n → Bool, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ (d : Fin n → Bool), ∀ r ∈ M n d, (hammingDist (A n r) d : ℝ) < ε * n := by
  obtain ⟨-, A, f, hf, hA⟩ := hM
  refine ⟨A, fun ε hε ↦ ?_⟩
  filter_upwards [hf.def (half_pos hε), eventually_ge_atTop 1] with n hn hn1 d r hr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.norm_natCast] at hn
  calc (hammingDist (A n r) d : ℝ) ≤ f n := hA n d r hr
    _ ≤ ‖f n‖ := Real.le_norm_self _
    _ ≤ ε / 2 * n := hn
    _ < ε * n := by linarith [mul_pos hε hn0]

omit [Fintype ι] in
/-- Flipping every entry of a database gives a database at Hamming distance `n` from it. -/
lemma Reconstruction.hammingDist_not (n : ℕ) (c : Fin n → Bool) :
    hammingDist c (fun i ↦ !c i) = n := by
  rw [hammingDist, filter_true_of_mem fun i _ ↦ by simp, card_univ, Fintype.card_fin]

/-- **Sanity check**: a mechanism that gives the same answers `r₀ n` on every database is not
blatantly non-private (the adversary's output is then independent of the database, so it is wrong
in every entry on the complementary database). -/
theorem not_isBlatantlyNonPrivate_const (r₀ : ∀ n : ℕ, Finset (Fin n) → ℝ) :
    ¬ IsBlatantlyNonPrivate fun n _ ↦ {r₀ n} := by
  intro h
  obtain ⟨A, hA⟩ := h.exists_eventually_lt
  obtain ⟨n, hn, hn1⟩ := ((hA 1 one_pos).and (eventually_ge_atTop 1)).exists
  have := hn (fun i ↦ !A n (r₀ n) i) (r₀ n) rfl
  rw [Reconstruction.hammingDist_not, one_mul] at this
  exact lt_irrefl _ this

/-! ### Consequence for differentially private mechanisms -/

namespace Reconstruction

omit [Fintype ι] in
/-- The set of transcripts within perturbation `E` of a database is measurable. -/
lemma measurableSet_isWithinPerturbation [Finite ι] (E : ℝ) (d : ι → Bool) :
    MeasurableSet {r : Finset ι → ℝ | IsWithinPerturbation E d r} := by
  simp only [IsWithinPerturbation, Set.ofPred_forall]
  exact MeasurableSet.iInter fun S ↦ measurableSet_le (by fun_prop) measurable_const

open scoped Classical in
/-- The reconstruction adversary is a measurable function of the transcript: it factors through
the finite set of candidates consistent with the transcript. -/
lemma measurable_reconstructionAttack (E : ℝ) :
    Measurable (reconstructionAttack (ι := ι) E) := by
  have h : reconstructionAttack (ι := ι) E =
      (fun P : (ι → Bool) → Prop ↦ if h : ∃ c, P c then h.choose else fun _ ↦ false) ∘
        fun r c ↦ IsWithinPerturbation E c r := rfl
  rw [h]
  refine (measurable_of_countable _).comp (Measurable.of_eval fun c ↦ ?_)
  exact measurableSet_setOfPred.1 (measurableSet_isWithinPerturbation E c)

variable [DecidableEq ι]

/-- The database `d` with its entry `i` flipped. -/
def flipEntry (d : ι → Bool) (i : ι) : ι → Bool :=
  Function.update d i (!d i)

omit [Fintype ι] in
/-- Flipping the same entry twice gives back the database. -/
lemma flipEntry_flipEntry (d : ι → Bool) (i : ι) : flipEntry (flipEntry d i) i = d := by
  simp [flipEntry]

/-- A database and the database with one entry flipped are neighbours: they are at Hamming
distance `1`. -/
lemma hammingDist_flipEntry (d : ι → Bool) (i : ι) : hammingDist d (flipEntry d i) = 1 := by
  rw [hammingDist, card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  rw [Finset.mem_filter, mem_singleton]
  by_cases hj : j = i
  · subst hj
    simp [flipEntry]
  · simp [flipEntry, hj]

end Reconstruction

open Reconstruction

variable [DecidableEq ι] {ε δ : ℝ}

/-- **Differentially private reconstructions err on a constant fraction of the entries.** If a
randomized reconstruction `R` of an `n`-bit database (a Markov kernel from databases to candidate
databases) is `(ε, δ)`-differentially private for databases differing in one entry, then on some
database `d` the expected Hamming distance between the output and `d` is at least
`n (1 - δ) / (1 + e^ε)` (the constant is derived here, not quoted from Dwork–Roth). This is the
key step of `not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP`. -/
theorem IsEpsDeltaDP.exists_card_mul_one_sub_le_sum_hammingDist
    {R : Kernel (ι → Bool) (ι → Bool)} [IsMarkovKernel R]
    (hR : IsEpsDeltaDP R (fun d d' ↦ hammingDist d d' = 1) ε δ) :
    ∃ d, (Fintype.card ι : ℝ) * (1 - δ) ≤
      (1 + exp ε) * ∑ c, (R d).real {c} * hammingDist c d := by
  -- `x d i` is the probability that entry `i` of the output differs from `dᵢ`.
  set x : (ι → Bool) → ι → ℝ := fun d i ↦ (R d).real {c | c i ≠ d i} with hx
  have hsum (d : ι → Bool) : ∑ c, (R d).real {c} * hammingDist c d = ∑ i, x d i := by
    simp only [hammingDist, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, mul_sum, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_filter, sum_measureReal_singleton, coe_filter]
    simp [hx]
  have hflip (d : ι → Bool) (i : ι) : 1 - x d i ≤ exp ε * x (flipEntry d i) i + δ := by
    have hset : {c : ι → Bool | c i ≠ flipEntry d i i} = {c | c i ≠ d i}ᶜ := by
      ext c
      simp only [flipEntry, Function.update_self, Set.mem_ofPred_eq, Set.mem_compl_iff, not_not]
      cases c i <;> cases d i <;> simp
    have h := hR (hammingDist_flipEntry d i) {c | c i ≠ flipEntry d i i}
    rwa [hset, probReal_compl_eq_one_sub (MeasurableSet.of_discrete), ← hset] at h
  have hT : ∑ d, ∑ i, x (flipEntry d i) i = ∑ d, ∑ i, x d i := by
    rw [sum_comm, sum_comm (f := x)]
    exact sum_congr rfl fun i _ ↦
      Equiv.sum_comp (Function.Involutive.toPerm (flipEntry · i) (flipEntry_flipEntry · i)) (x · i)
  have hmain : ∑ _d : ι → Bool, (Fintype.card ι : ℝ) * (1 - δ) ≤
      ∑ d, (1 + exp ε) * ∑ i, x d i := by
    have h := sum_le_sum fun d (_ : d ∈ univ) ↦ sum_le_sum fun i (_ : i ∈ univ) ↦ hflip d i
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, card_univ,
      nsmul_eq_mul, mul_one, hT] at h
    simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
    linarith
  obtain ⟨d, -, hd⟩ := exists_le_of_sum_le univ_nonempty hmain
  exact ⟨d, by rwa [hsum]⟩

variable {β : ℝ}

omit [DecidableEq ι] in
/-- **Differentially private mechanisms need linear perturbation on subset-sum queries.** If an
`(ε, δ)`-differentially private mechanism `M` (for databases differing in one entry) answers all
subset-sum queries on an `n`-bit database within perturbation `E ≥ 0` with probability at least
`1 - β`, for every database, then `n (1 - δ) ≤ (1 + e^ε)(4E + βn)`. This combines Theorem 8.1 of
Dwork–Roth (the reconstruction attack, a post-processing of the answers) with
`IsEpsDeltaDP.exists_card_mul_one_sub_le_sum_hammingDist`; it is a quantitative consequence in
the spirit of the remark on p. 163 of Dwork–Roth (the statement and constant are derived here, not
quoted). -/
theorem card_mul_one_sub_le_of_isEpsDeltaDP {M : Kernel (ι → Bool) (Finset ι → ℝ)}
    [IsMarkovKernel M] (hM : IsEpsDeltaDP M (fun d d' ↦ hammingDist d d' = 1) ε δ) (hE : 0 ≤ E)
    (hacc : ∀ d, 1 - β ≤ (M d).real {r | IsWithinPerturbation E d r}) :
    (Fintype.card ι : ℝ) * (1 - δ) ≤ (1 + exp ε) * (4 * E + β * Fintype.card ι) := by
  classical
  have hA := measurable_reconstructionAttack (ι := ι) E
  have := Kernel.IsMarkovKernel.map M hA
  obtain ⟨d, hd⟩ := (hM.map hA).exists_card_mul_one_sub_le_sum_hammingDist
  refine hd.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  set μ := M.map (reconstructionAttack E) d with hμ
  set K : Finset (ι → Bool) := {c | (hammingDist c d : ℝ) ≤ 4 * E}
  -- Outside `K` the attack has failed, which happens only off the accuracy event.
  have hKc : μ.real (↑Kᶜ : Set (ι → Bool)) ≤ β := by
    rw [hμ, Kernel.map_apply M hA, map_measureReal_apply hA (MeasurableSet.of_discrete)]
    have hsub : reconstructionAttack E ⁻¹' (↑Kᶜ : Set (ι → Bool)) ⊆
        {r | IsWithinPerturbation E d r}ᶜ := by
      intro r hr hr'
      simp only [Set.mem_preimage, coe_compl, Set.mem_compl_iff, mem_coe, K, mem_filter,
        mem_univ, true_and] at hr
      exact hr (hammingDist_reconstructionAttack_le hr')
    calc (M d).real (reconstructionAttack E ⁻¹' (↑Kᶜ : Set (ι → Bool)))
        ≤ (M d).real {r | IsWithinPerturbation E d r}ᶜ := measureReal_mono hsub
      _ = 1 - (M d).real {r | IsWithinPerturbation E d r} :=
        probReal_compl_eq_one_sub (measurableSet_isWithinPerturbation E d)
      _ ≤ β := by linarith [hacc d]
  have hK : ∑ c ∈ K, μ.real {c} * hammingDist c d ≤ ∑ c ∈ K, μ.real {c} * (4 * E) :=
    sum_le_sum fun c hc ↦ mul_le_mul_of_nonneg_left (by simpa [K] using hc) measureReal_nonneg
  have hKc' : ∑ c ∈ Kᶜ, μ.real {c} * hammingDist c d ≤
      ∑ c ∈ Kᶜ, μ.real {c} * Fintype.card ι :=
    sum_le_sum fun c _ ↦ mul_le_mul_of_nonneg_left (by exact_mod_cast hammingDist_le_card_fintype)
      measureReal_nonneg
  rw [← sum_add_sum_compl K]
  rw [← sum_mul, sum_measureReal_singleton] at hK hKc'
  have h1 : μ.real (K : Set (ι → Bool)) ≤ 1 := measureReal_le_one
  have h4 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * E),
    mul_le_mul_of_nonneg_left hKc h4]

omit [DecidableEq ι] in
/-- **Linear lower bound on the perturbation of differentially private mechanisms**: under the
hypotheses of `card_mul_one_sub_le_of_isEpsDeltaDP`,
`E ≥ (n / 4) ((1 - δ) / (1 + e^ε) - β)`, where `n` is the number of entries. -/
theorem le_perturbation_of_isEpsDeltaDP {M : Kernel (ι → Bool) (Finset ι → ℝ)}
    [IsMarkovKernel M] (hM : IsEpsDeltaDP M (fun d d' ↦ hammingDist d d' = 1) ε δ) (hE : 0 ≤ E)
    (hacc : ∀ d, 1 - β ≤ (M d).real {r | IsWithinPerturbation E d r}) :
    Fintype.card ι / 4 * ((1 - δ) / (1 + exp ε) - β) ≤ E := by
  have h := card_mul_one_sub_le_of_isEpsDeltaDP hM hE hacc
  have hpos : 0 < 1 + exp ε := by positivity
  have : (Fintype.card ι : ℝ) * (1 - δ) / (1 + exp ε) ≤ 4 * E + β * Fintype.card ι :=
    (div_le_iff₀ hpos).2 (by linarith)
  calc Fintype.card ι / 4 * ((1 - δ) / (1 + exp ε) - β)
      = ((Fintype.card ι : ℝ) * (1 - δ) / (1 + exp ε) - β * Fintype.card ι) / 4 := by ring
    _ ≤ E := by linarith


/-! ### Blatant non-privacy of randomized mechanisms -/

/-- **Blatant non-privacy of randomized mechanisms, almost-sure variant** (of Definition 8.1 of
Dwork–Roth, for a family of mechanisms given by Markov kernels `K n` from databases `d ∈ {0,1}^n`
to transcripts of answers to all subset-sum queries): some family of measurable adversaries `A n`
and some `f = o(n)` satisfy `‖A n r - d‖₀ ≤ f n` almost surely for `r ∼ K n d`, for every `n` and
every database `d`. The kernels are required to be Markov, which rules out the vacuous case of the
zero kernel.

Success is required almost surely, so this is stronger than non-privacy in the sense of
Definition 3 of Dinur–Nissim, which allows the attack to fail with probability `neg(n)`; its
negation, as in `not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP`, is correspondingly weaker. -/
def IsBlatantlyNonPrivateAE (K : ∀ n : ℕ, Kernel (Fin n → Bool) (Finset (Fin n) → ℝ)) : Prop :=
  (∀ n, IsMarkovKernel (K n)) ∧
    ∃ A : ∀ n : ℕ, (Finset (Fin n) → ℝ) → Fin n → Bool, (∀ n, Measurable (A n)) ∧
      ∃ f : ℕ → ℝ, f =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
        ∀ n (d : Fin n → Bool), ∀ᵐ r ∂(K n d), (hammingDist (A n r) d : ℝ) ≤ f n

omit [DecidableEq ι] in
/-- **Theorem 8.1 of Dwork–Roth for a randomized mechanism**: if the answers `r ∼ μ` are almost
surely within perturbation `E` of `d`, the reconstruction attack almost surely errs in at most
`4E` entries. -/
theorem ae_hammingDist_reconstructionAttack_le {μ : Measure (Finset ι → ℝ)}
    (h : ∀ᵐ r ∂μ, IsWithinPerturbation E d r) :
    ∀ᵐ r ∂μ, (hammingDist (reconstructionAttack E r) d : ℝ) ≤ 4 * E :=
  h.mono fun _ ↦ hammingDist_reconstructionAttack_le

/-- **Theorem 2 of Dinur–Nissim for randomized mechanisms** (without the running time): a family of
mechanisms, given by Markov kernels, whose answers to all subset-sum queries are almost surely
within perturbation `E n = o(n)` is blatantly non-private: the (measurable) attack
`reconstructionAttack (E n)` almost surely errs in at most `4 E n = o(n)` entries. -/
theorem isBlatantlyNonPrivateAE_of_isLittleO
    {K : ∀ n : ℕ, Kernel (Fin n → Bool) (Finset (Fin n) → ℝ)} [∀ n, IsMarkovKernel (K n)]
    {E : ℕ → ℝ} (hE : E =o[atTop] (fun n : ℕ ↦ (n : ℝ)))
    (hK : ∀ n (d : Fin n → Bool), ∀ᵐ r ∂(K n d), IsWithinPerturbation (E n) d r) :
    IsBlatantlyNonPrivateAE K :=
  ⟨fun _ ↦ inferInstance, fun n ↦ reconstructionAttack (E n),
    fun _ ↦ measurable_reconstructionAttack _, fun n ↦ 4 * E n, hE.const_mul_left 4,
    fun n d ↦ ae_hammingDist_reconstructionAttack_le (hK n d)⟩

/-- **Differential privacy prevents almost-sure blatant non-privacy** (a partial formalization of
the remark on p. 163 of Dwork–Roth): for fixed `ε` and `δ < 1`, a family of mechanisms that are
`(ε, δ)`-differentially private for databases differing in one entry is not blatantly non-private
in the almost-sure sense: no family of measurable adversaries errs in only `o(n)` entries almost
surely. Indeed, by `IsEpsDeltaDP.exists_card_mul_one_sub_le_sum_hammingDist`, any such adversary
errs in at least `n (1 - δ) / (1 + e^ε)` entries in expectation on some database.

Because `IsBlatantlyNonPrivateAE` demands success with probability one, this conclusion is weaker
than the remark: it does not exclude attacks that succeed with probability `1 - neg(n)`, as allowed
by Definition 3 of Dinur–Nissim. That stronger form is not formalized here. -/
theorem not_isBlatantlyNonPrivateAE_of_isEpsDeltaDP
    {K : ∀ n : ℕ, Kernel (Fin n → Bool) (Finset (Fin n) → ℝ)}
    (hK : ∀ n, IsEpsDeltaDP (K n) (fun d d' ↦ hammingDist d d' = 1) ε δ) (hδ : δ < 1) :
    ¬ IsBlatantlyNonPrivateAE K := by
  rintro ⟨hM, A, hA, f, hf, hAf⟩
  have hpos : 0 < 1 + exp ε := by positivity
  have hκ : 0 < (1 - δ) / (2 * (1 + exp ε)) := div_pos (by linarith) (by positivity)
  obtain ⟨n, hn, hn1⟩ := ((hf.def hκ).and (eventually_ge_atTop 1)).exists
  rw [Real.norm_natCast] at hn
  have := hM n
  have := Kernel.IsMarkovKernel.map (K n) (hA n)
  obtain ⟨d, hd⟩ := ((hK n).map (hA n)).exists_card_mul_one_sub_le_sum_hammingDist
  set μ := (K n).map (A n) d with hμ
  -- The output is within `f n` of `d` almost surely, hence on every atom of positive mass.
  have hae : ∀ᵐ c ∂μ, (hammingDist c d : ℝ) ≤ f n := by
    rw [hμ, Kernel.map_apply _ (hA n)]
    exact (ae_map_iff (hA n).aemeasurable MeasurableSet.of_discrete).2 (hAf n d)
  have hterm (c : Fin n → Bool) : μ.real {c} * hammingDist c d ≤ μ.real {c} * f n := by
    by_cases hc : (hammingDist c d : ℝ) ≤ f n
    · exact mul_le_mul_of_nonneg_left hc measureReal_nonneg
    · have h0 : μ {c} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.2 hc) (ae_iff.1 hae)
      simp [measureReal_def, h0]
  have hexp : ∑ c, μ.real {c} * hammingDist c d ≤ f n := by
    calc ∑ c, μ.real {c} * hammingDist c d ≤ ∑ c, μ.real {c} * f n := sum_le_sum fun c _ ↦ hterm c
      _ = f n := by rw [← sum_mul, sum_measureReal_singleton, coe_univ, probReal_univ, one_mul]
  have hfn : f n ≤ (1 - δ) / (2 * (1 + exp ε)) * n := (Real.le_norm_self _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have key := hd.trans (mul_le_mul_of_nonneg_left (hexp.trans hfn) hpos.le)
  rw [Fintype.card_fin] at key
  have heq : (1 + exp ε) * ((1 - δ) / (2 * (1 + exp ε)) * n) = n * (1 - δ) / 2 := by
    field_simp
  rw [heq] at key
  nlinarith [mul_pos hn0 (by linarith : (0 : ℝ) < 1 - δ)]

end InformationTheory
