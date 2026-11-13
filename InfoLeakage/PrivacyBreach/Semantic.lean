/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.LocalPrivacy.Basic
public import Mathlib.InformationTheory.Hamming

/-!
# Semantic privacy: a Bayesian formulation of differential privacy

This file formalizes the main definitions and results on pure differential privacy of
S. P. Kasiviswanathan and A. Smith, *On the 'semantics' of differential privacy: a Bayesian
formulation*, J. Privacy and Confidentiality 6(1), 2014,
[arXiv:0803.3946](https://arxiv.org/abs/0803.3946). Numbers refer to arXiv v4 (23 January 2023).

A database `x ∈ D^n` (here `x : ι → D` with a finite index set `ι`, the paper's `ι = Fin n`) is
released through a randomized algorithm `A`, with `A x t` the probability of the transcript `t`.
An adversary with prior belief `b` on databases who sees `t` forms the posterior
`b̄₀[x | t] ∝ A x t b x` (eq. (1)). In the hypothetical Game `i`, entry `i` is replaced by a
default value `d` before `A` is run, giving `x₋ᵢ` and the posterior `b̄ᵢ[x | t] ∝ A x₋ᵢ t b x`
(eq. (2)). The algorithm is `ε`-semantically private if `SD(b̄₀[· | t], b̄ᵢ[· | t]) ≤ ε` for every
prior, every possible transcript and every `i` (Definition 2.1); `(ε, δ)`-semantic privacy only
asks this with probability `≥ 1 - δ` over the transcript (Definition 2.3).

Theorem 2.2 compares semantic privacy with differential privacy (Definitions 1.1 and 1.2, over
databases at Hamming distance at most `1`). We prove its two parts, and the correct form of
Theorem 2.4 (2); Theorem 2.4 (2) as stated is false (see the notes on the paper below), and we
formalize a counterexample.

Transcript alphabets are finite. Algorithms are matrices `A : (ι → D) → T → ℝ` and priors are
vectors `b : (ι → D) → ℝ`, as for `IsLocalDP` and `outputLaw`; the statistical difference `SD` is
`tvDistSum`, which is `max_S |P(S) - Q(S)|` for probability vectors (`isGreatest_tvDistSum`). The
differential privacy of the matrix `A` is `SemanticPrivacy.IsDP A ε δ`; for a kernel `K` it is
`IsEpsDeltaDP K` over the Hamming neighbouring relation (`isEpsDeltaDP_iff_isDP`), and the main
theorems are also stated for kernels.

## Main definitions

* `SemanticPrivacy.posterior b A t`: the Bayes posterior `b̄[· | t]` (eq. (1)).
* `SemanticPrivacy.game A d i`: the algorithm `x ↦ A(x₋ᵢ)` of Game `i`.
* `SemanticPrivacy.PosteriorsClose A d b ε t i`: `b̄ᵢ[· | t]` is defined and
  `SD(b̄₀[· | t], b̄ᵢ[· | t]) ≤ ε`.
* `IsEpsSemanticPrivate A d ε`: `ε`-semantic privacy (Definition 2.1).
* `IsEpsDeltaSemanticPrivate A d ε δ`: `(ε, δ)`-semantic privacy (Definition 2.3).
* `SemanticPrivacy.IsDP A ε δ`: `(ε, δ)`-differential privacy of `A` (Definitions 1.1 and 1.2).

## Main statements

* `isEpsSemanticPrivate_of_isDP`: **Theorem 2.2**, first part, in the sharper form
  `ε`-DP ⇒ `(1 - e^{-ε})`-semantic privacy; `isEpsSemanticPrivate_exp_sub_one_of_isDP` is the
  paper's form `ε`-DP ⇒ `(e^ε - 1)`-semantic privacy.
* `isDP_of_isEpsSemanticPrivate`: **Theorem 2.2**, second part: for `0 ≤ ε ≤ 0.45`,
  `ε/2`-semantic privacy implies `3ε`-DP.
* `isDP_of_isEpsDeltaSemanticPrivate`: one natural repair of **Theorem 2.4 (2)**: for
  `0 ≤ ε ≤ 0.45`, `(ε/2, δ)`-semantic privacy implies `(3ε, 2δ)`-DP.
* `SemanticPrivacy.not_forall_isDP_of_isEpsDeltaSemanticPrivate`: Theorem 2.4 (2) as stated
  (`(ε, δ)`-semantic privacy implies `(3ε, 2δ)`-DP) fails for `ε = 1/5`, `δ = 1/100`;
  `SemanticPrivacy.not_forall_isDP_of_isEpsSemanticPrivate`: the step in the proof of
  Theorem 2.2, read without its (most likely dropped) `/2` ("`ε`-semantic privacy implies
  `3ε`-DP"), fails for `ε = 1/5`. The witness is randomized response
  `SemanticPrivacy.counterexampleRR`, which is `1/5`-semantically private for every default
  value.
* Kernel forms: `isEpsSemanticPrivate_of_isEpsDP`, `isEpsDP_of_isEpsSemanticPrivate`,
  `isEpsDeltaDP_of_isEpsDeltaSemanticPrivate`.

## Correspondence with the paper

* Definitions 1.1 and 1.2: `SemanticPrivacy.IsDP`, and `IsEpsDeltaDP` over
  `hammingDist x y ≤ 1` for kernels (`isEpsDeltaDP_iff_isDP`).
* Eqs. (1) and (2): `SemanticPrivacy.posterior`, `SemanticPrivacy.game`.
* Definition 2.1: `IsEpsSemanticPrivate`; Definition 2.3: `IsEpsDeltaSemanticPrivate`, and
  `IsEpsSemanticPrivate.isEpsDeltaSemanticPrivate`.
* Lemma 3.3 (5), for pointwise `(ε, 0)`-indistinguishable laws, in a sharper one-sided form:
  `SemanticPrivacy.tvDistSum_le_one_sub_exp_neg` (`e^{-ε} P ≤ Q` pointwise gives
  `SD(P, Q) ≤ 1 - e^{-ε} ≤ e^ε - 1`).
* Theorem 2.2: `isEpsSemanticPrivate_of_isDP`, `isEpsSemanticPrivate_exp_sub_one_of_isDP`,
  `isDP_of_isEpsSemanticPrivate`.
* Theorem 2.4 (2): `isDP_of_isEpsDeltaSemanticPrivate` (repaired), and the counterexample
  `SemanticPrivacy.not_forall_isDP_of_isEpsDeltaSemanticPrivate`.

## Implementation notes

* The default value `d` that replaces entry `i` in Game `i` is a parameter of the definitions.
* Definition 2.1 quantifies over "all possible transcripts `t`"; we read this as the transcripts
  of positive probability `∑_x b x A x t > 0` in the real world (Game 0), which is also what
  Definition 2.3 gives for `δ = 0`. The posterior `b̄ᵢ[· | t]` of Game `i` is defined only when
  `t` also has positive probability in Game `i`; `PosteriorsClose` requires this explicitly,
  rather than letting the junk value `x / 0 = 0` decide. This requirement matters. If transcripts
  that are impossible in Game `i` were simply skipped, Theorem 2.2 (2) would fail. For example,
  take `n = 1`, `D = {a, c, d}` with default `d`, `A(c) = A(d) = δ_{t₁}`, and let `A(a)` give `t₁`
  with probability `1 - η` and `t₂` with probability `η`. Then `t₂` is impossible in Game `1`,
  the condition at `t₁` holds with level about `η / 4`, and yet `A` is not `ε`-DP for any `ε`
  (this example is not formalized). For differentially private algorithms the two readings
  coincide, so the choice does not affect Theorem 2.2 (1).
* Definition 2.3 is stated as `P[t ∈ Bad] ≤ δ` for `t ∼ ∑_x b x A x`, where `Bad` is the set of
  transcripts at which some `i` fails `PosteriorsClose`.
* Differential privacy uses neighbouring databases at Hamming distance at most `1`
  (Definition 1.1); `SemanticPrivacy.IsDP` asks the inequality for all sets of transcripts.

## Notes on the paper

References are to arXiv:0803.3946v4. Only that version was checked, not the J. Privacy and
Confidentiality 2014 version.

* **Theorem 2.2, first part (Section 2, p. 4 and Section 3.2, p. 7).** The statement in Section 2
  reads "`ε`-differential privacy implies `ε̄`-semantic privacy, where `ε̄ = e^ε - 1`", while the
  restatement in Section 3.2 and its proof give "`ε/2`-differential privacy implies
  `ε̄`-semantic privacy": the proof bounds the posterior ratio by `e^{±ε}` using `ε/2`-DP and
  applies Lemma 3.3 (5). The Section 2 form is still true, and sharper: `ε`-DP implies
  `(1 - e^{-ε})`-semantic privacy (`isEpsSemanticPrivate_of_isDP`), since the two posteriors are
  tilts of each other by weights in `[e^{-ε}, e^ε]` whose normalizations are within `e^{±ε}`.
* **Theorem 2.2, second part, proof (Section 3.2, eq. (6), p. 7).** This is an internal
  inconsistency in the proof, most likely a dropped "`/2`", not a false theorem. The theorem
  assumes `ε/2`-semantic privacy, but the proof works with `ε`-semantic privacy, so that `b̄₀`
  gives each of the two databases probability in `1/2 ± ε`, and then uses
  `(1/2 + ε) / (1/2 - ε) ≤ e^{3ε}` for `ε ≤ 0.45`. That inequality fails for every
  `0 < ε ≤ 0.45`, since `log ((1 + 2ε) / (1 - 2ε)) = 2 artanh (2ε) > 4ε` (an elementary fact, not
  formalized). The version of the step without the `/2` ("`ε`-semantic privacy implies `3ε`-DP")
  is false: randomized response with probabilities `2/3, 1/3` on a single bit is
  `1/5`-semantically private, for either default value, but not `3/5`-DP
  (`SemanticPrivacy.not_forall_isDP_of_isEpsSemanticPrivate`). With the `/2` restored, the ratio
  is `(1 + ε) / (1 - ε) ≤ e^{3ε}` for `0 ≤ ε ≤ 0.45`, and Theorem 2.2 (2) as stated is true
  (`isDP_of_isEpsSemanticPrivate`).
* **Theorem 2.4 (2) (Section 2, p. 4 and Section 3.4, p. 9).** "If `ε, δ > 0` and `ε ≤ 0.45`,
  then `(ε, δ)`-semantic privacy implies `(3ε, 2δ)`-differential privacy" is **false**: the
  randomized response above is `(1/5, δ)`-semantically private for every `δ ≥ 0` but not
  `(3/5, 1/50)`-DP (`SemanticPrivacy.not_forall_isDP_of_isEpsDeltaSemanticPrivate`,
  `δ = 1/100`). Its proof repeats the step of Theorem 2.2. One natural repair, by analogy with
  Theorem 2.2, puts `(ε/2, δ)`-semantic privacy in the hypothesis
  (`isDP_of_isEpsDeltaSemanticPrivate`). Equivalently, `(ε, δ)`-semantic privacy implies
  `(6ε, 2δ)`-DP for `ε ≤ 0.225`. Unformalized side remark: randomized response on one bit with
  likelihood ratio `e^a` has semantic privacy level exactly `tanh (a / 4)` (for `e^a = 2`, this
  is `3 - 2√2 ≈ 0.17`). So from `ε`-semantic privacy alone, nothing better than
  `4 artanh ε`-DP can follow, and `4 artanh ε > 3ε` for every `ε ∈ (0, 1)`. The counterexamples
  are formalized for `n = 1` only; randomized response on coordinate `0` should give the same
  for every `n`, but that is not formalized.

## Not formalized

Scope: the transcript alphabet `T` and the domain `D` are finite, laws are discrete, and the
algorithm `A` is non-interactive (a fixed matrix). The paper notes that its results extend to the
interactive, continuous case; that extension is not formalized. Also not formalized:
Lemma 3.3 (1)–(4) and the `δ > 0` case of (5), the Conditioning Lemma 3.4, Theorem 2.4 (1),
Section 4 (local semantic privacy, Theorem 4.2, Corollary 4.4) and Appendix B.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory

namespace InformationTheory

variable {ι D T Ω : Type*}

/-! ### Definitions -/

namespace SemanticPrivacy

/-- The posterior belief `b̄[x | t] = b x A x t / ∑_z b z A z t` of an adversary with prior `b`
who sees the transcript `t` of the algorithm `A` (eq. (1) of Kasiviswanathan–Smith). -/
noncomputable def posterior [Fintype Ω] (b : Ω → ℝ) (A : Ω → T → ℝ) (t : T) (x : Ω) : ℝ :=
  b x * A x t / outputLaw b A t

/-- The algorithm `x ↦ A(x₋ᵢ)` of Game `i` of Kasiviswanathan–Smith (Section 2), where `x₋ᵢ` is
`x` with entry `i` replaced by the default value `d`. -/
def game [DecidableEq ι] (A : (ι → D) → T → ℝ) (d : D) (i : ι) : (ι → D) → T → ℝ :=
  fun x ↦ A (Function.update x i d)

/-- At the transcript `t`, the posterior `b̄ᵢ[· | t]` of Game `i` is defined (that is, `t` has
positive probability in Game `i`) and is within statistical difference `ε` of the posterior
`b̄₀[· | t]` of the real world. -/
def PosteriorsClose [Fintype ι] [DecidableEq ι] [Fintype D] (A : (ι → D) → T → ℝ) (d : D)
    (b : (ι → D) → ℝ) (ε : ℝ) (t : T) (i : ι) : Prop :=
  outputLaw b (game A d i) t ≠ 0 ∧ tvDistSum (posterior b A t) (posterior b (game A d i) t) ≤ ε

/-- **`(ε, δ)`-differential privacy** of the algorithm `A` (Definitions 1.1 and 1.2 of
Kasiviswanathan–Smith): for all databases `x, y` at Hamming distance at most `1` and every set `S`
of transcripts, `P[A(x) ∈ S] ≤ e^ε P[A(y) ∈ S] + δ`. Pure `ε`-DP is `δ = 0`. -/
def IsDP [Fintype ι] [DecidableEq D] (A : (ι → D) → T → ℝ) (ε δ : ℝ) : Prop :=
  ∀ x y, hammingDist x y ≤ 1 → ∀ S : Finset T, ∑ t ∈ S, A x t ≤ exp ε * ∑ t ∈ S, A y t + δ

/-- The uniform prior on the two databases `x` and `y`. -/
noncomputable def pairPrior [DecidableEq Ω] (x y : Ω) (z : Ω) : ℝ :=
  (if z = x then 1 / 2 else 0) + (if z = y then 1 / 2 else 0)

end SemanticPrivacy

open SemanticPrivacy

variable [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D]

/-- **`ε`-semantic privacy** (Definition 2.1 of Kasiviswanathan–Smith): for every prior belief `b`
on databases, every transcript `t` of positive probability and every `i`, the posteriors
`b̄₀[· | t]` and `b̄ᵢ[· | t]` of the real world and of Game `i` (with default value `d`) are within
statistical difference `ε`. -/
def IsEpsSemanticPrivate (A : (ι → D) → T → ℝ) (d : D) (ε : ℝ) : Prop :=
  ∀ b : (ι → D) → ℝ, (∀ x, 0 ≤ b x) → ∑ x, b x = 1 → ∀ t, outputLaw b A t ≠ 0 → ∀ i,
    PosteriorsClose A d b ε t i

/-- **`(ε, δ)`-semantic privacy** (Definition 2.3 of Kasiviswanathan–Smith): for every prior
belief `b`, with probability at least `1 - δ` over the transcript `t ∼ A(x)`, `x ∼ b`, the
posteriors `b̄₀[· | t]` and `b̄ᵢ[· | t]` are within statistical difference `ε` for all `i`. -/
def IsEpsDeltaSemanticPrivate [Fintype T] (A : (ι → D) → T → ℝ) (d : D) (ε δ : ℝ) : Prop :=
  ∀ b : (ι → D) → ℝ, (∀ x, 0 ≤ b x) → ∑ x, b x = 1 →
    ∑ t, {t | ∃ i, ¬PosteriorsClose A d b ε t i}.indicator (outputLaw b A) t ≤ δ

/-! ### Basic lemmas -/

namespace SemanticPrivacy

section Posterior

variable [Fintype Ω] {b : Ω → ℝ} {A : Ω → T → ℝ} {t : T}

lemma posterior_nonneg (hb : ∀ x, 0 ≤ b x) (hA : ∀ x t, 0 ≤ A x t) (x : Ω) :
    0 ≤ posterior b A t x :=
  div_nonneg (mul_nonneg (hb x) (hA x t)) (sum_nonneg fun z _ ↦ mul_nonneg (hb z) (hA z t))

/-- The posterior entries sum to one when the denominator `outputLaw b A t` is nonzero. (The
hypotheses allow signed `b` and `A`; for the posterior to be a probability vector, combine with
`posterior_nonneg`.) -/
lemma sum_posterior (h : outputLaw b A t ≠ 0) : ∑ x, posterior b A t x = 1 := by
  simp_rw [posterior, ← sum_div]
  exact div_self h

lemma outputLaw_nonneg (hb : ∀ x, 0 ≤ b x) (hA : ∀ x t, 0 ≤ A x t) (t : T) :
    0 ≤ outputLaw b A t :=
  sum_nonneg fun z _ ↦ mul_nonneg (hb z) (hA z t)

end Posterior

section PairPrior

variable [Fintype Ω] [DecidableEq Ω] {x y : Ω}

omit [Fintype Ω] in
lemma pairPrior_nonneg (x y z : Ω) : 0 ≤ pairPrior x y z := by
  unfold pairPrior; split_ifs <;> norm_num

lemma sum_pairPrior_mul (x y : Ω) (f : Ω → ℝ) : ∑ z, pairPrior x y z * f z = (f x + f y) / 2 := by
  simp only [pairPrior, add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_univ,
    ↓reduceIte]
  ring

lemma sum_pairPrior (x y : Ω) : ∑ z, pairPrior x y z = 1 := by
  simpa using sum_pairPrior_mul x y 1

lemma outputLaw_pairPrior (x y : Ω) (A : Ω → T → ℝ) (t : T) :
    outputLaw (pairPrior x y) A t = (A x t + A y t) / 2 :=
  sum_pairPrior_mul x y (A · t)

omit [Fintype Ω] in
lemma pairPrior_left (hxy : x ≠ y) : pairPrior x y x = 1 / 2 := by
  simp [pairPrior, hxy]

end PairPrior

omit [DecidableEq ι] [Fintype D] in
/-- Pure differential privacy is the pointwise inequality `A x t ≤ e^ε A y t`. -/
lemma isDP_zero_iff {A : (ι → D) → T → ℝ} {ε : ℝ} :
    IsDP A ε 0 ↔ ∀ x y, hammingDist x y ≤ 1 → ∀ t, A x t ≤ exp ε * A y t := by
  refine ⟨fun h x y hxy t ↦ by simpa using h x y hxy {t}, fun h x y hxy S ↦ ?_⟩
  rw [add_zero, mul_sum]
  exact sum_le_sum fun t _ ↦ h x y hxy t

omit [Fintype D] in
/-- Replacing one entry moves a database by Hamming distance at most `1`. -/
lemma hammingDist_update_le (x : ι → D) (i : ι) (d : D) :
    hammingDist x (Function.update x i d) ≤ 1 := by
  refine (card_le_card fun j hj ↦ ?_).trans (card_singleton i).le
  simp only [mem_filter, mem_univ, true_and] at hj
  rw [mem_singleton]
  by_contra h
  exact hj (Function.update_of_ne h d x).symm

omit [Fintype D] in
/-- Two distinct databases at Hamming distance at most `1` differ in a single entry `i`, so they
agree once entry `i` is replaced by `d`. -/
lemma exists_update_eq {x y : ι → D} (hxy : hammingDist x y ≤ 1) (hne : x ≠ y) (d : D) :
    ∃ i, Function.update x i d = Function.update y i d := by
  have h1 : hammingDist x y = 1 := le_antisymm hxy (hammingDist_pos.2 hne)
  obtain ⟨i, hi⟩ := card_eq_one.1 h1
  refine ⟨i, funext fun j ↦ ?_⟩
  by_cases hj : j = i
  · simp [hj]
  · have : j ∉ ({i} : Finset ι) := by simpa using hj
    rw [← hi] at this
    simp only [mem_filter, mem_univ, true_and, not_not] at this
    simp [Function.update_of_ne hj, this]

/-- A sharper, one-sided form of Lemma 3.3 (5) of Kasiviswanathan–Smith for `δ = 0`: if
`e^{-ε} P ≤ Q` pointwise for probability vectors `P, Q`, then `SD(P, Q) ≤ 1 - e^{-ε}`. -/
theorem tvDistSum_le_one_sub_exp_neg [Fintype Ω] {p q : Ω → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1) (hq₁ : ∑ x, q x = 1)
    (h : ∀ x, exp (-ε) * p x ≤ q x) : tvDistSum p q ≤ 1 - exp (-ε) := by
  rw [← sum_max_sub_zero_eq_tvDistSum (hp₁.trans hq₁.symm)]
  have hε' : 0 ≤ 1 - exp (-ε) := sub_nonneg.2 (exp_le_one_iff.2 (by linarith))
  calc ∑ x, max (p x - q x) 0 ≤ ∑ x, (1 - exp (-ε)) * p x :=
        sum_le_sum fun x _ ↦ max_le (by linarith [h x]) (mul_nonneg hε' (hp x))
    _ = 1 - exp (-ε) := by rw [← mul_sum, hp₁, mul_one]

/-- `1 - e^{-ε} ≤ e^ε - 1`. -/
lemma one_sub_exp_neg_le_exp_sub_one (ε : ℝ) : 1 - exp (-ε) ≤ exp ε - 1 := by
  have h := add_one_le_exp (-ε)
  have h' := add_one_le_exp ε
  nlinarith [exp_pos ε, exp_pos (-ε), exp_neg ε, mul_inv_cancel₀ (exp_pos ε).ne']

end SemanticPrivacy

/-! ### Theorem 2.2: differential privacy implies semantic privacy -/

section DPToSemantic

variable {A : (ι → D) → T → ℝ} {ε : ℝ}

/-- **Theorem 2.2**, first part, of Kasiviswanathan–Smith, in a sharper form: an `ε`-differentially
private algorithm is `(1 - e^{-ε})`-semantically private, for any default value `d`. The paper's
form, with `e^ε - 1`, is `isEpsSemanticPrivate_exp_sub_one_of_isDP`. -/
theorem isEpsSemanticPrivate_of_isDP (hε : 0 ≤ ε) (hA : ∀ x t, 0 ≤ A x t) (hDP : IsDP A ε 0)
    (d : D) : IsEpsSemanticPrivate A d (1 - exp (-ε)) := by
  rw [isDP_zero_iff] at hDP
  intro b hb _ t ht i
  have h₁ (x : ι → D) : A x t ≤ exp ε * game A d i x t :=
    hDP _ _ (hammingDist_update_le x i d) t
  have h₂ (x : ι → D) : game A d i x t ≤ exp ε * A x t :=
    hDP _ _ (by rw [hammingDist_comm]; exact hammingDist_update_le x i d) t
  have hG : ∀ x t, 0 ≤ game A d i x t := fun x t ↦ hA _ t
  set u := outputLaw b A t with hu_def
  set v := outputLaw b (game A d i) t with hv_def
  have hu : 0 < u := lt_of_le_of_ne (outputLaw_nonneg hb hA t) (Ne.symm ht)
  have huv : u ≤ exp ε * v := by
    simp only [u, v, outputLaw, mul_sum]
    exact sum_le_sum fun x _ ↦ by nlinarith [h₁ x, hb x]
  have hvu : v ≤ exp ε * u := by
    simp only [u, v, outputLaw, mul_sum]
    exact sum_le_sum fun x _ ↦ by nlinarith [h₂ x, hb x]
  have hv : 0 < v := by
    by_contra! h
    nlinarith [exp_pos ε]
  refine ⟨hv.ne', ?_⟩
  have hP := sum_posterior (A := A) ht
  have hQ := sum_posterior (A := game A d i) hv.ne'
  have key {a c w w' : ℝ} (hw : 0 < w) (hww' : w ≤ w') (ha : 0 ≤ a) (hc : c ≤ exp ε * a)
      {β : ℝ} (hβ : 0 ≤ β) : exp (-ε) * (β * c / w') ≤ β * a / w := by
    have hc' : exp (-ε) * c ≤ a := by
      rw [exp_neg, inv_mul_le_iff₀ (exp_pos ε)]
      exact hc
    calc exp (-ε) * (β * c / w') = β * (exp (-ε) * c) / w' := by ring
      _ ≤ β * a / w' := by gcongr; linarith
      _ ≤ β * a / w := by gcongr
  rcases le_total u v with h | h
  · rw [tvDistSum_comm]
    exact tvDistSum_le_one_sub_exp_neg hε (posterior_nonneg hb hG) hQ hP fun x ↦
      key hu h (hA x t) (h₂ x) (hb x)
  · exact tvDistSum_le_one_sub_exp_neg hε (posterior_nonneg hb hA) hP hQ fun x ↦
      key hv h (hG x t) (h₁ x) (hb x)

/-- **Theorem 2.2**, first part, of Kasiviswanathan–Smith, as stated in Section 2: an
`ε`-differentially private algorithm is `(e^ε - 1)`-semantically private. -/
theorem isEpsSemanticPrivate_exp_sub_one_of_isDP (hε : 0 ≤ ε) (hA : ∀ x t, 0 ≤ A x t)
    (hDP : IsDP A ε 0) (d : D) : IsEpsSemanticPrivate A d (exp ε - 1) :=
  fun b hb hb₁ t ht i ↦ ⟨(isEpsSemanticPrivate_of_isDP hε hA hDP d b hb hb₁ t ht i).1,
    (isEpsSemanticPrivate_of_isDP hε hA hDP d b hb hb₁ t ht i).2.trans
      (one_sub_exp_neg_le_exp_sub_one ε)⟩

end DPToSemantic

/-! ### Theorems 2.2 and 2.4 (2): semantic privacy implies differential privacy -/

section SemanticToDP

variable {A : (ι → D) → T → ℝ} {d : D} {ε δ : ℝ}

omit [DecidableEq D] in
/-- `ε`-semantic privacy implies `(ε, δ)`-semantic privacy for every `δ ≥ 0`. -/
theorem IsEpsSemanticPrivate.isEpsDeltaSemanticPrivate [Fintype T]
    (h : IsEpsSemanticPrivate A d ε) (hδ : 0 ≤ δ) : IsEpsDeltaSemanticPrivate A d ε δ := by
  intro b hb hb₁
  refine (sum_eq_zero fun t _ ↦ ?_).trans_le hδ
  by_cases ht : outputLaw b A t = 0
  · simp [Set.indicator, ht]
  · exact Set.indicator_of_notMem (by simpa using fun i ↦ h b hb hb₁ t ht i) _

namespace SemanticPrivacy

/-- `1 + ε ≤ (1 - ε) e^{3ε}` for `0 ≤ ε ≤ 0.45`, the inequality behind the constant `3` of
Theorem 2.2. -/
lemma one_add_le_one_sub_mul_exp (h₀ : 0 ≤ ε) (h : ε ≤ 9 / 20) :
    1 + ε ≤ (1 - ε) * exp (3 * ε) := by
  have he := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 3 * ε)
  have h₁ : (1 - ε) * (1 + 3 * ε + (3 * ε) ^ 2 / 2) ≤ (1 - ε) * exp (3 * ε) :=
    mul_le_mul_of_nonneg_left he (by linarith)
  nlinarith [mul_nonneg h₀ (mul_nonneg h₀ (by linarith : (0 : ℝ) ≤ 9 / 20 - ε))]

/-- The core of the proofs of Theorems 2.2 and 2.4 (2) of Kasiviswanathan–Smith: for the uniform
prior on two databases `x ≠ y` that agree once entry `i` is replaced, if the posteriors of the
real world and of Game `i` are within `ε / 2` at `t`, then `A x t ≤ e^{3ε} A y t`. -/
lemma le_exp_mul_of_posteriorsClose (hA : ∀ x t, 0 ≤ A x t) {x y : ι → D} (hxy : x ≠ y)
    {i : ι} (hi : Function.update x i d = Function.update y i d) (hε₀ : 0 ≤ ε) (hε : ε ≤ 9 / 20)
    {t : T} (ht : outputLaw (pairPrior x y) A t ≠ 0)
    (h : PosteriorsClose A d (pairPrior x y) (ε / 2) t i) : A x t ≤ exp (3 * ε) * A y t := by
  obtain ⟨hG, hTV⟩ := h
  have hgame : game A d i y t = game A d i x t := by simp [game, hi]
  have hP := sum_posterior ht
  have hQ := sum_posterior hG
  have habs := (abs_sum_sub_sum_le_tvDistSum (hP.trans hQ.symm) {x}).trans hTV
  simp only [sum_singleton, posterior, pairPrior_left hxy, outputLaw_pairPrior, hgame] at habs
  rw [outputLaw_pairPrior, hgame] at hG
  rw [outputLaw_pairPrior] at ht
  have hg : game A d i x t ≠ 0 := by intro h; apply hG; rw [h]; ring
  have hab : 0 < A x t + A y t := lt_of_le_of_ne (by linarith [hA x t, hA y t]) (by
    intro h; apply ht; rw [← h]; ring)
  have e₁ : 1 / 2 * A x t / ((A x t + A y t) / 2) = A x t / (A x t + A y t) := by
    field_simp
  have e₂ : 1 / 2 * game A d i x t / ((game A d i x t + game A d i x t) / 2) = 1 / 2 := by
    field_simp
    ring
  rw [e₁, e₂] at habs
  have h₁ : A x t / (A x t + A y t) ≤ (1 + ε) / 2 := by linarith [(abs_le.1 habs).2]
  rw [div_le_iff₀ hab] at h₁
  have h₂ : (1 - ε) * A x t ≤ (1 + ε) * A y t := by linarith
  have h₃ := mul_le_mul_of_nonneg_right (one_add_le_one_sub_mul_exp hε₀ hε) (hA y t)
  have h₄ : (1 - ε) * A x t ≤ (1 - ε) * (exp (3 * ε) * A y t) := by linarith
  exact le_of_mul_le_mul_left h₄ (by linarith)

end SemanticPrivacy

/-- **Theorem 2.2**, second part, of Kasiviswanathan–Smith: for `0 ≤ ε ≤ 0.45`, an
`ε/2`-semantically private algorithm (for any default value `d`) is `3ε`-differentially private.
The proof uses the uniform prior on two neighbouring databases. -/
theorem isDP_of_isEpsSemanticPrivate (hA : ∀ x t, 0 ≤ A x t) (hε₀ : 0 ≤ ε) (hε : ε ≤ 9 / 20)
    (h : IsEpsSemanticPrivate A d (ε / 2)) : IsDP A (3 * ε) 0 := by
  rw [isDP_zero_iff]
  intro x y hxy t
  by_cases hxy' : x = y
  · subst hxy'
    nlinarith [one_le_exp (by linarith : 0 ≤ 3 * ε), hA x t]
  by_cases h₀ : outputLaw (pairPrior x y) A t = 0
  · rw [outputLaw_pairPrior] at h₀
    have : A x t = 0 := by linarith [hA x t, hA y t]
    rw [this]
    exact mul_nonneg (exp_pos _).le (hA y t)
  obtain ⟨i, hi⟩ := exists_update_eq hxy hxy' d
  exact le_exp_mul_of_posteriorsClose hA hxy' hi hε₀ hε h₀
    (h _ (pairPrior_nonneg x y) (sum_pairPrior x y) t h₀ i)

/-- **Theorem 2.4 (2)** of Kasiviswanathan–Smith, in one natural repaired form: for
`0 ≤ ε ≤ 0.45`, an `(ε/2, δ)`-semantically private algorithm is `(3ε, 2δ)`-differentially
private. Equivalently, `(ε, δ)`-semantic privacy implies `(6ε, 2δ)`-DP for `ε ≤ 0.225`. The paper
states this with `(ε, δ)`-semantic privacy in the hypothesis and `(3ε, 2δ)`-DP in the conclusion,
which is false (`SemanticPrivacy.not_forall_isDP_of_isEpsDeltaSemanticPrivate`). The proof is the
paper's, with the ratio bound of Theorem 2.2. -/
theorem isDP_of_isEpsDeltaSemanticPrivate [Fintype T] (hA : ∀ x t, 0 ≤ A x t) (hε₀ : 0 ≤ ε)
    (hε : ε ≤ 9 / 20) (h : IsEpsDeltaSemanticPrivate A d (ε / 2) δ) :
    IsDP A (3 * ε) (2 * δ) := by
  intro x y hxy S
  have hδ' := h (pairPrior x y) (pairPrior_nonneg x y) (sum_pairPrior x y)
  set B := {t | ∃ i, ¬PosteriorsClose A d (pairPrior x y) (ε / 2) t i}
  have hind (t : T) : 0 ≤ B.indicator (outputLaw (pairPrior x y) A) t :=
    Set.indicator_nonneg (fun t _ ↦ outputLaw_nonneg (pairPrior_nonneg x y) hA t) t
  have key (t : T) :
      A x t ≤ exp (3 * ε) * A y t + 2 * B.indicator (outputLaw (pairPrior x y) A) t := by
    by_cases hxy' : x = y
    · subst hxy'
      nlinarith [one_le_exp (by linarith : 0 ≤ 3 * ε), hA x t, hind t]
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht, outputLaw_pairPrior]
      nlinarith [exp_pos (3 * ε), hA y t, hA x t]
    rw [Set.indicator_of_notMem ht, mul_zero, add_zero]
    by_cases h₀ : outputLaw (pairPrior x y) A t = 0
    · rw [outputLaw_pairPrior] at h₀
      have : A x t = 0 := by linarith [hA x t, hA y t]
      rw [this]
      exact mul_nonneg (exp_pos _).le (hA y t)
    obtain ⟨i, hi⟩ := exists_update_eq hxy hxy' d
    simp only [B, Set.mem_ofPred_eq, not_exists, not_not] at ht
    exact le_exp_mul_of_posteriorsClose hA hxy' hi hε₀ hε h₀ (ht i)
  calc ∑ t ∈ S, A x t
      ≤ ∑ t ∈ S, (exp (3 * ε) * A y t + 2 * B.indicator (outputLaw (pairPrior x y) A) t) :=
        sum_le_sum fun t _ ↦ key t
    _ = exp (3 * ε) * ∑ t ∈ S, A y t +
          2 * ∑ t ∈ S, B.indicator (outputLaw (pairPrior x y) A) t := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ exp (3 * ε) * ∑ t ∈ S, A y t + 2 * δ := by
        gcongr
        exact (sum_le_sum_of_subset_of_nonneg (subset_univ S) fun t _ _ ↦ hind t).trans hδ'

end SemanticToDP

/-! ### Kernels: `IsEpsDeltaDP` over the Hamming relation -/

section Kernel

variable [MeasurableSpace D] [MeasurableSpace T] [MeasurableSingletonClass T]
  {K : Kernel (ι → D) T} [IsFiniteKernel K] {d : D} {ε δ : ℝ}

omit [DecidableEq ι] [Fintype D] in
/-- For a kernel with a finite transcript alphabet, `(ε, δ)`-differential privacy
`IsEpsDeltaDP` over databases at Hamming distance at most `1` is `SemanticPrivacy.IsDP` of the
matrix of its transcript probabilities. -/
theorem isEpsDeltaDP_iff_isDP [Finite T] :
    IsEpsDeltaDP K (fun x y ↦ hammingDist x y ≤ 1) ε δ ↔ IsDP (fun x t ↦ (K x).real {t}) ε δ := by
  classical
  have := Fintype.ofFinite T
  refine ⟨fun h x y hxy S ↦ ?_, fun h x y hxy E ↦ ?_⟩
  · simpa [sum_measureReal_singleton] using h hxy (S : Set T)
  · simpa [sum_measureReal_singleton, Set.coe_toFinset] using h x y hxy E.toFinset

/-- **Theorem 2.2**, first part, of Kasiviswanathan–Smith for kernels, in the sharper form: an
`ε`-DP kernel (over the Hamming relation) is `(1 - e^{-ε})`-semantically private. -/
theorem isEpsSemanticPrivate_of_isEpsDP [Finite T] (hε : 0 ≤ ε)
    (hK : IsEpsDP K (fun x y ↦ hammingDist x y ≤ 1) ε) (d : D) :
    IsEpsSemanticPrivate (fun x t ↦ (K x).real {t}) d (1 - exp (-ε)) :=
  isEpsSemanticPrivate_of_isDP hε (fun _ _ ↦ measureReal_nonneg) (isEpsDeltaDP_iff_isDP.1 hK) d

/-- **Theorem 2.2**, second part, of Kasiviswanathan–Smith for kernels: for `0 ≤ ε ≤ 0.45`, an
`ε/2`-semantically private kernel is `3ε`-DP over the Hamming relation. -/
theorem isEpsDP_of_isEpsSemanticPrivate [Finite T] (hε₀ : 0 ≤ ε) (hε : ε ≤ 9 / 20)
    (h : IsEpsSemanticPrivate (fun x t ↦ (K x).real {t}) d (ε / 2)) :
    IsEpsDP K (fun x y ↦ hammingDist x y ≤ 1) (3 * ε) :=
  isEpsDeltaDP_iff_isDP.2 (isDP_of_isEpsSemanticPrivate (fun _ _ ↦ measureReal_nonneg) hε₀ hε h)

/-- Repaired **Theorem 2.4 (2)** of Kasiviswanathan–Smith for kernels: for `0 ≤ ε ≤ 0.45`, an
`(ε/2, δ)`-semantically private kernel is `(3ε, 2δ)`-DP over the Hamming relation. -/
theorem isEpsDeltaDP_of_isEpsDeltaSemanticPrivate [Fintype T] (hε₀ : 0 ≤ ε) (hε : ε ≤ 9 / 20)
    (h : IsEpsDeltaSemanticPrivate (fun x t ↦ (K x).real {t}) d (ε / 2) δ) :
    IsEpsDeltaDP K (fun x y ↦ hammingDist x y ≤ 1) (3 * ε) (2 * δ) :=
  isEpsDeltaDP_iff_isDP.2
    (isDP_of_isEpsDeltaSemanticPrivate (fun _ _ ↦ measureReal_nonneg) hε₀ hε h)

end Kernel

/-! ### A counterexample to Theorem 2.4 (2) as stated -/

namespace SemanticPrivacy

/-- Randomized response on a database made of a single bit: the transcript is the bit with
probability `2/3` and its negation with probability `1/3`. -/
noncomputable def counterexampleRR (x : Fin 1 → Bool) (t : Bool) : ℝ :=
  if t = x 0 then 2 / 3 else 1 / 3

private lemma sum_fin_one_bool (f : (Fin 1 → Bool) → ℝ) :
    ∑ x, f x = f (fun _ ↦ true) + f (fun _ ↦ false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  rfl

private lemma tvDistSum_two_point_le {q r a a' : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r = 1)
    (ha : a = 2 / 3 ∧ a' = 3⁻¹ ∨ a = 3⁻¹ ∧ a' = 2 / 3) :
    (|q * a / (q * a + r * a') - q| + |r * a' / (q * a + r * a') - r|) / 2 ≤ 5⁻¹ := by
  have hW : 0 < q * a + r * a' := by rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith
  rw [div_sub' hW.ne', div_sub' hW.ne', abs_div, abs_div, abs_of_pos hW,
    show q * a - (q * a + r * a') * q = q * r * (a - a') by linear_combination (-q * a) * hqr,
    show r * a' - (q * a + r * a') * r = -(q * r * (a - a')) by
      linear_combination (-r * a') * hqr,
    abs_neg, ← add_div, div_div, div_le_iff₀ (by positivity)]
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (q - 2 / 5)]
  · rw [abs_of_nonpos (by nlinarith)]
    nlinarith [sq_nonneg (r - 2 / 5)]

/-- Randomized response with probabilities `2/3, 1/3` on one bit is `1/5`-semantically private,
for either default value. -/
theorem isEpsSemanticPrivate_counterexampleRR (d : Bool) :
    IsEpsSemanticPrivate counterexampleRR d (1 / 5) := by
  intro b hb hb₁ t _ i
  have hupd (x : Fin 1 → Bool) : Function.update x i d = fun _ ↦ d :=
    funext fun j ↦ by rw [Subsingleton.elim j i]; simp
  have hgame : game counterexampleRR d i = fun _ t ↦ counterexampleRR (fun _ ↦ d) t := by
    funext x t
    simp [game, hupd]
  have hc : 0 < counterexampleRR (fun _ ↦ d) t := by
    simp only [counterexampleRR]; split_ifs <;> norm_num
  have hout : outputLaw b (game counterexampleRR d i) t = counterexampleRR (fun _ ↦ d) t := by
    rw [hgame, outputLaw, ← sum_mul, hb₁, one_mul]
  refine ⟨by rw [hout]; exact hc.ne', ?_⟩
  have hpost : posterior b (game counterexampleRR d i) t = b := by
    funext x
    rw [posterior, hout, hgame]
    field_simp
  rw [hpost]
  rw [sum_fin_one_bool] at hb₁
  have hq := hb (fun _ ↦ true)
  have hr := hb (fun _ ↦ false)
  simp only [tvDistSum, posterior, outputLaw, sum_fin_one_bool, counterexampleRR]
  cases t <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, one_div, ge_iff_le]
  · exact tvDistSum_two_point_le hq hr hb₁ (Or.inr ⟨rfl, rfl⟩)
  · exact tvDistSum_two_point_le hq hr hb₁ (Or.inl ⟨rfl, rfl⟩)

private lemma exp_three_fifths_lt : exp (3 / 5) < 19 / 10 := by
  have h₁ : exp (3 / 5) ^ 5 = exp 1 ^ 3 := by
    rw [← exp_nat_mul, ← exp_nat_mul]
    norm_num
  have h₂ : exp 1 ^ 3 < 2.7182818286 ^ 3 :=
    pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)
  by_contra! h
  have h₃ := pow_le_pow_left₀ (by norm_num) h 5
  rw [h₁] at h₃
  norm_num at h₂ h₃
  linarith

/-- Randomized response with probabilities `2/3, 1/3` on one bit is not `(3/5, 1/50)`-DP. -/
theorem not_isDP_counterexampleRR : ¬IsDP counterexampleRR (3 / 5) (1 / 50) := by
  intro h
  have := h (fun _ ↦ true) (fun _ ↦ false) (hammingDist_le_card_fintype.trans (by simp)) {true}
  simp only [sum_singleton, counterexampleRR, ↓reduceIte] at this
  norm_num at this
  linarith [exp_three_fifths_lt]

/-- **Counterexample to Theorem 2.4 (2)** of Kasiviswanathan–Smith as stated ("if `ε, δ > 0` and
`ε ≤ 0.45`, then `(ε, δ)`-semantic privacy implies `(3ε, 2δ)`-differential privacy"): it fails
for `n = 1`, `D = Bool`, Boolean transcripts, `ε = 1/5` and `δ = 1/100`, with randomized response
`counterexampleRR`. -/
theorem not_forall_isDP_of_isEpsDeltaSemanticPrivate :
    ¬∀ (A : (Fin 1 → Bool) → Bool → ℝ) (d : Bool) (ε δ : ℝ), 0 < ε → 0 < δ → ε ≤ 9 / 20 →
      (∀ x t, 0 ≤ A x t) → (∀ x, ∑ t, A x t = 1) → IsEpsDeltaSemanticPrivate A d ε δ →
        IsDP A (3 * ε) (2 * δ) := by
  intro h
  refine not_isDP_counterexampleRR ?_
  convert h counterexampleRR false (1 / 5) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (fun x t ↦ by simp only [counterexampleRR]; split_ifs <;> norm_num)
    (fun x ↦ by simp only [counterexampleRR, Fintype.sum_bool]; cases x 0 <;> norm_num)
    ((isEpsSemanticPrivate_counterexampleRR false).isEpsDeltaSemanticPrivate (by norm_num))
    using 2 <;> norm_num

/-- The proof of Theorem 2.2 of Kasiviswanathan–Smith (Section 3.2, eq. (6)) is internally
inconsistent, most likely because of a dropped "`/2`". It works with `ε`-semantic privacy, while
the theorem assumes `ε/2`-semantic privacy. This shows that the step cannot be read without the
`/2`: "`ε`-semantic privacy implies `3ε`-DP for `ε ≤ 0.45`" fails for `n = 1`, `D = Bool`,
Boolean transcripts and `ε = 1/5`. Theorem 2.2 itself, with `ε/2`, is true
(`isDP_of_isEpsSemanticPrivate`). -/
theorem not_forall_isDP_of_isEpsSemanticPrivate :
    ¬∀ (A : (Fin 1 → Bool) → Bool → ℝ) (d : Bool) (ε : ℝ), 0 < ε → ε ≤ 9 / 20 →
      (∀ x t, 0 ≤ A x t) → (∀ x, ∑ t, A x t = 1) → IsEpsSemanticPrivate A d ε →
        IsDP A (3 * ε) 0 := by
  intro h
  refine not_isDP_counterexampleRR ?_
  have h' := h counterexampleRR false (1 / 5) (by norm_num) (by norm_num)
    (fun x t ↦ by simp only [counterexampleRR]; split_ifs <;> norm_num)
    (fun x ↦ by simp only [counterexampleRR, Fintype.sum_bool]; cases x 0 <;> norm_num)
    (isEpsSemanticPrivate_counterexampleRR false)
  intro x y hxy S
  have := h' x y hxy S
  norm_num at this ⊢
  linarith

end SemanticPrivacy

end InformationTheory
