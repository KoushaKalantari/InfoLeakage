/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.FInformation.Basic
public import InfoLeakage.LocalPrivacy.Basic
public import InfoLeakage.PerfectSecrecy.Basic
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Fundamental limits of perfect privacy

This file formalizes the characterization of perfect privacy by the smallest principal inertia
component from

* F. P. Calmon, A. Makhdoumi, M. Médard, *Fundamental limits of perfect privacy*, Proc. IEEE
  ISIT 2015, pp. 1796–1800, doi:10.1109/ISIT.2015.7282765 (not on arXiv; numbering refers to the
  author's final manuscript, MIT DSpace hdl:1721.1/113672);
* F. P. Calmon, A. Makhdoumi, M. Médard, M. Varia, M. Christiansen, K. R. Duffy, *Principal
  inertia components and applications*, IEEE Trans. Inf. Theory 63(8), 2017,
  [arXiv:1704.00820](https://arxiv.org/abs/1704.00820) (v1), Section 5, which reproduces the
  ISIT paper; its numbering is given in brackets below.

A private variable `S` and a useful variable `X` have a joint law `p_{S,X}` on finite alphabets.
A *privacy-assuring mapping* `p_{Y|X}` releases `Y`, so that `S → X → Y`. Perfect privacy is
`I(S; Y) = 0`, and the utility is `I(X; Y)`. With `Q = D_S^{-1/2} P_{S,X} D_X^{-1/2}`, the
principal inertia components (PICs) of `p_{S,X}` are the squared singular values of `Q` other
than the largest one, and `δ(p_{S,X})` is the smallest PIC if `|𝓧| ≤ |𝓢|` and `0` otherwise.
The headline result (Theorem 3 [Theorem 10]) is that perfect privacy is achievable with
non-trivial utility `I(X; Y) > 0` if and only if `δ(p_{S,X}) = 0`.

## Main definitions

* `inertiaMatrix μ`: the matrix `Q = D_S^{-1/2} P_{S,X} D_X^{-1/2}` of a joint law `μ`.
* `principalInertia μ k`: `σ_k(Q)²`, the `k`-th PIC for `1 ≤ k < min {|𝓢|, |𝓧|}`.
* `smallestPIC μ`, `privacyDelta μ`: the smallest PIC and the coefficient `δ(p_{S,X})`.
* `perfectPrivacyMapping f y₀ y₁`: the binary privacy-assuring mapping of the proof of Theorem 3,
  `P(Y = y₁ | X = x) = 1/2 + f(x) / (2 ‖f‖_∞)`.
* `privacyFunnel π κ t`: the privacy funnel `G_I(t, p_{S,X})`.

## Main statements

* `exists_perfectPrivacy_iff`: the first clause of **Theorem 3** [Theorem 10]: for an output
  alphabet with at least two letters, some privacy-assuring mapping has `I(S; Y) = 0` and
  `I(X; Y) > 0` if and only if `δ(p_{S,X}) = 0`; `exists_fin_perfectPrivacy_iff` is the statement
  with "some finite output alphabet" as in the paper.
* `exists_dependence_eq_zero_and_pos_iff`: **Corollary 1** [Corollary 7], the same for any
  dependence measures vanishing exactly on product laws.
* `privacyDelta_eq_zero_iff_not_injective`, `privacyDelta_compProd_eq_zero_iff`: `δ(p_{S,X}) = 0`
  iff `Q` is not injective iff some nonzero `f` has `E[f(X) | S] = 0`.
* `privacyDelta_mul_le`, `exists_privacyDelta_eq`: **Lemma 5** [Lemma 13],
  `δ(p_{S,X}) = min {‖E[f(X) | S]‖₂² | E[f(X)] = 0, ‖f(X)‖₂ = 1}` (for `|𝓧| ≥ 2`).
* `principalInertia_zero`: the largest singular value of `Q` is `1`.
* `mutualInfo_perfectPrivacyMapping`: the utility (19) [(71)] of the mapping of Theorem 3.
* `privacyFunnel_eq_zero_of_le`: the first claim of **Corollary 2** [Corollary 8] (in its
  corrected form, see the notes below), and `exists_pos_privacyFunnel_eq_zero`: the "if" part of
  (18) [(70)].

## Paper results and their Lean names

* Definition 1 [Definition 12] → `privacyFunnel`.
* Definition 3, (7) [Definition 2, Theorem 1 (4), Definition 14] → `inertiaMatrix`,
  `principalInertia`, `smallestPIC`, `privacyDelta`; "the largest singular value of `Q` is 1" →
  `principalInertia_zero`; the observation that `δ(p_{S,X})` is the smallest eigenvalue
  `σ_{|𝓧|-1}(Q)²` of `QᵀQ` → `privacyDelta_eq_principalInertia`.
* Lemma 5 [Lemma 13] → `privacyDelta_mul_le` (lower bound) and `exists_privacyDelta_eq`
  (attainment, for `|𝓧| ≥ 2`, where the constraint set is nonempty).
* Discussion before Theorem 3 ("`Q`, and consequently `P_{S|X}`, is either not full rank or has
  more columns than rows") → `privacyDelta_eq_zero_iff_not_injective`,
  `privacyDelta_eq_zero_of_card_lt`, `privacyDelta_eq_zero_iff_exists`,
  `privacyDelta_compProd_eq_zero_iff`.
* Theorem 3 [Theorem 10], first clause (existence of `p_{Y|X}` with `I(X; Y) > 0` and
  `I(S; Y) = 0` iff `δ(p_{S,X}) = 0`) → `exists_perfectPrivacy_iff`,
  `exists_fin_perfectPrivacy_iff`, `exists_compProd_eq_prod_and_ne_prod_iff` (independence form);
  the equivalence with `v*(p_{S,X}) = 0` and the "only if" part of (18) [(70)] are not formalized;
  the "only if" part of the first clause for every
  countable output alphabet → `privacyDelta_eq_zero_of_compProd_eq_prod`; the construction of the
  proof → `perfectPrivacyMapping`, `perfectPrivacyMapping_comp_eq_const`,
  `compProd_comp_perfectPrivacyMapping_eq_prod`, `compProd_perfectPrivacyMapping_ne_prod`;
  (19) [(71)] → `mutualInfo_perfectPrivacyMapping`, `PerfectPrivacy.sum_binEntropy_lt_log_two`;
  (18) [(70)], "if" part → `exists_pos_privacyFunnel_eq_zero`.
* Remark after Theorem 3 ("if `|𝓧| > |𝓢|` ... perfect privacy while disclosing some useful
  information") → `exists_perfectPrivacy_of_card_lt`.
* Corollary 1 [Corollary 7] → `exists_dependence_eq_zero_and_pos_iff`.
* Corollary 2 [Corollary 8], first claim, corrected → `privacyFunnel_eq_zero_of_le` (the
  sharpness claim is not formalized).
* [Footnote 8], corrected → `exists_perfectPrivacy_iff_compProd_eq_prod_of_card_eq_two`.

## Implementation notes

* The private variable has law `π` on `𝓢` and `κ : Kernel 𝓢 𝓧` is `p_{X|S}`, so
  `p_{S,X} = π ⊗ₘ κ` and `p_X = κ ∘ₘ π`; every joint law on finite alphabets is of this form. A
  privacy-assuring mapping is a Markov kernel `W : Kernel 𝓧 𝓨`. The Markov chain `S → X → Y` is
  built in: the law of `(S, Y)` is `π ⊗ₘ (W ∘ₖ κ)` and that of `(X, Y)` is `(κ ∘ₘ π) ⊗ₘ W`.
  Mutual information is Statlib's `mutualInfo`, in nats, so the paper's `1 - E[h_b(⋯)]` (bits)
  becomes `log 2 - E[h(⋯)]` with Mathlib's `Real.binEntropy`.
* As in the paper ("`D_X` being invertible (by definition)"), both marginals are assumed to have
  full support: `π {s} ≠ 0` and `(κ ∘ₘ π) {x} ≠ 0`. Without them `Q` is not defined in the paper.
* Singular values are Mathlib's `LinearMap.singularValues` of `Q` as a map
  `EuclideanSpace ℝ 𝓧 → EuclideanSpace ℝ 𝓢`: zero-indexed, sorted, padded with zeros. The paper's
  `σ_k(Q)`, `1 ≤ k ≤ m - 1`, is the Mathlib value at `k`, the value at `0` being the largest
  singular value, which is `1` (`principalInertia_zero`). For `|𝓧| = 1` the paper's `δ` is
  undefined (there is no PIC); `privacyDelta` is then `σ_0(Q)² = 1`, and the theorems hold as
  stated in that case too.
* The "only if" part of Theorem 3 is proved directly rather than through Theorem 2 (which uses
  the divergence characterization of Lemma 4 and Pinsker's inequality): if `Y ⊥ S` but `Y` is not
  independent of `X`, then `f(x) = P(Y = y | X = x) - P(Y = y)` is, for a suitable `y`, a nonzero
  function with `E[f(X) | S] = 0`.
* The paper's privacy-assuring mappings have a finite output alphabet. `exists_perfectPrivacy_iff`
  fixes the output alphabet `𝓨` (any countable alphabet with at least two letters, which is
  necessary since `I(X; Y) = 0` for a constant `Y`); `exists_fin_perfectPrivacy_iff` and
  `privacyFunnel` range over the output alphabets `Fin n`, which represent all finite alphabets.

## Notes on the paper

* ISIT 2015, Section V, Corollary 2, (20) [T-IT, Corollary 8, (72), p. 30]: the bound
  `t* ≥ 1 - max_{f ∈ F₀} E[h_b(1/2 + f(X) / (2‖f‖_∞))]` should read `min` instead of `max`.
  `F₀` contains the trivial function `f₀ = 0`, for which the term `f₀(X) / (2‖f₀‖_∞)` is
  literally `0 / 0`, so the printed right-hand side is undefined as written. Under the extension
  reading `0 / 0` as `0` (as Lean does), the expectation for `f₀` is `h_b(1/2) = 1`, and
  `h_b ≤ 1`, so the right-hand side is `0` and the printed bound is vacuous; its vacuity thus
  depends on that zero-function extension. Even with `f₀` excluded, `max` gives a weaker bound
  than the proof provides. The construction of
  Theorem 3 gives `G_I(t, p_{S,X}) = 0` for `t ≤ 1 - E[h_b(⋯)]` for *every* `f ∈ F₀`, which is
  the bound with `min`. The printed inequality is still true (it is weaker); the corrected one is
  `privacyFunnel_eq_zero_of_le`.
* ISIT 2015, Section II, Lemma 3, (3): the lower bound `min {t - H(X|S), 0} ≤ G_I(t, p_{S,X})`
  should read `max`, as in [T-IT, Lemma 11, (61)]; with `min` the bound is trivial (its left-hand
  side is `≤ 0`), although the text calls it sharp. The printed inequality is still true. This
  lemma is not formalized here.
* [T-IT, footnote 8, p. 28, attached to Lemma 15]: "If `S` is binary, then (69) implies that
  perfect privacy is achievable iff `S` and `X` are independent (since `δ(p_{S,X}) = ρ_m(S;X)²`)"
  is false for `|𝓧| ≥ 3`: then `δ(p_{S,X}) = 0` by Definition 14 whatever the dependence. For
  instance, `S` uniform on `{1, 2}`, `p_{X|S=1} = (1/2, 1/2, 0)`, `p_{X|S=2} = (0, 1/2, 1/2)` and
  `Y = 1{X ≠ 2}` give `Y ⊥ S` and `I(X; Y) = 1` bit although `S` and `X` are dependent
  (`exists_perfectPrivacy_of_card_lt`). Up to relabeling, this is the paper's own example for the
  sharpness of Corollary 2 [Corollary 8] (ISIT 2015, Appendix F: `X` is `S` sent through an
  erasure channel with erasure probability `1/2`). The claim holds for a binary *useful* variable
  `X`: `exists_perfectPrivacy_iff_compProd_eq_prod_of_card_eq_two`; the identity
  `δ(p_{S,X}) = ρ_m(S;X)²` for binary `X` is not formalized (maximal correlation is not defined
  here). The result the footnote says it recovers, [61, Thm. 2] (Asoodeh–Alajaji–Linder, Allerton
  2014), concerns a binary observable, which is consistent with the corrected binary-`X` form;
  this was not checked against [61].
* ISIT 2015, Section IV, Corollary 1: the measure `J` is introduced, but the conclusion is printed
  with mutual information, "`I(X; Y) > 0` and `I(S; Y) = 0`"; it should read `J(X; Y) > 0` and
  `J(S; Y) = 0`, as in `exists_dependence_eq_zero_and_pos_iff`.
* Cross-references: after the proof of Theorem 3, "the value of `t₀` in (10)" should be "(18)"
  (ISIT 2015, Section IV), and "the value of `t₀` in (100)" should be "(70)" [T-IT, p. 29].

## Not formalized

* Lemmas 1–4 [Lemmas 10–12] (the cardinality bound and convexity of the privacy funnel,
  its bounds, the divergence characterization of `v*`), Theorems 1 and 2 [Lemmas 14 and 15] on the
  optimal privacy-utility coefficient `v*` (hence the clause "equivalently `v*(p_{S,X}) = 0`" of
  Theorem 3), and Proposition 1 [Proposition 1] (tensorization).
* The "only if" part of (18) [(70)], which needs Theorem 2 or the attainment of the infimum in the
  privacy funnel (Lemma 1); the sharpness claim of Corollary 2 [Corollary 8], which needs the
  lower bound of Lemma 3 and entropy computations; the identity `δ(p_{S,X}) = ρ_m(S;X)²` of
  [footnote 8].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {𝓢 𝓧 𝓨 : Type*} [MeasurableSpace 𝓢] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

private lemma measureReal_pos_of_ne_zero {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {a : α} (h : ν {a} ≠ 0) : 0 < ν.real {a} :=
  ENNReal.toReal_pos h (measure_ne_top _ _)

/-! ### The principal inertia components and the coefficient `δ` -/

section PIC

/-- The matrix `Q = D_S^{-1/2} P_{S,X} D_X^{-1/2}` of a joint law `μ = p_{S,X}` on `𝓢 × 𝓧`
(Calmon–Makhdoumi–Médard, Definition 3 [T-IT, Definition 2, (14)]), with entries
`p_{S,X}(s, x) / √(p_S(s) p_X(x))`. -/
noncomputable def inertiaMatrix (μ : Measure (𝓢 × 𝓧)) : Matrix 𝓢 𝓧 ℝ :=
  Matrix.of fun s x ↦ μ.real {(s, x)} / (√(μ.fst.real {s}) * √(μ.snd.real {x}))

variable [Fintype 𝓢] [Fintype 𝓧] [DecidableEq 𝓧]

/-- The `k`-th principal inertia component `λ_k(S; X) = σ_k(Q)²` of a joint law, where
`σ_0(Q) ≥ σ_1(Q) ≥ ⋯` are the singular values of `Q = inertiaMatrix μ` (Mathlib's
`LinearMap.singularValues`, zero-indexed and padded with zeros). In the paper the largest
singular value `σ_0(Q) = 1` is not counted, and the principal inertia components are
`λ_1, …, λ_{m-1}`, `m = min {|𝓢|, |𝓧|}` (Calmon–Makhdoumi–Médard, Definition 3 [T-IT,
Theorem 1 (4)]). -/
noncomputable def principalInertia (μ : Measure (𝓢 × 𝓧)) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin (inertiaMatrix μ)).singularValues k ^ 2

/-- The smallest principal inertia component `σ_{m-1}(Q)²`, `m = min {|𝓢|, |𝓧|}`, of a joint
law (Calmon–Makhdoumi–Médard, Definition 3 [T-IT, `λ_d(S; X)`, `d = m - 1`]). -/
noncomputable def smallestPIC (μ : Measure (𝓢 × 𝓧)) : ℝ :=
  principalInertia μ (min (Fintype.card 𝓢) (Fintype.card 𝓧) - 1)

/-- The coefficient `δ(p_{S,X})` of Calmon–Makhdoumi–Médard (Definition 3, (7) [T-IT,
Definition 14, (65)]): the smallest principal inertia component if `|𝓧| ≤ |𝓢|`, and `0`
otherwise. -/
noncomputable def privacyDelta (μ : Measure (𝓢 × 𝓧)) : ℝ :=
  if Fintype.card 𝓧 ≤ Fintype.card 𝓢 then smallestPIC μ else 0

variable {μ : Measure (𝓢 × 𝓧)}

lemma principalInertia_nonneg (k : ℕ) : 0 ≤ principalInertia μ k := sq_nonneg _

lemma privacyDelta_nonneg : 0 ≤ privacyDelta μ := by
  unfold privacyDelta
  split_ifs
  exacts [principalInertia_nonneg _, le_rfl]

/-- `δ(p_{S,X})` is the square of the `|𝓧|`-th largest singular value `σ_{|𝓧|-1}(Q)` of `Q`,
whatever the sizes of the alphabets: if `|𝓧| > |𝓢|`, this singular value vanishes since `Q` has
rank at most `|𝓢|`. -/
lemma privacyDelta_eq_principalInertia :
    privacyDelta μ = principalInertia μ (Fintype.card 𝓧 - 1) := by
  unfold privacyDelta smallestPIC
  split_ifs with h
  · rw [min_eq_right h]
  · rw [principalInertia, eq_comm, sq_eq_zero_iff,
      LinearMap.singularValues_eq_zero_iff_le_finrank_range]
    calc Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin (inertiaMatrix μ)))
        ≤ Module.finrank ℝ (EuclideanSpace ℝ 𝓢) := Submodule.finrank_le _
      _ = Fintype.card 𝓢 := finrank_euclideanSpace
      _ ≤ Fintype.card 𝓧 - 1 := by omega

/-- If `|𝓧| > |𝓢|`, then `δ(p_{S,X}) = 0` (by definition). -/
lemma privacyDelta_eq_zero_of_card_lt (h : Fintype.card 𝓢 < Fintype.card 𝓧) :
    privacyDelta μ = 0 := by
  unfold privacyDelta
  split_ifs <;> first | omega | rfl

/-- `δ(p_{S,X}) = 0` if and only if `Q` is not injective, that is, `Q` (equivalently the
`|𝓢| × |𝓧|` matrix `P_{S|X}`) is not of full rank or has more columns than rows
(Calmon–Makhdoumi–Médard, discussion before Theorem 3). -/
theorem privacyDelta_eq_zero_iff_not_injective [Nonempty 𝓧] :
    privacyDelta μ = 0 ↔ ¬ Function.Injective (Matrix.toEuclideanLin (inertiaMatrix μ)) := by
  set T := Matrix.toEuclideanLin (inertiaMatrix μ)
  have hn : 0 < Fintype.card 𝓧 := Fintype.card_pos
  rw [privacyDelta_eq_principalInertia, principalInertia, sq_eq_zero_iff,
    T.injective_iff_forall_lt_finrank_singularValues_pos, finrank_euclideanSpace]
  constructor
  · intro h0 hpos
    exact (hpos _ (by omega)).ne' h0
  · intro h
    by_contra h0
    refine h fun i hi ↦ ?_
    have hle := T.singularValues_antitone (show i ≤ Fintype.card 𝓧 - 1 by omega)
    exact lt_of_lt_of_le
      ((T.singularValues_pos_iff_ne_zero _).2 h0) hle

omit [Fintype 𝓢] [DecidableEq 𝓧] in
private lemma inertiaMatrix_mulVec_apply (y : 𝓧 → ℝ) (s : 𝓢) : (inertiaMatrix μ).mulVec y s =
    (√(μ.fst.real {s}))⁻¹ * ∑ x, μ.real {(s, x)} * (y x / √(μ.snd.real {x})) := by
  simp only [Matrix.mulVec, dotProduct, inertiaMatrix, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  field_simp

/-- Under full support of both marginals, `δ(p_{S,X}) = 0` if and only if some nonzero
`f : 𝓧 → ℝ` satisfies `∑_x p_{S,X}(s, x) f(x) = 0`, that is `E[f(X) | S = s] = 0`, for every `s`
(Calmon–Makhdoumi–Médard, Lemma 5 and the discussion before Theorem 3). -/
theorem privacyDelta_eq_zero_iff_exists [IsProbabilityMeasure μ] (hS : ∀ s, μ.fst {s} ≠ 0)
    (hX : ∀ x, μ.snd {x} ≠ 0) :
    privacyDelta μ = 0 ↔ ∃ f : 𝓧 → ℝ, f ≠ 0 ∧ ∀ s, ∑ x, μ.real {(s, x)} * f x = 0 := by
  have : Nonempty 𝓧 := (nonempty_of_isProbabilityMeasure μ).map Prod.snd
  have hpS (s : 𝓢) : 0 < √(μ.fst.real {s}) := Real.sqrt_pos.2 (measureReal_pos_of_ne_zero (hS s))
  have hpX (x : 𝓧) : 0 < √(μ.snd.real {x}) := Real.sqrt_pos.2 (measureReal_pos_of_ne_zero (hX x))
  rw [privacyDelta_eq_zero_iff_not_injective, injective_iff_map_eq_zero]
  push Not
  constructor
  · rintro ⟨v, hv, hv0⟩
    refine ⟨fun x ↦ v.ofLp x / √(μ.snd.real {x}), fun hf ↦ hv0 ?_, fun s ↦ ?_⟩
    · ext x
      have := congrFun hf x
      simp only [Pi.zero_apply, div_eq_zero_iff, (hpX x).ne', or_false] at this
      simpa using this
    · have := congrFun (congrArg WithLp.ofLp hv) s
      rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, inertiaMatrix_mulVec_apply] at this
      simpa [(hpS s).ne'] using this
  · rintro ⟨f, hf0, hf⟩
    refine ⟨WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * f x, ?_, fun hv ↦ hf0 ?_⟩
    · ext s
      rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, inertiaMatrix_mulVec_apply]
      simp [(hpX _).ne', hf s]
    · ext x
      have := congrFun (congrArg WithLp.ofLp hv) x
      simpa [(hpX x).ne'] using this

open scoped RealInnerProductSpace in
/-- For a linear map `T` between finite-dimensional real inner product spaces,
`σ_{n-1}(T)² ‖x‖² ≤ ‖T x‖²`, `n` the dimension of the domain: the smallest eigenvalue of `T* T`
bounds its Rayleigh quotient from below. -/
lemma PerfectPrivacy.sq_singularValues_mul_sq_norm_le {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (x : E) :
    T.singularValues (Module.finrank ℝ E - 1) ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn | hn
  · have : Subsingleton E := Module.finrank_zero_iff.1 hn
    simp [Subsingleton.elim x 0]
  have hA := T.isSymmetric_adjoint_comp_self
  set b := hA.eigenvectorBasis rfl
  have h1 : ‖T x‖ ^ 2 = ⟪(LinearMap.adjoint T ∘ₗ T) x, x⟫ := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have h2 : ⟪(LinearMap.adjoint T ∘ₗ T) x, x⟫ = ∑ i, hA.eigenvalues rfl i * ⟪b i, x⟫ ^ 2 := by
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hA, hA.apply_eigenvectorBasis, real_inner_smul_right, real_inner_comm x]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  have h3 (i : Fin (Module.finrank ℝ E)) :
      T.singularValues (Module.finrank ℝ E - 1) ^ 2 ≤ hA.eigenvalues rfl i := by
    rw [T.sq_singularValues_of_lt rfl (Nat.sub_lt hn one_pos)]
    exact hA.eigenvalues_antitone rfl (Fin.mk_le_mk.2 (by omega))
  rw [h1, h2, ← b.sum_sq_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (h3 i) (sq_nonneg _)

omit [Fintype 𝓢] [DecidableEq 𝓧] in
private lemma sq_norm_toLp_sqrt_mul (f : 𝓧 → ℝ) :
    ‖(WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * f x : EuclideanSpace ℝ 𝓧)‖ ^ 2 =
      ∑ x, μ.snd.real {x} * f x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [mul_pow, Real.sq_sqrt measureReal_nonneg]

private lemma sq_norm_toEuclideanLin_inertiaMatrix [IsFiniteMeasure μ] (hX : ∀ x, μ.snd {x} ≠ 0)
    (f : 𝓧 → ℝ) :
    ‖Matrix.toEuclideanLin (inertiaMatrix μ) (WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * f x)‖ ^ 2 =
      ∑ s, (∑ x, μ.real {(s, x)} * f x) ^ 2 / μ.fst.real {s} := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hpX (x : 𝓧) : √(μ.snd.real {x}) ≠ 0 :=
    (Real.sqrt_pos.2 (measureReal_pos_of_ne_zero (hX x))).ne'
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, inertiaMatrix_mulVec_apply]
  simp [hpX, mul_pow, div_eq_inv_mul, Real.sq_sqrt measureReal_nonneg]

omit [Fintype 𝓢] [Fintype 𝓧] [DecidableEq 𝓧] in
private lemma toLp_sqrt_mul_div [IsFiniteMeasure μ] (hX : ∀ x, μ.snd {x} ≠ 0)
    (y : EuclideanSpace ℝ 𝓧) :
    (WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * (y.ofLp x / √(μ.snd.real {x})) :
      EuclideanSpace ℝ 𝓧) = y := by
  ext x
  simp [mul_div_cancel₀ _ (Real.sqrt_pos.2 (measureReal_pos_of_ne_zero (hX x))).ne']

/-- **Lemma 5 of Calmon–Makhdoumi–Médard**, inequality part (the part of Lemma 13 of the T-IT
version that is proved there): `δ(p_{S,X}) ‖f(X)‖₂² ≤ ‖E[f(X) | S]‖₂²` for every
`f : 𝓧 → ℝ`, where `‖f(X)‖₂² = ∑_x p_X(x) f(x)²` and
`‖E[f(X) | S]‖₂² = ∑_s p_S(s) E[f(X) | S = s]² = ∑_s (∑_x p_{S,X}(s, x) f(x))² / p_S(s)`.
So `δ(p_{S,X})` is at most the minimum in (8) [(66)]; the mean-zero constraint `E[f(X)] = 0` of
(8) is not needed for this inequality. The minimum is attained: `exists_privacyDelta_eq`. -/
theorem privacyDelta_mul_le [IsFiniteMeasure μ] (hX : ∀ x, μ.snd {x} ≠ 0) (f : 𝓧 → ℝ) :
    privacyDelta μ * ∑ x, μ.snd.real {x} * f x ^ 2 ≤
      ∑ s, (∑ x, μ.real {(s, x)} * f x) ^ 2 / μ.fst.real {s} := by
  have := PerfectPrivacy.sq_singularValues_mul_sq_norm_le
    (Matrix.toEuclideanLin (inertiaMatrix μ)) (WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * f x)
  rwa [finrank_euclideanSpace, sq_norm_toLp_sqrt_mul, sq_norm_toEuclideanLin_inertiaMatrix hX,
    ← principalInertia, ← privacyDelta_eq_principalInertia] at this

open scoped RealInnerProductSpace in
/-- For a linear map `T` between finite-dimensional real inner product spaces,
`‖T x‖² ≤ σ_0(T)² ‖x‖²`. -/
lemma PerfectPrivacy.sq_norm_le_sq_singularValues_zero_mul {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (x : E) :
    ‖T x‖ ^ 2 ≤ T.singularValues 0 ^ 2 * ‖x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn | hn
  · have : Subsingleton E := Module.finrank_zero_iff.1 hn
    simp [Subsingleton.elim x 0]
  have hA := T.isSymmetric_adjoint_comp_self
  set b := hA.eigenvectorBasis rfl
  have h1 : ‖T x‖ ^ 2 = ⟪(LinearMap.adjoint T ∘ₗ T) x, x⟫ := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have h2 : ⟪(LinearMap.adjoint T ∘ₗ T) x, x⟫ = ∑ i, hA.eigenvalues rfl i * ⟪b i, x⟫ ^ 2 := by
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hA, hA.apply_eigenvectorBasis, real_inner_smul_right, real_inner_comm x]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  have h3 (i : Fin (Module.finrank ℝ E)) : hA.eigenvalues rfl i ≤ T.singularValues 0 ^ 2 := by
    rw [T.sq_singularValues_of_lt rfl hn]
    exact hA.eigenvalues_antitone rfl (Fin.mk_le_mk.2 (Nat.zero_le _))
  rw [h1, h2, ← b.sum_sq_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (h3 i) (sq_nonneg _)

open scoped RealInnerProductSpace in
private lemma PerfectPrivacy.sq_norm_eq_inner {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (x : E) :
    ‖T x‖ ^ 2 = ⟪(LinearMap.adjoint T ∘ₗ T) x, x⟫ := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

section Marginals

variable [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓧]

omit [Fintype 𝓢] [DecidableEq 𝓧] in
private lemma fst_real_singleton [IsFiniteMeasure μ] (s : 𝓢) :
    μ.fst.real {s} = ∑ x, μ.real {(s, x)} := by
  classical
  have h : (Prod.fst ⁻¹' {s} : Set (𝓢 × 𝓧)) =
      ↑(Finset.univ.image fun x : 𝓧 ↦ ((s, x) : 𝓢 × 𝓧)) := by
    ext ⟨a, b⟩
    simp [eq_comm]
  rw [measureReal_def, Measure.fst_apply (measurableSet_singleton s), h, ← measureReal_def,
    ← sum_measureReal_singleton, Finset.sum_image fun _ _ _ _ h ↦ (Prod.ext_iff.1 h).2]

omit [Fintype 𝓧] [DecidableEq 𝓧] in
private lemma snd_real_singleton [IsFiniteMeasure μ] (x : 𝓧) :
    μ.snd.real {x} = ∑ s, μ.real {(s, x)} := by
  classical
  have h : (Prod.snd ⁻¹' {x} : Set (𝓢 × 𝓧)) =
      ↑(Finset.univ.image fun s : 𝓢 ↦ ((s, x) : 𝓢 × 𝓧)) := by
    ext ⟨a, b⟩
    simp [eq_comm]
  rw [measureReal_def, Measure.snd_apply (measurableSet_singleton x), h, ← measureReal_def,
    ← sum_measureReal_singleton, Finset.sum_image fun _ _ _ _ h ↦ (Prod.ext_iff.1 h).1]

omit [DecidableEq 𝓧] in
/-- `‖E[f(X) | S]‖₂² ≤ ‖f(X)‖₂²` (conditional Jensen), by the Cauchy–Schwarz inequality. -/
private lemma sum_sq_div_le [IsFiniteMeasure μ] (f : 𝓧 → ℝ) :
    ∑ s, (∑ x, μ.real {(s, x)} * f x) ^ 2 / μ.fst.real {s} ≤ ∑ x, μ.snd.real {x} * f x ^ 2 := by
  calc ∑ s, (∑ x, μ.real {(s, x)} * f x) ^ 2 / μ.fst.real {s}
      ≤ ∑ s, ∑ x, μ.real {(s, x)} * f x ^ 2 := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        rcases (measureReal_nonneg : 0 ≤ μ.fst.real {s}).eq_or_lt with h | h
        · rw [← h, div_zero]
          exact Finset.sum_nonneg fun x _ ↦ mul_nonneg measureReal_nonneg (sq_nonneg _)
        · rw [div_le_iff₀ h, fst_real_singleton, mul_comm]
          exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun _ _ ↦ measureReal_nonneg)
            (fun _ _ ↦ mul_nonneg measureReal_nonneg (sq_nonneg _)) fun x _ ↦ le_of_eq (by ring)
    _ = ∑ x, μ.snd.real {x} * f x ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [snd_real_singleton, Finset.sum_mul]

/-- The largest singular value of `Q` is `1`, `σ_0(Q)² = 1`, under full support of `p_X`
(Calmon–Makhdoumi–Médard, Definition 3: "The largest singular value of `Q` is 1"). This is why
`σ_0(Q)` is not counted among the principal inertia components. -/
theorem principalInertia_zero [IsProbabilityMeasure μ] (hX : ∀ x, μ.snd {x} ≠ 0) :
    principalInertia μ 0 = 1 := by
  set T := Matrix.toEuclideanLin (inertiaMatrix μ)
  have : Nonempty 𝓧 := (nonempty_of_isProbabilityMeasure μ).map Prod.snd
  have hcontr (y : EuclideanSpace ℝ 𝓧) : ‖T y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [← toLp_sqrt_mul_div hX y, sq_norm_toEuclideanLin_inertiaMatrix hX, sq_norm_toLp_sqrt_mul]
    exact sum_sq_div_le _
  have hu : ‖(WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * 1 : EuclideanSpace ℝ 𝓧)‖ ^ 2 = 1 := by
    rw [sq_norm_toLp_sqrt_mul]
    simp
  have hTu : ‖T (WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * 1)‖ ^ 2 = 1 := by
    rw [sq_norm_toEuclideanLin_inertiaMatrix hX]
    simp_rw [mul_one, ← fst_real_singleton, sq, mul_self_div_self]
    simp
  have hA := T.isSymmetric_adjoint_comp_self
  have hn : 0 < Module.finrank ℝ (EuclideanSpace ℝ 𝓧) := by
    rw [finrank_euclideanSpace]
    exact Fintype.card_pos
  refine le_antisymm ?_ ?_
  · set e := hA.eigenvectorBasis rfl ⟨0, hn⟩
    have he : ‖e‖ = 1 := (hA.eigenvectorBasis rfl).orthonormal.1 _
    have hTe : ‖T e‖ ^ 2 = principalInertia μ 0 := by
      rw [principalInertia, T.sq_singularValues_of_lt rfl hn, PerfectPrivacy.sq_norm_eq_inner,
        hA.apply_eigenvectorBasis, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      simp
    rw [← hTe]
    simpa [he] using hcontr e
  · have := PerfectPrivacy.sq_norm_le_sq_singularValues_zero_mul T
      (WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) * 1)
    rwa [hTu, hu, mul_one] at this

omit [DecidableEq 𝓧] in
private lemma PerfectPrivacy.inv_sqrt_mul_self {a : ℝ} (ha : 0 ≤ a) : (√a)⁻¹ * a = √a := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  · calc (√a)⁻¹ * a = (√a)⁻¹ * (√a * √a) := by rw [Real.mul_self_sqrt ha.le]
      _ = √a := inv_mul_cancel_left₀ (Real.sqrt_pos.2 ha).ne' _

open scoped RealInnerProductSpace in
/-- **Lemma 5 of Calmon–Makhdoumi–Médard**, attainment (Lemma 13 of the T-IT version): for
`|𝓧| ≥ 2` and full-support marginals, some `f : 𝓧 → ℝ` with `E[f(X)] = 0` and
`‖f(X)‖₂ = 1` has `‖E[f(X) | S]‖₂² = δ(p_{S,X})`. With `privacyDelta_mul_le`, this is (8) [(66)]:
`δ(p_{S,X})` is the minimum of `‖E[f(X) | S]‖₂²` over such `f`. -/
theorem exists_privacyDelta_eq [IsProbabilityMeasure μ] (hS : ∀ s, μ.fst {s} ≠ 0)
    (hX : ∀ x, μ.snd {x} ≠ 0) (h2 : 2 ≤ Fintype.card 𝓧) :
    ∃ f : 𝓧 → ℝ, ∑ x, μ.snd.real {x} * f x = 0 ∧ ∑ x, μ.snd.real {x} * f x ^ 2 = 1 ∧
      ∑ s, (∑ x, μ.real {(s, x)} * f x) ^ 2 / μ.fst.real {s} = privacyDelta μ := by
  classical
  set T := Matrix.toEuclideanLin (inertiaMatrix μ) with hT
  have hpS (s : 𝓢) : √(μ.fst.real {s}) ≠ 0 :=
    (Real.sqrt_pos.2 (measureReal_pos_of_ne_zero (hS s))).ne'
  have hpX (x : 𝓧) : √(μ.snd.real {x}) ≠ 0 :=
    (Real.sqrt_pos.2 (measureReal_pos_of_ne_zero (hX x))).ne'
  set u : EuclideanSpace ℝ 𝓧 := WithLp.toLp 2 fun x ↦ √(μ.snd.real {x}) with hu_def
  have hu1 : ‖u‖ ^ 2 = 1 := by
    have := sq_norm_toLp_sqrt_mul (μ := μ) fun _ ↦ 1
    simpa using this
  have hTu : T u = WithLp.toLp 2 fun s ↦ √(μ.fst.real {s}) := by
    ext s
    rw [hT, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, inertiaMatrix_mulVec_apply]
    simp_rw [hu_def, div_self (hpX _), mul_one, ← fst_real_singleton]
    exact PerfectPrivacy.inv_sqrt_mul_self measureReal_nonneg
  have hAu : (LinearMap.adjoint T ∘ₗ T) u = u := by
    rw [LinearMap.comp_apply, hTu, hT, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext x
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, inertiaMatrix,
      Matrix.of_apply, star_trivial, hu_def]
    have (s : 𝓢) : μ.real {(s, x)} / (√(μ.fst.real {s}) * √(μ.snd.real {x})) *
        √(μ.fst.real {s}) = μ.real {(s, x)} / √(μ.snd.real {x}) := by
      field_simp [hpS s]
    simp_rw [this, ← Finset.sum_div, ← snd_real_singleton, Real.div_sqrt]
  have hA := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ 𝓧) = Fintype.card 𝓧 := finrank_euclideanSpace
  have hlt : Fintype.card 𝓧 - 1 < Module.finrank ℝ (EuclideanSpace ℝ 𝓧) := by omega
  have hδ : privacyDelta μ = hA.eigenvalues rfl ⟨Fintype.card 𝓧 - 1, hlt⟩ := by
    rw [privacyDelta_eq_principalInertia, principalInertia, T.sq_singularValues_of_lt rfl hlt]
  have hδ1 : privacyDelta μ ≤ 1 := by
    rw [← principalInertia_zero hX, privacyDelta_eq_principalInertia, principalInertia,
      principalInertia]
    exact pow_le_pow_left₀ (T.singularValues_nonneg _) (T.singularValues_antitone (Nat.zero_le _)) 2
  obtain ⟨v, hv1, hvu, hTv⟩ : ∃ v : EuclideanSpace ℝ 𝓧,
      ‖v‖ = 1 ∧ ⟪u, v⟫ = 0 ∧ ‖T v‖ ^ 2 = privacyDelta μ := by
    rcases hδ1.lt_or_eq with hlt1 | heq1
    · set b := hA.eigenvectorBasis rfl
      have hAv := hA.apply_eigenvectorBasis rfl ⟨Fintype.card 𝓧 - 1, hlt⟩
      simp only [RCLike.ofReal_real_eq_id, id] at hAv
      refine ⟨b ⟨Fintype.card 𝓧 - 1, hlt⟩, b.orthonormal.1 _, ?_, ?_⟩
      · have h1 := hA u (b ⟨Fintype.card 𝓧 - 1, hlt⟩)
        rw [hAu, hAv, real_inner_smul_right, ← hδ] at h1
        have : (privacyDelta μ - 1) * ⟪u, b ⟨Fintype.card 𝓧 - 1, hlt⟩⟫ = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (by linarith)
      · rw [PerfectPrivacy.sq_norm_eq_inner, hAv, real_inner_smul_left,
          real_inner_self_eq_norm_sq, b.orthonormal.1, hδ]
        simp
    · have hcontr (y : EuclideanSpace ℝ 𝓧) : ‖T y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
        rw [← toLp_sqrt_mul_div hX y, sq_norm_toEuclideanLin_inertiaMatrix hX,
          sq_norm_toLp_sqrt_mul]
        exact sum_sq_div_le _
      have hlow (y : EuclideanSpace ℝ 𝓧) : ‖y‖ ^ 2 ≤ ‖T y‖ ^ 2 := by
        have := PerfectPrivacy.sq_singularValues_mul_sq_norm_le T y
        rwa [hn, ← principalInertia, ← privacyDelta_eq_principalInertia, heq1, one_mul] at this
      have hu0 : u ≠ 0 := fun h ↦ by simp [h] at hu1
      have hK : (ℝ ∙ u)ᗮ ≠ ⊥ := by
        intro hK
        have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
        rw [finrank_span_singleton hu0, hK, finrank_bot, hn] at this
        omega
      obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
      have hv : ‖‖w‖⁻¹ • w‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
      refine ⟨‖w‖⁻¹ • w, hv, ?_, ?_⟩
      · rw [real_inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hwK,
          mul_zero]
      · rw [heq1]
        refine le_antisymm ?_ ?_
        · have h := hcontr (‖w‖⁻¹ • w)
          rwa [hv, one_pow] at h
        · have h := hlow (‖w‖⁻¹ • w)
          rwa [hv, one_pow] at h
  refine ⟨fun x ↦ v.ofLp x / √(μ.snd.real {x}), ?_, ?_, ?_⟩
  · rw [← hvu, hu_def, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_div_assoc', mul_comm, mul_div_assoc, Real.div_sqrt]
  · rw [← sq_norm_toLp_sqrt_mul, toLp_sqrt_mul_div hX, hv1, one_pow]
  · rw [← sq_norm_toEuclideanLin_inertiaMatrix hX, toLp_sqrt_mul_div hX, hTv]

end Marginals

end PIC

/-! ### Auxiliary lemmas on finite alphabets -/

namespace PerfectPrivacy

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Mutual information vanishes exactly for product laws. -/
lemma mutualInfo_eq_zero_iff {ρ : Measure (α × β)} [IsFiniteMeasure ρ] :
    mutualInfo ρ = 0 ↔ ρ = ρ.fst.prod ρ.snd := by
  rw [mutualInfo, klDiv_eq_zero_iff]

/-- On countable alphabets with measurable singletons, `μ ⊗ₘ η = μ × ν` if and only if
`η a = ν` for every atom `a` of `μ`. -/
lemma compProd_eq_prod_iff [Countable α] [MeasurableSingletonClass α] [Countable β]
    [MeasurableSingletonClass β] {μ : Measure α} [IsFiniteMeasure μ] {η : Kernel α β}
    [IsFiniteKernel η] {ν : Measure β} [SFinite ν] :
    μ ⊗ₘ η = μ.prod ν ↔ ∀ a, μ {a} ≠ 0 → η a = ν := by
  have h (a : α) (b : β) : ((μ ⊗ₘ η) {(a, b)} = (μ.prod ν) {(a, b)}) ↔
      μ {a} * η a {b} = μ {a} * ν {b} := by
    rw [← Set.singleton_prod_singleton, compProd_apply_singleton_prod, Measure.prod_prod]
  constructor
  · intro hμ a ha
    refine Measure.ext_iff_singleton.2 fun b ↦ ?_
    exact (ENNReal.mul_right_inj ha (measure_ne_top _ _)).1 ((h a b).1 (by rw [hμ]))
  · intro hη
    refine Measure.ext_iff_singleton.2 fun ⟨a, b⟩ ↦ (h a b).2 ?_
    by_cases ha : μ {a} = 0
    · simp [ha]
    · rw [hη a ha]

/-- The point masses of a composition of kernels on finite alphabets, in real form. -/
lemma comp_real_singleton [Fintype β] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel β γ) [IsFiniteKernel η] (a : α) (c : γ) :
    ((η ∘ₖ κ) a).real {c} = ∑ b, (κ a).real {b} * (η b).real {c} := by
  rw [measureReal_def, Kernel.comp_apply' _ _ _ (measurableSet_singleton c), lintegral_fintype,
    ENNReal.toReal_sum fun b _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp [measureReal_def, ENNReal.toReal_mul, mul_comm]

/-- The point masses of `μ ⊗ₘ κ`, in real form. -/
lemma compProd_real_singleton [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) (b : β) :
    (μ ⊗ₘ κ).real {(a, b)} = μ.real {a} * (κ a).real {b} := by
  rw [measureReal_def, ← Set.singleton_prod_singleton, compProd_apply_singleton_prod,
    ENNReal.toReal_mul, measureReal_def, measureReal_def]

/-- The law on `β` putting mass `1 - b` on `y₀` and mass `b` on `y₁`. -/
noncomputable def twoPoint (y₀ y₁ : β) (b : ℝ) : Measure β :=
  ENNReal.ofReal (1 - b) • Measure.dirac y₀ + ENNReal.ofReal b • Measure.dirac y₁

variable {y₀ y₁ : β} {b : ℝ}

lemma isProbabilityMeasure_twoPoint (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    IsProbabilityMeasure (twoPoint y₀ y₁ b) :=
  ⟨by simp [twoPoint, ← ENNReal.ofReal_add (sub_nonneg.2 hb₁) hb₀]⟩

variable [MeasurableSingletonClass β]

lemma twoPoint_singleton_right (hne : y₀ ≠ y₁) : twoPoint y₀ y₁ b {y₁} = ENNReal.ofReal b := by
  simp [twoPoint, hne]

lemma twoPoint_singleton_left (hne : y₀ ≠ y₁) :
    twoPoint y₀ y₁ b {y₀} = ENNReal.ofReal (1 - b) := by
  simp [twoPoint, hne.symm]

lemma twoPoint_singleton_of_ne {y : β} (h₀ : y ≠ y₀) (h₁ : y ≠ y₁) : twoPoint y₀ y₁ b {y} = 0 := by
  simp [twoPoint, Ne.symm h₀, Ne.symm h₁]

lemma twoPoint_real_singleton_right (hne : y₀ ≠ y₁) (hb₀ : 0 ≤ b) :
    (twoPoint y₀ y₁ b).real {y₁} = b := by
  rw [measureReal_def, twoPoint_singleton_right hne, ENNReal.toReal_ofReal hb₀]

lemma twoPoint_real_singleton_left (hne : y₀ ≠ y₁) (hb₁ : b ≤ 1) :
    (twoPoint y₀ y₁ b).real {y₀} = 1 - b := by
  rw [measureReal_def, twoPoint_singleton_left hne, ENNReal.toReal_ofReal (sub_nonneg.2 hb₁)]

end PerfectPrivacy

open PerfectPrivacy

/-! ### The privacy-assuring mapping of the proof of Theorem 3 -/

section Mapping

variable [Fintype 𝓧] [MeasurableSingletonClass 𝓧]

/-- The privacy-assuring mapping of the proof of Theorem 3 of Calmon–Makhdoumi–Médard: given
`f : 𝓧 → ℝ`, when `X = x` the output takes the value `y₁` with probability
`1/2 + f(x) / (2 ‖f‖_∞)` and the value `y₀` with probability `1/2 - f(x) / (2 ‖f‖_∞)`
(the paper's `ε = (2 max_x |f(x)|)⁻¹`). For `f = 0` it is the constant uniform law on
`{y₀, y₁}`. -/
noncomputable def perfectPrivacyMapping (f : 𝓧 → ℝ) (y₀ y₁ : 𝓨) : Kernel 𝓧 𝓨 :=
  Kernel.ofFunOfCountable fun x ↦ twoPoint y₀ y₁ (2⁻¹ + f x / (2 * ‖f‖))

variable {f : 𝓧 → ℝ} {y₀ y₁ : 𝓨}

lemma perfectPrivacyMapping_apply (x : 𝓧) :
    perfectPrivacyMapping f y₀ y₁ x = twoPoint y₀ y₁ (2⁻¹ + f x / (2 * ‖f‖)) := rfl

omit [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] in
lemma PerfectPrivacy.abs_div_two_mul_norm_le (f : 𝓧 → ℝ) (x : 𝓧) :
    |f x / (2 * ‖f‖)| ≤ 2⁻¹ := by
  rcases eq_or_ne ‖f‖ 0 with h | h
  · simp [h]
  · have hpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm h)
    have := norm_le_pi_norm f x
    rw [Real.norm_eq_abs] at this
    have h2 : 0 < 2 * ‖f‖ := mul_pos two_pos hpos
    rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
    linarith

omit [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] in
lemma PerfectPrivacy.param_nonneg (f : 𝓧 → ℝ) (x : 𝓧) : 0 ≤ 2⁻¹ + f x / (2 * ‖f‖) := by
  linarith [(abs_le.1 (abs_div_two_mul_norm_le f x)).1]

omit [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧] in
lemma PerfectPrivacy.param_le_one (f : 𝓧 → ℝ) (x : 𝓧) : 2⁻¹ + f x / (2 * ‖f‖) ≤ 1 := by
  linarith [(abs_le.1 (abs_div_two_mul_norm_le f x)).2]

instance (f : 𝓧 → ℝ) (y₀ y₁ : 𝓨) : IsMarkovKernel (perfectPrivacyMapping f y₀ y₁) :=
  ⟨fun x ↦ isProbabilityMeasure_twoPoint (param_nonneg f x) (param_le_one f x)⟩

instance (y₀ y₁ : 𝓨) : IsProbabilityMeasure (twoPoint y₀ y₁ 2⁻¹) :=
  isProbabilityMeasure_twoPoint (by norm_num) (by norm_num)

variable [Countable 𝓨] [MeasurableSingletonClass 𝓨] {κ : Kernel 𝓢 𝓧} [IsMarkovKernel κ]

/-- If `E[f(X) | S = s] = 0` for every `s`, then the output of `perfectPrivacyMapping f y₀ y₁`
is uniform on `{y₀, y₁}` whatever the value of `S`. -/
theorem perfectPrivacyMapping_comp_eq_const (hne : y₀ ≠ y₁)
    (hf : ∀ s, ∑ x, (κ s).real {x} * f x = 0) :
    perfectPrivacyMapping f y₀ y₁ ∘ₖ κ = Kernel.const 𝓢 (twoPoint y₀ y₁ 2⁻¹) := by
  ext1 s
  rw [Kernel.const_apply]
  refine Measure.ext_iff_singleton.2 fun y ↦ ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
    ← measureReal_def, ← measureReal_def, comp_real_singleton]
  have hsum : ∑ x, (κ s).real {x} = 1 := by simp
  have hlin (c d : ℝ) : ∑ x, (κ s).real {x} * (c + d * f x) = c := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, mul_left_comm _ d,
      ← Finset.mul_sum, hf s]
    ring
  simp_rw [perfectPrivacyMapping_apply]
  by_cases h₁ : y = y₁
  · subst h₁
    simp_rw [twoPoint_real_singleton_right hne (param_nonneg f _),
      twoPoint_real_singleton_right hne (by norm_num : (0 : ℝ) ≤ 2⁻¹), div_eq_inv_mul _ (2 * ‖f‖)]
    exact hlin _ _
  by_cases h₀ : y = y₀
  · subst h₀
    simp_rw [twoPoint_real_singleton_left hne (param_le_one f _),
      twoPoint_real_singleton_left hne (by norm_num : (2⁻¹ : ℝ) ≤ 1)]
    convert hlin (1 - 2⁻¹) (-(2 * ‖f‖)⁻¹) using 3
    ring
  · simp [measureReal_def, twoPoint_singleton_of_ne h₀ h₁]

end Mapping

/-! ### Perfect privacy with non-trivial utility -/

section Setting

variable [Fintype 𝓢] [MeasurableSingletonClass 𝓢] [Fintype 𝓧] [MeasurableSingletonClass 𝓧]
  [MeasurableSingletonClass 𝓨] {π : Measure 𝓢} [IsProbabilityMeasure π] {κ : Kernel 𝓢 𝓧}
  [IsMarkovKernel κ] {f : 𝓧 → ℝ} {y₀ y₁ : 𝓨}

omit [Fintype 𝓢] in
private lemma sum_compProd_real_mul_eq_zero_iff (hπ : ∀ s, π {s} ≠ 0) :
    (∀ s, ∑ x, (π ⊗ₘ κ).real {(s, x)} * f x = 0) ↔ ∀ s, ∑ x, (κ s).real {x} * f x = 0 := by
  refine forall_congr' fun s ↦ ?_
  simp_rw [compProd_real_singleton, mul_assoc, ← Finset.mul_sum]
  exact mul_eq_zero_iff_left (measureReal_pos_of_ne_zero (hπ s)).ne'

/-- `δ(p_{S,X}) = 0` if and only if the matrix `P_{X|S}` has a nontrivial kernel: some nonzero
`f : 𝓧 → ℝ` has `E[f(X) | S = s] = ∑_x p_{X|S}(x | s) f(x) = 0` for every `s`. Here
`p_{S,X} = π ⊗ₘ κ`, and both marginals `p_S = π` and `p_X = κ ∘ₘ π` have full support. -/
theorem privacyDelta_compProd_eq_zero_iff [DecidableEq 𝓧] (hπ : ∀ s, π {s} ≠ 0)
    (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) :
    privacyDelta (π ⊗ₘ κ) = 0 ↔ ∃ f : 𝓧 → ℝ, f ≠ 0 ∧ ∀ s, ∑ x, (κ s).real {x} * f x = 0 := by
  rw [privacyDelta_eq_zero_iff_exists (by simpa [Measure.fst_compProd] using hπ)
    (by simpa [Measure.snd_compProd] using hX)]
  exact exists_congr fun f ↦ and_congr_right fun _ ↦ sum_compProd_real_mul_eq_zero_iff hπ

variable [Countable 𝓨]

omit [Fintype 𝓢] [MeasurableSingletonClass 𝓢] in
/-- If `E[f(X) | S] = 0`, then the output of `perfectPrivacyMapping f y₀ y₁` is independent of
`S`: perfect privacy (proof of Theorem 3 of Calmon–Makhdoumi–Médard). -/
theorem compProd_comp_perfectPrivacyMapping_eq_prod (hne : y₀ ≠ y₁)
    (hf : ∀ s, ∑ x, (κ s).real {x} * f x = 0) :
    π ⊗ₘ (perfectPrivacyMapping f y₀ y₁ ∘ₖ κ) =
      π.prod ((perfectPrivacyMapping f y₀ y₁ ∘ₖ κ) ∘ₘ π) := by
  rw [perfectPrivacyMapping_comp_eq_const hne hf, Measure.compProd_const, Measure.const_comp,
    measure_univ, one_smul]

omit [Fintype 𝓢] [MeasurableSingletonClass 𝓢] in
/-- If `E[f(X) | S] = 0`, the output of `perfectPrivacyMapping f y₀ y₁` is uniform on
`{y₀, y₁}`. -/
theorem perfectPrivacyMapping_comp_comp (hne : y₀ ≠ y₁)
    (hf : ∀ s, ∑ x, (κ s).real {x} * f x = 0) :
    perfectPrivacyMapping f y₀ y₁ ∘ₘ (κ ∘ₘ π) = twoPoint y₀ y₁ 2⁻¹ := by
  rw [Measure.comp_assoc, perfectPrivacyMapping_comp_eq_const hne hf, Measure.const_comp,
    measure_univ, one_smul]

omit [Fintype 𝓢] [MeasurableSingletonClass 𝓢] in
/-- If `E[f(X) | S] = 0` and `f ≠ 0` on the support of `p_X`, the output of
`perfectPrivacyMapping f y₀ y₁` is not independent of `X`: non-trivial utility (proof of
Theorem 3 of Calmon–Makhdoumi–Médard). -/
theorem compProd_perfectPrivacyMapping_ne_prod (hne : y₀ ≠ y₁)
    (hf : ∀ s, ∑ x, (κ s).real {x} * f x = 0) {x : 𝓧} (hx : f x ≠ 0)
    (hpx : (κ ∘ₘ π) {x} ≠ 0) :
    (κ ∘ₘ π) ⊗ₘ perfectPrivacyMapping f y₀ y₁ ≠
      (κ ∘ₘ π).prod (perfectPrivacyMapping f y₀ y₁ ∘ₘ (κ ∘ₘ π)) := by
  rw [Ne, compProd_eq_prod_iff, perfectPrivacyMapping_comp_comp hne hf]
  intro h
  have h₁ := congrArg (fun ν : Measure 𝓨 ↦ ν {y₁}) (h x hpx)
  simp only [perfectPrivacyMapping_apply, twoPoint_singleton_right hne] at h₁
  rw [ENNReal.ofReal_eq_ofReal_iff (param_nonneg f x) (by norm_num)] at h₁
  have hn : 0 < ‖f‖ := norm_pos_iff.2 fun h0 ↦ hx (by simp [h0])
  have : f x / (2 * ‖f‖) = 0 := by linarith
  exact hx (by simpa [hn.ne'] using this)

variable [DecidableEq 𝓧]

/-- **Theorem 3 of Calmon–Makhdoumi–Médard, "only if" part.** If a privacy-assuring mapping
`W : p_{Y|X}` makes `Y` independent of `S` (perfect privacy) but not of `X` (non-trivial utility),
then `δ(p_{S,X}) = 0`. Here `𝓨` is any countable alphabet. -/
theorem privacyDelta_eq_zero_of_compProd_eq_prod (hπ : ∀ s, π {s} ≠ 0)
    (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) (W : Kernel 𝓧 𝓨) [IsMarkovKernel W]
    (hSY : π ⊗ₘ (W ∘ₖ κ) = π.prod ((W ∘ₖ κ) ∘ₘ π))
    (hXY : (κ ∘ₘ π) ⊗ₘ W ≠ (κ ∘ₘ π).prod (W ∘ₘ (κ ∘ₘ π))) :
    privacyDelta (π ⊗ₘ κ) = 0 := by
  rw [privacyDelta_compProd_eq_zero_iff hπ hX]
  rw [compProd_eq_prod_iff] at hSY
  rw [Ne, compProd_eq_prod_iff] at hXY
  push Not at hXY
  obtain ⟨x₀, -, hW⟩ := hXY
  obtain ⟨y, hy⟩ : ∃ y, W x₀ {y} ≠ (W ∘ₘ (κ ∘ₘ π)) {y} := by
    by_contra! h
    exact hW (Measure.ext_iff_singleton.2 h)
  refine ⟨fun x ↦ (W x).real {y} - (W ∘ₘ (κ ∘ₘ π)).real {y}, fun h ↦ hy ?_, fun s ↦ ?_⟩
  · have := congrFun h x₀
    rw [Pi.zero_apply, sub_eq_zero] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  · have hsum : ∑ x, (κ s).real {x} = 1 := by simp
    have hcomp := comp_real_singleton κ W s y
    rw [hSY s (hπ s), ← Measure.comp_assoc] at hcomp
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, ← hcomp]
    ring

/-- **Theorem 3 of Calmon–Makhdoumi–Médard**, first clause, independence form: for an output
alphabet `𝓨` with at least two letters, there is a privacy-assuring mapping `W : p_{Y|X}` such
that `Y` is independent of `S` but not of `X` if and only if `δ(p_{S,X}) = 0`. The equivalence
with `v*(p_{S,X}) = 0` and the "only if" part of (18) are not formalized. -/
theorem exists_compProd_eq_prod_and_ne_prod_iff [Nontrivial 𝓨] (hπ : ∀ s, π {s} ≠ 0)
    (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) :
    (∃ W : Kernel 𝓧 𝓨, IsMarkovKernel W ∧ π ⊗ₘ (W ∘ₖ κ) = π.prod ((W ∘ₖ κ) ∘ₘ π) ∧
      (κ ∘ₘ π) ⊗ₘ W ≠ (κ ∘ₘ π).prod (W ∘ₘ (κ ∘ₘ π))) ↔ privacyDelta (π ⊗ₘ κ) = 0 := by
  refine ⟨fun ⟨W, _, hSY, hXY⟩ ↦ privacyDelta_eq_zero_of_compProd_eq_prod hπ hX W hSY hXY,
    fun hδ ↦ ?_⟩
  obtain ⟨y₀, y₁, hne⟩ := exists_pair_ne 𝓨
  obtain ⟨f, hf0, hf⟩ := (privacyDelta_compProd_eq_zero_iff hπ hX).1 hδ
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf0
  exact ⟨perfectPrivacyMapping f y₀ y₁, inferInstance,
    compProd_comp_perfectPrivacyMapping_eq_prod hne hf,
    compProd_perfectPrivacyMapping_ne_prod hne hf hx (hX x)⟩

/-- **Corollary 1 of Calmon–Makhdoumi–Médard** (Corollary 7 of the T-IT version): Theorem 3 holds
for every pair of non-negative dependence measures `J₁`, `J₂` that vanish exactly on product laws
(e.g. total variation or maximal correlation): for an output alphabet `𝓨` with at least two
letters, some privacy-assuring mapping has `J(S; Y) = 0` and `J(X; Y) > 0` if and only if
`δ(p_{S,X}) = 0`. -/
theorem exists_dependence_eq_zero_and_pos_iff [Nontrivial 𝓨]
    (J₁ : Measure (𝓢 × 𝓨) → ℝ≥0∞) (J₂ : Measure (𝓧 × 𝓨) → ℝ≥0∞)
    (hJ₁ : ∀ ρ, IsProbabilityMeasure ρ → (J₁ ρ = 0 ↔ ρ = ρ.fst.prod ρ.snd))
    (hJ₂ : ∀ ρ, IsProbabilityMeasure ρ → (J₂ ρ = 0 ↔ ρ = ρ.fst.prod ρ.snd))
    (hπ : ∀ s, π {s} ≠ 0) (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) :
    (∃ W : Kernel 𝓧 𝓨, IsMarkovKernel W ∧ J₁ (π ⊗ₘ (W ∘ₖ κ)) = 0 ∧
      0 < J₂ ((κ ∘ₘ π) ⊗ₘ W)) ↔ privacyDelta (π ⊗ₘ κ) = 0 := by
  rw [← exists_compProd_eq_prod_and_ne_prod_iff (𝓨 := 𝓨) hπ hX]
  refine exists_congr fun W ↦ ⟨fun ⟨hW, h₁, h₂⟩ ↦ ⟨hW, ?_, ?_⟩, fun ⟨hW, h₁, h₂⟩ ↦ ⟨hW, ?_, ?_⟩⟩
  · simpa [Measure.fst_compProd, Measure.snd_compProd] using (hJ₁ _ inferInstance).1 h₁
  · simpa [pos_iff_ne_zero, hJ₂ _ inferInstance, Measure.fst_compProd, Measure.snd_compProd]
      using h₂
  · exact (hJ₁ _ inferInstance).2 (by simpa [Measure.fst_compProd, Measure.snd_compProd] using h₁)
  · simpa [pos_iff_ne_zero, hJ₂ _ inferInstance, Measure.fst_compProd, Measure.snd_compProd]
      using h₂

/-- **Theorem 3 of Calmon–Makhdoumi–Médard**, first clause (Theorem 10 of Calmon et al., T-IT
2017): for an output alphabet `𝓨` with at least two letters, there is a privacy-assuring mapping
`W : p_{Y|X}`, `S → X → Y`, with perfect privacy `I(S; Y) = 0` and non-trivial utility
`I(X; Y) > 0` if and only if `δ(p_{S,X}) = 0`. The equivalence with `v*(p_{S,X}) = 0` and the
"only if" part of (18) [(70)] are not formalized. -/
theorem exists_perfectPrivacy_iff [Nontrivial 𝓨] (hπ : ∀ s, π {s} ≠ 0)
    (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) :
    (∃ W : Kernel 𝓧 𝓨, IsMarkovKernel W ∧ mutualInfo (π ⊗ₘ (W ∘ₖ κ)) = 0 ∧
      0 < mutualInfo ((κ ∘ₘ π) ⊗ₘ W)) ↔ privacyDelta (π ⊗ₘ κ) = 0 :=
  exists_dependence_eq_zero_and_pos_iff _ _ (fun _ _ ↦ mutualInfo_eq_zero_iff)
    (fun _ _ ↦ mutualInfo_eq_zero_iff) hπ hX

omit [Countable 𝓨] [MeasurableSingletonClass 𝓨] in
/-- **Theorem 3 of Calmon–Makhdoumi–Médard**, first clause, as stated: there is a
privacy-assuring mapping with a finite output alphabet (`Fin n` for some `n`), perfect privacy
`I(S; Y) = 0` and non-trivial utility `I(X; Y) > 0` if and only if `δ(p_{S,X}) = 0`. The
equivalence with `v*(p_{S,X}) = 0` and the "only if" part of (18) [(70)] are not formalized. -/
theorem exists_fin_perfectPrivacy_iff (hπ : ∀ s, π {s} ≠ 0) (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) :
    (∃ (n : ℕ) (W : Kernel 𝓧 (Fin n)), IsMarkovKernel W ∧ mutualInfo (π ⊗ₘ (W ∘ₖ κ)) = 0 ∧
      0 < mutualInfo ((κ ∘ₘ π) ⊗ₘ W)) ↔ privacyDelta (π ⊗ₘ κ) = 0 := by
  refine ⟨fun ⟨n, W, _, h₁, h₂⟩ ↦ privacyDelta_eq_zero_of_compProd_eq_prod hπ hX W
    (mutualInfo_compProd_eq_zero_iff.1 h₁)
    (fun h ↦ h₂.ne' (mutualInfo_compProd_eq_zero_iff.2 h)), fun h ↦ ⟨2, ?_⟩⟩
  exact (exists_perfectPrivacy_iff hπ hX).2 h

omit [DecidableEq 𝓧] in
/-- If `|𝓧| > |𝓢|`, perfect privacy with non-trivial utility is always achievable
(Calmon–Makhdoumi–Médard, remark after Theorem 3). -/
theorem exists_perfectPrivacy_of_card_lt [Nontrivial 𝓨] (hπ : ∀ s, π {s} ≠ 0)
    (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) (h : Fintype.card 𝓢 < Fintype.card 𝓧) :
    ∃ W : Kernel 𝓧 𝓨, IsMarkovKernel W ∧ mutualInfo (π ⊗ₘ (W ∘ₖ κ)) = 0 ∧
      0 < mutualInfo ((κ ∘ₘ π) ⊗ₘ W) := by
  classical
  exact (exists_perfectPrivacy_iff hπ hX).2 (privacyDelta_eq_zero_of_card_lt h)

omit [Fintype 𝓢] [DecidableEq 𝓧] in
/-- For a **binary** useful variable `X`, perfect privacy with non-trivial utility is achievable
if and only if `S` and `X` are independent. This is the corrected form of footnote 8 of the
T-IT version (Calmon et al. 2017), which states it for a binary *private* variable `S` (see the
notes on the paper). -/
theorem exists_perfectPrivacy_iff_compProd_eq_prod_of_card_eq_two [Finite 𝓢] [Nontrivial 𝓨]
    (hπ : ∀ s, π {s} ≠ 0) (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) (h2 : Fintype.card 𝓧 = 2) :
    (∃ W : Kernel 𝓧 𝓨, IsMarkovKernel W ∧ mutualInfo (π ⊗ₘ (W ∘ₖ κ)) = 0 ∧
      0 < mutualInfo ((κ ∘ₘ π) ⊗ₘ W)) ↔ π ⊗ₘ κ = π.prod (κ ∘ₘ π) := by
  classical
  have := Fintype.ofFinite 𝓢
  obtain ⟨a, b, hab, huniv⟩ := Finset.card_eq_two.1 h2
  have hmem (x : 𝓧) : x = a ∨ x = b := by
    have := Finset.mem_univ x
    rw [huniv] at this
    simpa using this
  have hsum2 (g : 𝓧 → ℝ) : ∑ x, g x = g a + g b :=
    Fintype.sum_eq_add a b hab fun x hx ↦ ((hmem x).elim hx.1 hx.2).elim
  have hone (s : 𝓢) : (κ s).real {a} + (κ s).real {b} = 1 := by
    rw [← hsum2 fun x ↦ (κ s).real {x}]
    simp
  have : Nonempty 𝓢 := nonempty_of_isProbabilityMeasure π
  rw [exists_perfectPrivacy_iff hπ hX, privacyDelta_compProd_eq_zero_iff hπ hX,
    compProd_eq_prod_iff]
  constructor
  · rintro ⟨f, hf0, hf⟩
    have hk (s : 𝓢) : (κ s).real {a} * (f a - f b) = -f b := by
      have := hf s
      rw [hsum2] at this
      linear_combination this - f b * hone s
    have hfab : f a - f b ≠ 0 := by
      intro h0
      obtain ⟨s⟩ := ‹Nonempty 𝓢›
      have hb : f b = 0 := by simpa [h0] using hk s
      refine hf0 (funext fun x ↦ ?_)
      rcases hmem x with rfl | rfl
      · simpa [hb] using sub_eq_zero.1 h0
      · simpa using hb
    obtain ⟨s₀⟩ := ‹Nonempty 𝓢›
    have hκ (s : 𝓢) : κ s = κ s₀ := by
      have ha : (κ s).real {a} = (κ s₀).real {a} :=
        mul_right_cancel₀ hfab ((hk s).trans (hk s₀).symm)
      have hb : (κ s).real {b} = (κ s₀).real {b} := by linarith [hone s, hone s₀]
      refine Measure.ext_iff_singleton.2 fun x ↦ ?_
      rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
      rcases hmem x with rfl | rfl
      exacts [ha, hb]
    have hconst : κ = Kernel.const 𝓢 (κ s₀) := Kernel.ext fun s ↦ hκ s
    intro s _
    rw [hconst, Kernel.const_apply, Measure.const_comp, measure_univ, one_smul]
  · intro hκ
    refine ⟨fun x ↦ if x = a then (κ ∘ₘ π).real {b} else -(κ ∘ₘ π).real {a}, fun h0 ↦ ?_,
      fun s ↦ ?_⟩
    · have := congrFun h0 a
      simp only [ite_true, Pi.zero_apply] at this
      exact (measureReal_pos_of_ne_zero (hX b)).ne' this
    · simp only [hsum2, hκ s (hπ s), ite_true, hab.symm, ite_false]
      ring

end Setting

/-! ### The privacy funnel and the utility of perfectly private mappings -/

section Funnel

/-- The **privacy funnel** `G_I(t, p_{S,X}) = inf {I(S; Y) | I(X; Y) ≥ t, S → X → Y}`
(Calmon–Makhdoumi–Médard, Definition 1), with `p_{S,X} = π ⊗ₘ κ`, the infimum being over all
privacy-assuring mappings `W : p_{Y|X}` with a finite output alphabet, which we take to be
`Fin n` for some `n` (mutual information is in nats). The paper considers `0 ≤ t ≤ H(X)`; for
larger `t` the infimum is over the empty set and equals `∞`. -/
noncomputable def privacyFunnel (π : Measure 𝓢) (κ : Kernel 𝓢 𝓧) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (W : Kernel 𝓧 (Fin n)) (_ : IsMarkovKernel W)
    (_ : t ≤ mutualInfo ((κ ∘ₘ π) ⊗ₘ W)), mutualInfo (π ⊗ₘ (W ∘ₖ κ))

private lemma mul_log_two_mul (b : ℝ) :
    b * Real.log (b * 2) = b * Real.log 2 + b * Real.log b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · rw [Real.log_mul hb two_ne_zero]
    ring

variable [MeasurableSingletonClass 𝓨] {y₀ y₁ : 𝓨}

/-- The divergence of the law `twoPoint y₀ y₁ b` from the uniform law on `{y₀, y₁}` is
`log 2 - h(b)`, `h` the binary entropy function (in nats). -/
lemma PerfectPrivacy.sum_twoPoint_mul_log [Fintype 𝓨] (hne : y₀ ≠ y₁) {b : ℝ} (hb₀ : 0 ≤ b)
    (hb₁ : b ≤ 1) :
    ∑ y, (twoPoint y₀ y₁ b).real {y} *
      Real.log ((twoPoint y₀ y₁ b).real {y} / (twoPoint y₀ y₁ 2⁻¹).real {y}) =
      Real.log 2 - Real.binEntropy b := by
  rw [Fintype.sum_eq_add y₁ y₀ hne.symm fun y hy ↦ by
      simp [measureReal_def, twoPoint_singleton_of_ne hy.2 hy.1],
    twoPoint_real_singleton_right hne hb₀, twoPoint_real_singleton_right hne (by norm_num),
    twoPoint_real_singleton_left hne hb₁, twoPoint_real_singleton_left hne (by norm_num),
    show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, div_inv_eq_mul, div_inv_eq_mul, mul_log_two_mul,
    mul_log_two_mul]
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  ring

variable [Fintype 𝓢] [MeasurableSingletonClass 𝓢] [Fintype 𝓧] [MeasurableSingletonClass 𝓧]
  {π : Measure 𝓢} [IsProbabilityMeasure π] {κ : Kernel 𝓢 𝓧} [IsMarkovKernel κ] {f : 𝓧 → ℝ}

omit [Fintype 𝓢] [MeasurableSingletonClass 𝓢] in
/-- The useful information disclosed by the perfectly private mapping of the proof of Theorem 3
(Calmon–Makhdoumi–Médard, (19), in nats): if `E[f(X) | S] = 0`, then
`I(X; Y) = log 2 - ∑_x p_X(x) h(1/2 + f(x) / (2 ‖f‖_∞))`, `h` the binary entropy function. -/
theorem mutualInfo_perfectPrivacyMapping [Finite 𝓨] (hne : y₀ ≠ y₁)
    (hf : ∀ s, ∑ x, (κ s).real {x} * f x = 0) :
    mutualInfo ((κ ∘ₘ π) ⊗ₘ perfectPrivacyMapping f y₀ y₁) = ENNReal.ofReal
      (Real.log 2 - ∑ x, (κ ∘ₘ π).real {x} * Real.binEntropy (2⁻¹ + f x / (2 * ‖f‖))) := by
  have := Fintype.ofFinite 𝓨
  rw [mutualInfo_compProd, perfectPrivacyMapping_comp_comp hne hf]
  have hac : (κ ∘ₘ π) ⊗ₘ perfectPrivacyMapping f y₀ y₁ ≪
      (κ ∘ₘ π).prod (twoPoint y₀ y₁ 2⁻¹) := by
    refine fun s hs ↦ ?_
    rw [measure_eq_zero_iff_ae_notMem, ae_iff_of_countable] at hs ⊢
    rintro ⟨x, y⟩ hz hzs
    refine hs (x, y) (fun hν ↦ hz ?_) hzs
    rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_eq_zero] at hν
    rw [← Set.singleton_prod_singleton, compProd_apply_singleton_prod]
    rcases hν with h | h
    · simp [h]
    · have h₁ : y ≠ y₁ := by
        rintro rfl
        simp [twoPoint_singleton_right hne] at h
      have h₀ : y ≠ y₀ := by
        rintro rfl
        rw [twoPoint_singleton_left hne, ENNReal.ofReal_eq_zero] at h
        norm_num at h
      simp [perfectPrivacyMapping_apply, twoPoint_singleton_of_ne h₀ h₁]
  rw [klDiv_eq_ofReal_klDivSum hac, klDivSum, Fintype.sum_prod_type]
  congr 1
  simp_rw [compProd_real_singleton, ← Set.singleton_prod_singleton, measureReal_prod_prod]
  have hx (x : 𝓧) : ∑ y, (κ ∘ₘ π).real {x} * (perfectPrivacyMapping f y₀ y₁ x).real {y} *
      Real.log ((κ ∘ₘ π).real {x} * (perfectPrivacyMapping f y₀ y₁ x).real {y} /
        ((κ ∘ₘ π).real {x} * (twoPoint y₀ y₁ 2⁻¹).real {y})) =
      (κ ∘ₘ π).real {x} * (Real.log 2 - Real.binEntropy (2⁻¹ + f x / (2 * ‖f‖))) := by
    rcases eq_or_ne ((κ ∘ₘ π).real {x}) 0 with h0 | h0
    · simp [h0]
    · simp_rw [mul_div_mul_left _ _ h0, mul_assoc, ← Finset.mul_sum, perfectPrivacyMapping_apply,
        sum_twoPoint_mul_log hne (param_nonneg f x) (param_le_one f x)]
  have hsum : ∑ x, (κ ∘ₘ π).real {x} = 1 := by simp
  simp_rw [hx, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]

omit [Fintype 𝓢] [MeasurableSingletonClass 𝓢] in
/-- The entropy inequality `∑_x p_X(x) h(1/2 + f(x) / (2 ‖f‖_∞)) < log 2`, for any `f` that is
nonzero at some point of the support of `p_X`.

When moreover `f` is conditionally centered (`E[f(X) | S] = 0`) and `y₀ ≠ y₁`, the difference
`log 2 - ∑_x p_X(x) h(⋯)` is the useful information `I(X; Y)` disclosed by
`perfectPrivacyMapping f y₀ y₁` (`mutualInfo_perfectPrivacyMapping`, (19) of
Calmon–Makhdoumi–Médard), which is therefore positive. Without centering this interpretation
fails: for `f ≡ 1` the difference is `log 2`, but the mapping always outputs `y₁`, so
`I(X; Y) = 0`. -/
theorem PerfectPrivacy.sum_binEntropy_lt_log_two {x : 𝓧} (hx : f x ≠ 0) (hpx : (κ ∘ₘ π) {x} ≠ 0) :
    ∑ x, (κ ∘ₘ π).real {x} * Real.binEntropy (2⁻¹ + f x / (2 * ‖f‖)) < Real.log 2 := by
  have hn : 0 < ‖f‖ := norm_pos_iff.2 fun h0 ↦ hx (by simp [h0])
  calc ∑ x, (κ ∘ₘ π).real {x} * Real.binEntropy (2⁻¹ + f x / (2 * ‖f‖))
      < ∑ x, (κ ∘ₘ π).real {x} * Real.log 2 := by
        refine Finset.sum_lt_sum (fun x _ ↦ mul_le_mul_of_nonneg_left Real.binEntropy_le_log_two
          measureReal_nonneg) ⟨x, Finset.mem_univ _, ?_⟩
        refine mul_lt_mul_of_pos_left (Real.binEntropy_lt_log_two.2 fun h ↦ hx ?_)
          (measureReal_pos_of_ne_zero hpx)
        have : f x / (2 * ‖f‖) = 0 := by linarith
        simpa [hn.ne'] using this
    _ = Real.log 2 := by rw [← Finset.sum_mul]; simp

omit [Fintype 𝓢] [MeasurableSingletonClass 𝓢] in
/-- **Corollary 2 of Calmon–Makhdoumi–Médard** (Corollary 8 of Calmon et al., T-IT 2017),
first claim, in nats (the sharpness claim is not formalized): for every conditionally centered
`f`, i.e. with `E[f(X) | S] = 0` and no normalization assumed, the privacy funnel vanishes,
`G_I(t, p_{S,X}) = 0`, for all `t ≤ log 2 - E[h(1/2 + f(X) / (2 ‖f‖_∞))]`.

The paper's `F₀` consists of the trivial function `f₀ = 0` and the conditionally centered `f`
with `E[f(X)] = 0` and `‖f(X)‖₂ = 1`; every element of `F₀` is conditionally centered, so the
theorem applies to all of them. Hence the largest `t*` with `G_I(t*, p_{S,X}) = 0` satisfies
`t* ≥ sup_{f ∈ F₀} (log 2 - E[h(1/2 + f(X) / (2 ‖f‖_∞))])` (see the notes on the paper). The
normalization in `F₀` loses nothing: the bound is unchanged when `f` is replaced by `c f` with
`c ≠ 0`, since it depends on `f` only through `f / ‖f‖_∞` up to sign and `h` is symmetric about
`1/2`. -/
theorem privacyFunnel_eq_zero_of_le (hf : ∀ s, ∑ x, (κ s).real {x} * f x = 0) {t : ℝ≥0∞}
    (ht : t ≤ ENNReal.ofReal
      (Real.log 2 - ∑ x, (κ ∘ₘ π).real {x} * Real.binEntropy (2⁻¹ + f x / (2 * ‖f‖)))) :
    privacyFunnel π κ t = 0 := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  refine le_antisymm ?_ zero_le
  refine iInf_le_of_le 2 <| iInf_le_of_le (perfectPrivacyMapping f 0 1) <|
    iInf_le_of_le inferInstance <| iInf_le_of_le ?_ ?_
  · rwa [mutualInfo_perfectPrivacyMapping hne hf]
  · exact (mutualInfo_compProd_eq_zero_iff.2
      (compProd_comp_perfectPrivacyMapping_eq_prod hne hf)).le

/-- **Theorem 3 of Calmon–Makhdoumi–Médard**, (18), "if" part: if `δ(p_{S,X}) = 0`, then the
privacy funnel vanishes at some `t₀ > 0`, i.e. a non-negligible amount of useful information can
be disclosed with perfect privacy. -/
theorem exists_pos_privacyFunnel_eq_zero [DecidableEq 𝓧] (hπ : ∀ s, π {s} ≠ 0)
    (hX : ∀ x, (κ ∘ₘ π) {x} ≠ 0) (h : privacyDelta (π ⊗ₘ κ) = 0) :
    ∃ t₀ : ℝ≥0∞, 0 < t₀ ∧ privacyFunnel π κ t₀ = 0 := by
  obtain ⟨f, hf0, hf⟩ := (privacyDelta_compProd_eq_zero_iff hπ hX).1 h
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf0
  exact ⟨_, ENNReal.ofReal_pos.2 (sub_pos.2 (sum_binEntropy_lt_log_two hx (hX x))),
    privacyFunnel_eq_zero_of_le hf le_rfl⟩

end Funnel

end InformationTheory
