/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.MetricPrivacy.Laplace
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.InformationTheory.Hamming

/-!
# Differentially private empirical risk minimization: output perturbation

This file formalizes the output-perturbation part of K. Chaudhuri, C. Monteleoni and
A. D. Sarwate, *Differentially private empirical risk minimization*, JMLR 12 (2011), 1069–1109
([arXiv:0912.0071](https://arxiv.org/abs/0912.0071), v5), cited as [CMS]: the minimizer of a
`Λ`-strongly convex regularized empirical risk moves by at most `2 / (nΛ)` when one data point
changes (Lemma 1, Corollary 1), so releasing it with additive noise of density `∝ e^{-β‖b‖}`,
`β = nΛε/2`, is `ε`-differentially private (Algorithm 1, Theorem 1).

Strong convexity is Mathlib's `StrongConvexOn univ m`, which is Definition 1, equation (3), of
[CMS]: `H(αf + (1 - α)g) ≤ αH(f) + (1 - α)H(g) - (m/2) α (1 - α) ‖f - g‖²`. Privacy is
`IsEpsDP` (`InfoLeakage.DP.Basic`), i.e. Definition 3 of [CMS]; the noise mechanism is the
Laplace mechanism `MetricDP.laplaceMech` of `InfoLeakage.MetricPrivacy.Laplace` for the scaled
Euclidean distance, and its privacy comes from `MetricDP.isMetricDP_laplaceMech_edist`.

## Main definitions

* `PrivateERM.objective ℓ N Λ D`: the regularized empirical risk
  `J(f, D) = (1/n) ∑ᵢ ℓ(yᵢ ⟪xᵢ, f⟫) + Λ N(f)` of a dataset `D = ((xᵢ, yᵢ))ᵢ` of `n` points of
  `E × ℝ`, for linear predictors `f ∈ E` and a margin loss `ℓ` (equation (1) of [CMS] with
  `f(x) = fᵀx`, in the form `ℓ(y fᵀx)` used in Section 3).
* `PrivateERM.noiseConst E β`, `PrivateERM.outputPerturbation β`: the normalizing constant
  `α = ∫ e^{-β‖b‖} db` and the kernel `c ↦ law(c + b)`, `b` of density `e^{-β‖b‖} / α`
  (equation (7) and Algorithm 1 of [CMS]), on a finite-dimensional real inner product space `E`
  such as `EuclideanSpace ℝ (Fin d)`.
* `PrivateERM.erm ℓ N Λ D`: the minimizer `argmin_f J(f, D)` (`PrivateERM.isMinOn_erm`).
* `PrivateERM.Neighbour`: datasets of points with `‖x‖ ≤ 1`, `|y| ≤ 1` differing in one entry.
* `PrivateERM.logisticLoss`: `ℓ_LR(z) = log(1 + e^{-z})` (Section 3.4.1).

## Main statements (paper result → Lean name)

* Lemma 1 (sensitivity of the minimizer under a perturbation `g` of a strongly convex `G`):
  `PrivateERM.norm_sub_le_of_norm_gradient_le` (with `‖∇g‖ ≤ L` as in the paper), and its
  derivative-free form `PrivateERM.norm_sub_le_of_lipschitzWith` (`g` `L`-Lipschitz).
* Corollary 1 (the `L₂`-sensitivity of `argmin J(·, D)` is at most `2 / (nΛ)`):
  `PrivateERM.norm_sub_le_two_div_of_hammingDist_le_one` (differentiable `ℓ` with `|ℓ'| ≤ 1`, as
  in the paper), generalized to `L`-Lipschitz losses (bound `2L / (nΛ)`, no differentiability of
  `ℓ` or `N`) in `PrivateERM.norm_sub_le_of_hammingDist_le_one` and
  `PrivateERM.norm_sub_le_of_forall_ne_eq`.
* Theorem 1 (Algorithm 1 is `ε`-differentially private): as an `IsEpsDP` mechanism
  `D ↦ argmin J(·, D) + b`, `PrivateERM.isEpsDP_outputPerturbation_comap_erm` (for any choice of
  minimizers, `PrivateERM.isEpsDP_outputPerturbation_comap`); for the output distributions of
  two neighbouring datasets, `PrivateERM.outputPerturbation_le_smul_of_neighbour`; in the
  two-sided form of equation (5), `PrivateERM.measureReal_outputPerturbation_erm_mem_Icc` (using
  `PrivateERM.Neighbour.symm`); for `L`-Lipschitz losses,
  `PrivateERM.outputPerturbation_le_smul_of_lipschitzWith`. The `IsEpsDP` statements also assert
  that the mechanism is a Markov kernel, since `IsEpsDP` alone holds for the zero kernel.
* Section 3.1 (the sensitivity method with `ℓ₂` noise of density `∝ e^{-β‖b‖}`, and the
  computation (10)–(11)): `PrivateERM.isMetricDP_outputPerturbation`,
  `PrivateERM.outputPerturbation_le_smul`, `PrivateERM.isEpsDP_comap_outputPerturbation`; the
  noise density is a probability density for `β > 0`:
  `PrivateERM.isMarkovKernel_outputPerturbation`, and the output is `c + b`:
  `PrivateERM.outputPerturbation_eq_map`.
* Corollary 2, Algorithm 1 part (logistic regression with `N(f) = ‖f‖² / 2`):
  `PrivateERM.isEpsDP_outputPerturbation_comap_erm_logisticLoss`, through
  `PrivateERM.convexOn_logisticLoss`, `PrivateERM.abs_deriv_logisticLoss_le` and
  `PrivateERM.strongConvexOn_half_sq_norm`.
* Section 2.2 ("a strictly convex function has a unique minimum"), uniqueness part, for strongly
  convex functions: `PrivateERM.eq_of_isMinOn_of_isMinOn`. Existence of the minimizer is an
  addition (not claimed in the paper, and false for strictly convex functions in general; see the
  notes below), proved for strongly convex functions in finite dimension:
  `PrivateERM.exists_isMinOn_of_strongConvexOn` and `PrivateERM.exists_isMinOn_objective`.
* Supporting results: quadratic growth at a minimizer,
  `PrivateERM.mul_sq_norm_sub_le_of_isMinOn`; strong convexity of the objective,
  `PrivateERM.strongConvexOn_objective`; continuity of the minimizer in the data (not in the
  paper), `PrivateERM.continuous_of_isMinOn_objective`, hence `PrivateERM.measurable_erm`.

## Implementation notes

The proof of Lemma 1 in [CMS] goes through the first-order optimality conditions and the strong
monotonicity of `∇G` (Lemma 14 of Shalev-Shwartz's thesis). We use instead the quadratic growth
`G(f) ≥ G(f₁) + (m/2)‖f - f₁‖²` of an `m`-strongly convex `G` at its minimizer `f₁`, which needs
no derivatives: adding it for `G` at `f₁` and for `G + g` at `f₂` gives
`m ‖f₁ - f₂‖² ≤ g(f₁) - g(f₂) ≤ L ‖f₁ - f₂‖`. This uses the hypothesis of [CMS] that both `G` and
`G + g` are strongly convex, but neither the differentiability of `G` nor that of `g` (only its
Lipschitz constant). Consequently Corollary 1 and Theorem 1 hold for any convex `L`-Lipschitz
loss and any `1`-strongly convex regularizer, differentiable or not; the paper-faithful
statements keep the paper's hypotheses on `ℓ` and drop the (unused) differentiability of `N`.

Datasets are tuples `D : Fin n → E × ℝ`, and "differing in a single entry" is
`hammingDist D D' ≤ 1` in the sensitivity results and `MetricDP.HammingAdj` (`= 1`) in
`Neighbour`. [CMS] assumes that all feature vectors lie in the unit ball and that the labels are
`±1`; we assume `‖xᵢ‖ ≤ 1` and `|yᵢ| ≤ 1` (the proof of Corollary 1 uses `yᵢ ∈ [-1, 1]`), and in
`PrivateERM.norm_sub_le_of_forall_ne_eq` only for the record that changes. Labels and features
are otherwise arbitrary, and `E` is any real inner product space (finite-dimensional for the
noise).

Definition 3 of [CMS] quantifies over datasets without any measurability in the dataset, and
`PrivateERM.outputPerturbation_le_smul_of_neighbour` states Theorem 1 in exactly that form, for
the minimizers themselves. A Markov kernel on datasets, as `IsEpsDP` requires, needs the map
`D ↦ argmin J(·, D)` to be measurable for the Borel σ-algebra of `Fin n → E × ℝ`; we prove it is
continuous (`PrivateERM.continuous_of_isMinOn_objective`), a fact the paper does not discuss.

## Notes on the paper

* Section 2.2 (p. 6 of arXiv v5): "A strictly convex function has a unique minimum". Only
  uniqueness holds: a strictly convex function need not attain its infimum (`exp` on `ℝ`). The
  objectives of the paper are `Λ`-strongly convex with `Λ > 0`, and in finite dimension these do
  have a minimizer (`PrivateERM.exists_isMinOn_of_strongConvexOn`), so `argmin J(·, D)` is well
  defined and the paper's results are unaffected.
* Proof of Theorem 1 (pp. 9–10 of arXiv v5), equations (10)–(11): by (10) the density ratio is
  `ν(b₁)/ν(b₂) = e^{β(‖b₂‖ - ‖b₁‖)}`, so the bound `≤ e^ε` needs `‖b₂‖ - ‖b₁‖ ≤ 2/(nΛ)`, whereas
  (11) bounds `‖b₁‖ - ‖b₂‖`. The same triangle inequality with `b₁, b₂` exchanged gives the needed
  bound, so the theorem is unaffected (`PrivateERM.outputPerturbation_le_smul_of_neighbour`).
* Statement of Corollary 1 (Section 3.3.1, p. 10 of arXiv v5): "the `L₂`-sensitivity of
  `J(f, D)`" should read "of `argmin_f J(f, D)`", as in the proof of Theorem 1.
* Proof of Corollary 1 (p. 10 of arXiv v5), equation (16) is the gradient of `-g` rather than of
  `g`, which does not affect the norm bound. In the last display, the first inequality
  `‖∇g(f)‖ ≤ (1/n)‖xₙ - x'ₙ‖` does not hold in general: for `x'ₙ = xₙ ≠ 0`, `y'ₙ = -yₙ = -1` and
  the logistic loss, the right side is `0` while
  `∇g(f) = -(1/n)(ℓ'(fᵀxₙ) + ℓ'(-fᵀxₙ)) xₙ = xₙ / n` (as `ℓ'_LR(z) + ℓ'_LR(-z) = -1`). The bound
  `‖∇g(f)‖ ≤ (1/n)(‖xₙ‖ + ‖x'ₙ‖) ≤ 2/n` that the proof then uses follows directly from the
  triangle inequality, so Corollary 1 is true
  (`PrivateERM.norm_sub_le_two_div_of_hammingDist_le_one`).
* Lemma 1 (p. 10) calls `G` and `g` "vector-valued"; they are real-valued.

## Not formalized

* Objective perturbation: Algorithm 2, Theorem 2 (its privacy, via a change of variables with
  the Jacobian of `b ↦ f_priv`), Lemma 2, and the Algorithm 2 parts of Corollaries 2–4.
* Support vector machines (Section 3.4.2, Corollaries 3 and 4: Huber loss), kernel methods
  (Section 5), parameter tuning (Section 6), and the generalization bounds (Section 4:
  Theorems 3 and 4, Lemmas 3–5, Corollaries 5 and 6).
-/

@[expose] public section

open Set Real
open scoped ENNReal NNReal InnerProductSpace Gradient

namespace InformationTheory

namespace PrivateERM

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G g : E → ℝ} {m : ℝ}

/-- **Quadratic growth at a minimizer**: if `F` is `m`-strongly convex and `x₀` minimizes `F`,
then `F(x₀) + (m/2)‖y - x₀‖² ≤ F(y)` for every `y`. -/
theorem mul_sq_norm_sub_le_of_isMinOn (hF : StrongConvexOn univ m F) {x₀ : E}
    (hx₀ : IsMinOn F univ x₀) (y : E) : m / 2 * ‖y - x₀‖ ^ 2 ≤ F y - F x₀ := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → (1 - t) * (m / 2 * ‖y - x₀‖ ^ 2) ≤ F y - F x₀ := by
    intro t ht₀ ht₁
    have h₁ := hF.2 (mem_univ y) (mem_univ x₀) ht₀.le (sub_nonneg.2 ht₁) (add_sub_cancel t 1)
    have h₂ := isMinOn_univ_iff.1 hx₀ (t • y + (1 - t) • x₀)
    simp only [smul_eq_mul] at h₁
    have : t * ((1 - t) * (m / 2 * ‖y - x₀‖ ^ 2)) ≤ t * (F y - F x₀) := by linarith
    exact le_of_mul_le_mul_left this ht₀
  have hlim : Filter.Tendsto (fun t : ℝ ↦ (1 - t) * (m / 2 * ‖y - x₀‖ ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds (m / 2 * ‖y - x₀‖ ^ 2)) := by
    have : Continuous fun t : ℝ ↦ (1 - t) * (m / 2 * ‖y - x₀‖ ^ 2) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht using key t ht.1 ht.2

/-- The core of **Lemma 1** of Chaudhuri–Monteleoni–Sarwate: if `G` and `G + g` are
`m`-strongly convex (`m > 0`) with minimizers `f₁` and `f₂`, and
`g(f₁) - g(f₂) ≤ L ‖f₁ - f₂‖` with `L ≥ 0`, then `‖f₁ - f₂‖ ≤ L / m`. -/
theorem norm_sub_le_of_sub_le (hG : StrongConvexOn univ m G)
    (hGg : StrongConvexOn univ m (G + g)) (hm : 0 < m) {f₁ f₂ : E} (h₁ : IsMinOn G univ f₁)
    (h₂ : IsMinOn (G + g) univ f₂) {L : ℝ} (hL : 0 ≤ L) (hg : g f₁ - g f₂ ≤ L * ‖f₁ - f₂‖) :
    ‖f₁ - f₂‖ ≤ L / m := by
  have a := mul_sq_norm_sub_le_of_isMinOn hG h₁ f₂
  have b := mul_sq_norm_sub_le_of_isMinOn hGg h₂ f₁
  rw [norm_sub_rev f₂ f₁] at a
  simp only [Pi.add_apply] at b
  rw [le_div_iff₀ hm]
  rcases (norm_nonneg (f₁ - f₂)).eq_or_lt with h | h
  · rwa [← h, zero_mul]
  · nlinarith

/-- **Lemma 1** of Chaudhuri–Monteleoni–Sarwate, derivative-free form: if `G` and `G + g` are
`m`-strongly convex (`m > 0`), `f₁` minimizes `G`, `f₂` minimizes `G + g`, and `g` is
`L`-Lipschitz, then `‖f₁ - f₂‖ ≤ L / m`. The paper assumes `G` and `g` differentiable with
`‖∇g‖ ≤ L` (`norm_sub_le_of_norm_gradient_le`); only the Lipschitz bound is needed here. -/
theorem norm_sub_le_of_lipschitzWith (hG : StrongConvexOn univ m G)
    (hGg : StrongConvexOn univ m (G + g)) (hm : 0 < m) {L : ℝ≥0} (hg : LipschitzWith L g)
    {f₁ f₂ : E} (h₁ : IsMinOn G univ f₁) (h₂ : IsMinOn (G + g) univ f₂) :
    ‖f₁ - f₂‖ ≤ L / m := by
  refine norm_sub_le_of_sub_le hG hGg hm h₁ h₂ L.2 ((le_abs_self _).trans ?_)
  simpa [Real.dist_eq, dist_eq_norm] using hg.dist_le_mul f₁ f₂

/-- A strongly convex function (`m > 0`) has at most one minimizer (the uniqueness part of
"a strictly convex function has a unique minimum", Section 2.2 of
Chaudhuri–Monteleoni–Sarwate, for strongly convex functions). -/
theorem eq_of_isMinOn_of_isMinOn (hF : StrongConvexOn univ m F) (hm : 0 < m) {x y : E}
    (hx : IsMinOn F univ x) (hy : IsMinOn F univ y) : x = y := by
  have h := mul_sq_norm_sub_le_of_isMinOn hF hx y
  have hyx := isMinOn_univ_iff.1 hy x
  have : ‖y - x‖ ^ 2 ≤ 0 := by nlinarith
  exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm this (sq_nonneg _))))).symm

/-- A strongly convex function (`m > 0`) on a finite-dimensional real normed space has a
minimizer. (It is continuous, being convex, and grows quadratically at infinity.) Not in
Chaudhuri–Monteleoni–Sarwate; it fails for merely strictly convex functions, such as `exp`. -/
theorem exists_isMinOn_of_strongConvexOn [FiniteDimensional ℝ E] (hF : StrongConvexOn univ m F)
    (hm : 0 < m) : ∃ x, IsMinOn F univ x := by
  have hcont : Continuous F := continuousOn_univ.1 <|
    (UniformConvexOn.convexOn hF fun r ↦ by positivity).continuousOn isOpen_univ
  obtain ⟨x₁, -, hx₁⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    (Metric.nonempty_closedBall.2 zero_le_one) hcont.continuousOn
  have hb : F x₁ ≤ F 0 := hx₁ (Metric.mem_closedBall_self zero_le_one)
  set R := 1 + 2 * (F 0 - F x₁) / m
  have hR : 1 ≤ R := by
    have : 0 ≤ 2 * (F 0 - F x₁) / m := div_nonneg (by linarith) hm.le
    linarith
  obtain ⟨x, hx⟩ := hcont.exists_forall_le' 0 <|
    (tendsto_norm_cocompact_atTop.eventually (Filter.eventually_ge_atTop R)).mono fun x hx ↦ by
      set r := ‖x‖ with hr_def
      have hr : 0 < r := by linarith
      have h₁ := hF.2 (mem_univ x) (mem_univ 0) (inv_nonneg.2 hr.le)
        (sub_nonneg.2 (inv_le_one_of_one_le₀ (hR.trans hx))) (add_sub_cancel r⁻¹ 1)
      simp only [smul_zero, add_zero, sub_zero, smul_eq_mul] at h₁
      have h₂ : F x₁ ≤ F (r⁻¹ • x) := hx₁ <| by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hr.ne']
      have h₃ : r * F x₁ ≤ F x + (r - 1) * F 0 - m / 2 * (r ^ 2 - r) := by
        have := mul_le_mul_of_nonneg_left (h₂.trans h₁) hr.le
        rw [← hr_def] at this
        field_simp at this
        linear_combination this / 2
      have h₄ : 2 * (F 0 - F x₁) ≤ (r - 1) * m :=
        (div_le_iff₀ hm).1 (by linarith)
      nlinarith
  exact ⟨x, isMinOn_univ_iff.2 hx⟩

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {G g : E → ℝ} {m : ℝ}

/-- **Lemma 1** of Chaudhuri–Monteleoni–Sarwate: let `G` and `G + g` be `m`-strongly convex
(`m > 0`), let `g` be differentiable with `‖∇g(f)‖ ≤ L` for all `f`, and let `f₁` minimize `G`
and `f₂` minimize `G + g`. Then `‖f₁ - f₂‖ ≤ L / m` (the paper's
`‖f₁ - f₂‖ ≤ (1/λ) max_f ‖∇g(f)‖`). The paper also assumes `G` continuous and differentiable;
this is not needed (see `norm_sub_le_of_lipschitzWith`). -/
theorem norm_sub_le_of_norm_gradient_le (hG : StrongConvexOn univ m G)
    (hGg : StrongConvexOn univ m (G + g)) (hm : 0 < m) (hgd : Differentiable ℝ g) {L : ℝ≥0}
    (hgL : ∀ f, ‖∇ g f‖ ≤ L) {f₁ f₂ : E} (h₁ : IsMinOn G univ f₁)
    (h₂ : IsMinOn (G + g) univ f₂) : ‖f₁ - f₂‖ ≤ L / m := by
  refine norm_sub_le_of_lipschitzWith hG hGg hm (lipschitzWith_of_nnnorm_fderiv_le hgd fun f ↦ ?_)
    h₁ h₂
  rw [← toDual_gradient, LinearIsometryEquiv.nnnorm_map, ← NNReal.coe_le_coe, coe_nnnorm]
  exact hgL f

end InnerProductSpace

/-! ### Regularized empirical risk minimization -/

section Objective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The **regularized empirical risk** (equation (1) of Chaudhuri–Monteleoni–Sarwate, for linear
predictors `f(x) = fᵀx` and a margin loss `ℓ(y fᵀx)` as in Section 3): for a dataset
`D = ((x₁, y₁), …, (xₙ, yₙ))` of `n` points of `E × ℝ`, a loss `ℓ : ℝ → ℝ`, a regularizer
`N : E → ℝ` and a regularization parameter `Λ`,
`J(f, D) = (1/n) ∑ᵢ ℓ(yᵢ ⟪xᵢ, f⟫) + Λ N(f)`. -/
noncomputable def objective (ℓ : ℝ → ℝ) (N : E → ℝ) (Λ : ℝ) (D : Fin n → E × ℝ) (f : E) : ℝ :=
  (∑ i, ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ)) / n + Λ * N f

variable {ℓ : ℝ → ℝ} {N : E → ℝ} {Λ : ℝ}

/-- `f ↦ ℓ(y ⟪x, f⟫)` is convex when `ℓ` is. -/
lemma convexOn_comp_inner (hℓ : ConvexOn ℝ univ ℓ) (x : E) (y : ℝ) :
    ConvexOn ℝ univ fun f ↦ ℓ (y * ⟪x, f⟫_ℝ) := by
  refine ⟨convex_univ, fun f _ f' _ a b ha hb hab ↦ ?_⟩
  have := hℓ.2 (mem_univ (y * ⟪x, f⟫_ℝ)) (mem_univ (y * ⟪x, f'⟫_ℝ)) ha hb hab
  simp only [inner_add_right, inner_smul_right, smul_eq_mul] at this ⊢
  convert this using 2
  ring

/-- If `N` is `1`-strongly convex and `Λ ≥ 0`, then `Λ N` is `Λ`-strongly convex. -/
lemma strongConvexOn_const_mul (hN : StrongConvexOn univ 1 N) (hΛ : 0 ≤ Λ) :
    StrongConvexOn univ Λ fun f ↦ Λ * N f := by
  refine ⟨convex_univ, fun f _ f' _ a b ha hb hab ↦ ?_⟩
  have := mul_le_mul_of_nonneg_left (hN.2 (mem_univ f) (mem_univ f') ha hb hab) hΛ
  simp only [smul_eq_mul] at this ⊢
  linarith

/-- The objective `J(·, D)` is `Λ`-strongly convex when `ℓ` is convex and `N` is `1`-strongly
convex (Section 3.3.1 of Chaudhuri–Monteleoni–Sarwate, proof of Corollary 1). -/
theorem strongConvexOn_objective (hℓ : ConvexOn ℝ univ ℓ) (hN : StrongConvexOn univ 1 N)
    (hΛ : 0 ≤ Λ) (D : Fin n → E × ℝ) : StrongConvexOn univ Λ (objective ℓ N Λ D) := by
  have hs (s : Finset (Fin n)) :
      ConvexOn ℝ univ fun f ↦ ∑ i ∈ s, ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ) := by
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) convex_univ
    | insert i s hi ih =>
      convert (convexOn_comp_inner hℓ (D i).1 (D i).2).add ih using 1
      funext f
      simp [Finset.sum_insert hi]
  have hloss : ConvexOn ℝ univ fun f ↦ (∑ i, ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ)) / n := by
    convert (hs Finset.univ).smul (inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) n)) using 1
    funext f
    simp [div_eq_inv_mul]
  have := (uniformConvexOn_zero.2 hloss).add (strongConvexOn_const_mul hN hΛ)
  rw [zero_add] at this
  exact this

/-- **Existence of the minimizer** of the objective in finite dimension: for `Λ > 0`, a convex
loss and a `1`-strongly convex regularizer, `J(·, D)` has a minimizer, unique by
`eq_of_isMinOn_of_isMinOn`. This is an addition: Section 2.2 of Chaudhuri–Monteleoni–Sarwate only
states that "a strictly convex function has a unique minimum", whose existence part fails for
strictly convex functions in general. -/
theorem exists_isMinOn_objective [FiniteDimensional ℝ E] (hΛ : 0 < Λ) (hℓ : ConvexOn ℝ univ ℓ)
    (hN : StrongConvexOn univ 1 N) (D : Fin n → E × ℝ) :
    ∃ f, IsMinOn (objective ℓ N Λ D) univ f :=
  exists_isMinOn_of_strongConvexOn (strongConvexOn_objective hℓ hN hΛ.le D) hΛ

/-- A loss term `f ↦ ℓ(y ⟪x, f⟫)` is `L`-Lipschitz when `ℓ` is, `‖x‖ ≤ 1` and `|y| ≤ 1`. -/
lemma abs_sub_le_of_lipschitzWith {L : ℝ≥0} (hℓ : LipschitzWith L ℓ) {x : E} {y : ℝ}
    (hx : ‖x‖ ≤ 1) (hy : |y| ≤ 1) (f f' : E) :
    |ℓ (y * ⟪x, f⟫_ℝ) - ℓ (y * ⟪x, f'⟫_ℝ)| ≤ L * ‖f - f'‖ := by
  have h := hℓ.dist_le_mul (y * ⟪x, f⟫_ℝ) (y * ⟪x, f'⟫_ℝ)
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, ← inner_sub_right, abs_mul] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ L.2)
  calc |y| * |⟪x, f - f'⟫_ℝ| ≤ 1 * (‖x‖ * ‖f - f'‖) :=
        mul_le_mul hy (abs_real_inner_le_norm _ _) (abs_nonneg _) zero_le_one
    _ ≤ ‖f - f'‖ := by
      rw [one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- For datasets that agree outside the entry `i`, the objectives differ by
`(1/n)(ℓ(y'ᵢ ⟪x'ᵢ, f⟫) - ℓ(yᵢ ⟪xᵢ, f⟫))`. -/
lemma objective_sub_objective {D D' : Fin n → E × ℝ} {i : Fin n} (h : ∀ j ≠ i, D j = D' j)
    (f : E) : objective ℓ N Λ D' f - objective ℓ N Λ D f =
      (ℓ ((D' i).2 * ⟪(D' i).1, f⟫_ℝ) - ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ)) / n := by
  simp only [objective]
  rw [add_sub_add_right_eq_sub, ← sub_div, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single i (fun j _ hj ↦ by rw [h j hj, sub_self]) (by simp)]

/-- **Corollary 1** of Chaudhuri–Monteleoni–Sarwate for `L`-Lipschitz losses, with the changed
entry explicit: let `n > 0`, `Λ > 0`, `ℓ` convex and `L`-Lipschitz, `N` `1`-strongly convex, and
let `D, D'` agree outside the entry `i`, whose feature vectors satisfy `‖xᵢ‖, ‖x'ᵢ‖ ≤ 1` and
labels `|yᵢ|, |y'ᵢ| ≤ 1`. Then the minimizers `f₁` of `J(·, D)` and `f₂` of `J(·, D')` satisfy
`‖f₁ - f₂‖ ≤ 2L / (nΛ)`. Neither `ℓ` nor `N` needs to be differentiable. -/
theorem norm_sub_le_of_forall_ne_eq (hn : 0 < n) (hΛ : 0 < Λ) (hℓc : ConvexOn ℝ univ ℓ)
    {L : ℝ≥0} (hℓ : LipschitzWith L ℓ) (hN : StrongConvexOn univ 1 N) {D D' : Fin n → E × ℝ}
    {i : Fin n} (hDD' : ∀ j ≠ i, D j = D' j) (hx : ‖(D i).1‖ ≤ 1) (hy : |(D i).2| ≤ 1)
    (hx' : ‖(D' i).1‖ ≤ 1) (hy' : |(D' i).2| ≤ 1) {f₁ f₂ : E}
    (h₁ : IsMinOn (objective ℓ N Λ D) univ f₁) (h₂ : IsMinOn (objective ℓ N Λ D') univ f₂) :
    ‖f₁ - f₂‖ ≤ 2 * L / (n * Λ) := by
  set g := fun f ↦ objective ℓ N Λ D' f - objective ℓ N Λ D f
  have hGg : objective ℓ N Λ D + g = objective ℓ N Λ D' := by
    funext f
    simp [g]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : StrongConvexOn univ Λ (objective ℓ N Λ D + g) := by
    rw [hGg]
    exact strongConvexOn_objective hℓc hN hΛ.le D'
  have h₂' : IsMinOn (objective ℓ N Λ D + g) univ f₂ := by rwa [hGg]
  have key := norm_sub_le_of_sub_le (strongConvexOn_objective hℓc hN hΛ.le D) hc hΛ h₁ h₂'
    (L := 2 * L / n) (by positivity) ?_
  · rwa [div_div] at key
  · have a := abs_le.1 (abs_sub_le_of_lipschitzWith hℓ hx' hy' f₁ f₂)
    have b := abs_le.1 (abs_sub_le_of_lipschitzWith hℓ hx hy f₁ f₂)
    simp only [g, objective_sub_objective hDD']
    rw [div_sub_div_same, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn']
    linarith [a.2, b.1]

/-- Neighbouring datasets: if `hammingDist D D' ≤ 1` (`D` and `D'` differ in at most one entry),
then there is an entry `i` outside of which they agree. -/
lemma exists_forall_ne_eq_of_hammingDist_le_one {V : Type*} [DecidableEq V] (hn : 0 < n)
    {D D' : Fin n → V} (h : hammingDist D D' ≤ 1) : ∃ i, ∀ j ≠ i, D j = D' j := by
  by_cases hex : ∃ i, D i ≠ D' i
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, fun j hj ↦ ?_⟩
    by_contra hne
    exact hj (Finset.card_le_one.1 h j (by simpa using hne) i (by simpa using hi))
  · push Not at hex
    exact ⟨⟨0, hn⟩, fun j _ ↦ hex j⟩

/-- **Corollary 1** of Chaudhuri–Monteleoni–Sarwate for `L`-Lipschitz losses: let `n > 0`,
`Λ > 0`, `ℓ` convex and `L`-Lipschitz, `N` `1`-strongly convex, and let `D, D'` be datasets of
points `(x, y)` with `‖x‖ ≤ 1`, `|y| ≤ 1` that differ in at most one entry. Then the minimizers
`f₁` of `J(·, D)` and `f₂` of `J(·, D')` satisfy `‖f₁ - f₂‖ ≤ 2L / (nΛ)`: the `L₂`-sensitivity of
regularized ERM is at most `2L / (nΛ)`. -/
theorem norm_sub_le_of_hammingDist_le_one [DecidableEq E] (hn : 0 < n) (hΛ : 0 < Λ)
    (hℓc : ConvexOn ℝ univ ℓ) {L : ℝ≥0} (hℓ : LipschitzWith L ℓ) (hN : StrongConvexOn univ 1 N)
    {D D' : Fin n → E × ℝ} (hD : ∀ i, ‖(D i).1‖ ≤ 1 ∧ |(D i).2| ≤ 1)
    (hD' : ∀ i, ‖(D' i).1‖ ≤ 1 ∧ |(D' i).2| ≤ 1) (hDD' : hammingDist D D' ≤ 1) {f₁ f₂ : E}
    (h₁ : IsMinOn (objective ℓ N Λ D) univ f₁) (h₂ : IsMinOn (objective ℓ N Λ D') univ f₂) :
    ‖f₁ - f₂‖ ≤ 2 * L / (n * Λ) := by
  obtain ⟨i, hi⟩ := exists_forall_ne_eq_of_hammingDist_le_one hn hDD'
  exact norm_sub_le_of_forall_ne_eq hn hΛ hℓc hℓ hN hi (hD i).1 (hD i).2 (hD' i).1 (hD' i).2 h₁ h₂

/-- A differentiable `ℓ : ℝ → ℝ` with `|ℓ'| ≤ 1` is `1`-Lipschitz. -/
lemma lipschitzWith_one_of_abs_deriv_le {ℓ : ℝ → ℝ} (hℓd : Differentiable ℝ ℓ)
    (hℓ' : ∀ z, |deriv ℓ z| ≤ 1) : LipschitzWith 1 ℓ :=
  lipschitzWith_of_nnnorm_deriv_le hℓd fun z ↦ by
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact hℓ' z

/-- **Corollary 1** of Chaudhuri–Monteleoni–Sarwate: if `N` is `1`-strongly convex and `ℓ` is
convex and differentiable with `|ℓ'(z)| ≤ 1` for all `z`, then for `n > 0`, `Λ > 0` and datasets
`D, D'` of points `(x, y)` with `‖x‖ ≤ 1`, `|y| ≤ 1` that differ in at most one entry, the
minimizers `f₁` of `J(·, D)` and `f₂` of `J(·, D')` satisfy `‖f₁ - f₂‖ ≤ 2 / (nΛ)`. The paper also
assumes `N` differentiable; this is not needed. -/
theorem norm_sub_le_two_div_of_hammingDist_le_one [DecidableEq E] (hn : 0 < n) (hΛ : 0 < Λ)
    (hℓc : ConvexOn ℝ univ ℓ) (hℓd : Differentiable ℝ ℓ) (hℓ' : ∀ z, |deriv ℓ z| ≤ 1)
    (hN : StrongConvexOn univ 1 N) {D D' : Fin n → E × ℝ}
    (hD : ∀ i, ‖(D i).1‖ ≤ 1 ∧ |(D i).2| ≤ 1) (hD' : ∀ i, ‖(D' i).1‖ ≤ 1 ∧ |(D' i).2| ≤ 1)
    (hDD' : hammingDist D D' ≤ 1) {f₁ f₂ : E} (h₁ : IsMinOn (objective ℓ N Λ D) univ f₁)
    (h₂ : IsMinOn (objective ℓ N Λ D') univ f₂) : ‖f₁ - f₂‖ ≤ 2 / (n * Λ) := by
  simpa using norm_sub_le_of_hammingDist_le_one hn hΛ hℓc
    (lipschitzWith_one_of_abs_deriv_le hℓd hℓ') hN hD hD' hDD' h₁ h₂

/-- **Continuity of regularized ERM in the data**: for `n > 0`, `Λ > 0`, a convex `L`-Lipschitz
loss and a `1`-strongly convex regularizer, any choice `D ↦ A(D)` of minimizers of `J(·, D)` is
continuous on the space of all datasets (by the quadratic growth bound
`Λ ‖A D₀ - A D‖² ≤ (L/n) ∑ᵢ ‖yᵢ xᵢ - y⁰ᵢ x⁰ᵢ‖ (‖A D₀‖ + ‖A D‖)`). Not in the paper; it makes
Algorithm 1 a measurable mechanism. -/
theorem continuous_of_isMinOn_objective (hn : 0 < n) (hΛ : 0 < Λ) (hℓc : ConvexOn ℝ univ ℓ)
    {L : ℝ≥0} (hℓ : LipschitzWith L ℓ) (hN : StrongConvexOn univ 1 N)
    {A : (Fin n → E × ℝ) → E} (hA : ∀ D, IsMinOn (objective ℓ N Λ D) univ (A D)) :
    Continuous A := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set δ : (Fin n → E × ℝ) → (Fin n → E × ℝ) → ℝ := fun D₀ D ↦
    L / n * ∑ i, ‖(D i).2 • (D i).1 - (D₀ i).2 • (D₀ i).1‖ with hδ_def
  have hδ₀ (D₀ D) : 0 ≤ δ D₀ D := by positivity
  have hg (D₀ D : Fin n → E × ℝ) (f : E) :
      |objective ℓ N Λ D f - objective ℓ N Λ D₀ f| ≤ δ D₀ D * ‖f‖ := by
    have h₁ : objective ℓ N Λ D f - objective ℓ N Λ D₀ f =
        (∑ i, (ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ) - ℓ ((D₀ i).2 * ⟪(D₀ i).1, f⟫_ℝ))) / n := by
      simp only [objective, Finset.sum_sub_distrib]
      ring
    have h₂ (i : Fin n) : |ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ) - ℓ ((D₀ i).2 * ⟪(D₀ i).1, f⟫_ℝ)| ≤
        L * (‖(D i).2 • (D i).1 - (D₀ i).2 • (D₀ i).1‖ * ‖f‖) := by
      have := hℓ.dist_le_mul ((D i).2 * ⟪(D i).1, f⟫_ℝ) ((D₀ i).2 * ⟪(D₀ i).1, f⟫_ℝ)
      have e : (D i).2 * ⟪(D i).1, f⟫_ℝ - (D₀ i).2 * ⟪(D₀ i).1, f⟫_ℝ =
          ⟪(D i).2 • (D i).1 - (D₀ i).2 • (D₀ i).1, f⟫_ℝ := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      rw [Real.dist_eq, Real.dist_eq, e] at this
      exact this.trans (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) L.2)
    rw [h₁, abs_div, abs_of_pos hn', div_le_iff₀ hn']
    calc |∑ i, (ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ) - ℓ ((D₀ i).2 * ⟪(D₀ i).1, f⟫_ℝ))|
        ≤ ∑ i, |ℓ ((D i).2 * ⟪(D i).1, f⟫_ℝ) - ℓ ((D₀ i).2 * ⟪(D₀ i).1, f⟫_ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, L * (‖(D i).2 • (D i).1 - (D₀ i).2 • (D₀ i).1‖ * ‖f‖) :=
          Finset.sum_le_sum fun i _ ↦ h₂ i
      _ = δ D₀ D * ‖f‖ * n := by
        rw [hδ_def, ← Finset.mul_sum, ← Finset.sum_mul]
        field_simp
  have key (D₀ D : Fin n → E × ℝ) :
      Λ * ‖A D₀ - A D‖ ^ 2 ≤ δ D₀ D * (‖A D₀‖ + ‖A D‖) := by
    have a := mul_sq_norm_sub_le_of_isMinOn (strongConvexOn_objective hℓc hN hΛ.le D₀) (hA D₀)
      (A D)
    have b := mul_sq_norm_sub_le_of_isMinOn (strongConvexOn_objective hℓc hN hΛ.le D) (hA D)
      (A D₀)
    rw [norm_sub_rev (A D) (A D₀)] at a
    have c := abs_le.1 (hg D₀ D (A D₀))
    have d := abs_le.1 (hg D₀ D (A D))
    nlinarith [c.2, d.1]
  refine continuous_iff_continuousAt.2 fun D₀ ↦ Metric.tendsto_nhds.2 fun η hη ↦ ?_
  have hδc : Continuous (δ D₀) := by
    rw [hδ_def]
    fun_prop
  have hpos : 0 < Λ * η ^ 2 / (2 * ‖A D₀‖ + η) := by positivity
  have hδ0 : δ D₀ D₀ = 0 := by simp [hδ_def]
  filter_upwards [(hδc.tendsto D₀).eventually (gt_mem_nhds (hδ0 ▸ hpos))] with D hD
  rw [dist_comm, dist_eq_norm]
  by_contra! hu
  have hk := key D₀ D
  have hAD : ‖A D‖ ≤ ‖A D₀‖ + ‖A D₀ - A D‖ := by
    calc ‖A D‖ = ‖A D₀ - (A D₀ - A D)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A D₀‖ + ‖A D₀ - A D‖ := norm_sub_le _ _
  rw [lt_div_iff₀ (by positivity)] at hD
  have hδη : δ D₀ D ≤ Λ * η := by
    have : δ D₀ D * η < Λ * η ^ 2 := by nlinarith [hδ₀ D₀ D, norm_nonneg (A D₀)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hδη (sub_nonneg.2 hu), hδ₀ D₀ D,
    mul_le_mul_of_nonneg_left hAD (hδ₀ D₀ D),
    mul_nonneg (mul_nonneg hΛ.le (hη.le.trans hu)) (sub_nonneg.2 hu)]

/-- The **regularized ERM solution** `argmin_f J(f, D)`: a minimizer of `J(·, D)`, chosen by
`Classical.epsilon` (it is a minimizer whenever one exists). Under the hypotheses of
Corollary 1 of Chaudhuri–Monteleoni–Sarwate it is the unique minimizer (`isMinOn_erm`,
`eq_of_isMinOn_of_isMinOn`). -/
noncomputable def erm (ℓ : ℝ → ℝ) (N : E → ℝ) (Λ : ℝ) (D : Fin n → E × ℝ) : E :=
  Classical.epsilon fun f ↦ IsMinOn (objective ℓ N Λ D) univ f

/-- In finite dimension, `erm ℓ N Λ D` minimizes `J(·, D)` (for `Λ > 0`, a convex loss and a
`1`-strongly convex regularizer). -/
theorem isMinOn_erm [FiniteDimensional ℝ E] (hΛ : 0 < Λ) (hℓ : ConvexOn ℝ univ ℓ)
    (hN : StrongConvexOn univ 1 N) (D : Fin n → E × ℝ) :
    IsMinOn (objective ℓ N Λ D) univ (erm ℓ N Λ D) :=
  Classical.epsilon_spec (exists_isMinOn_objective hΛ hℓ hN D)

end Objective

section OutputPerturbation

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The noise distribution -/

variable (E) in
/-- The normalizing constant `α = ∫ e^{-β‖b‖} db` of the noise density `ν(b) = e^{-β‖b‖} / α` of
equation (7) of Chaudhuri–Monteleoni–Sarwate, with respect to Lebesgue measure on `E` (for
example `E = EuclideanSpace ℝ (Fin d)`, i.e. `ℝ^d`). It is finite and nonzero for `β > 0`
(`noiseConst_ne_top`, `noiseConst_ne_zero`). -/
noncomputable def noiseConst (β : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ b : E, ENNReal.ofReal (exp (-(β * ‖b‖)))

/-- `b ↦ e^{-β‖b‖}` is integrable on a finite-dimensional space for `β > 0`. -/
lemma integrable_exp_neg_mul_norm {β : ℝ} (hβ : 0 < β) :
    Integrable fun b : E ↦ exp (-(β * ‖b‖)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsFiniteMeasure (volume : Measure E) := inferInstance
    exact (integrable_const (1 : ℝ)).congr (ae_of_all _ fun b ↦ by
      simp [Subsingleton.elim b 0])
  · refine (integrable_fun_norm_addHaar volume (f := fun t ↦ exp (-(β * t)))).2 ?_
    have hs : (-1 : ℝ) < (Module.finrank ℝ E - 1 : ℕ) := by
      have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E - 1)
      linarith
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow hs zero_lt_one hβ).congr_fun
      (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
    simp [Real.rpow_natCast, Real.rpow_one]

lemma noiseConst_ne_top {β : ℝ≥0} (hβ : 0 < β) : noiseConst E β ≠ ∞ :=
  (integrable_exp_neg_mul_norm (E := E) (NNReal.coe_pos.2 hβ)).lintegral_lt_top.ne

lemma noiseConst_ne_zero (β : ℝ≥0) : noiseConst E β ≠ 0 := by
  refine ((lintegral_pos_iff_support ?_).2 ?_).ne'
  · fun_prop
  · have : Function.support (fun b : E ↦ ENNReal.ofReal (exp (-(β * ‖b‖)))) = univ :=
      eq_univ_of_forall fun b ↦ by simp [exp_pos]
    rw [this, Measure.measure_univ_pos]
    exact NeZero.ne _

/-- **Output perturbation** with noise density `ν(b) = e^{-β‖b‖} / α` (equation (7) and
Algorithm 1 of Chaudhuri–Monteleoni–Sarwate): the kernel sending `c ∈ E` to the distribution of
`c + b`, where `b` has density `ν` with respect to Lebesgue measure; that is, `c` is sent to the
measure with density `z ↦ e^{-β‖z - c‖} / α` (`outputPerturbation_apply`). It is the Laplace
mechanism `MetricDP.laplaceMech` of `(E, β ‖· - ·‖)` with constant scaling function `1 / α`, and
a Markov kernel for `β > 0` (`isMarkovKernel_outputPerturbation`). -/
noncomputable def outputPerturbation (β : ℝ≥0) : Kernel E E :=
  MetricDP.laplaceMech volume (fun _ ↦ (noiseConst E β)⁻¹) fun c z ↦ β * edist c z

lemma outputPerturbation_apply (β : ℝ≥0) (c : E) :
    outputPerturbation β c =
      volume.withDensity fun z ↦ (noiseConst E β)⁻¹ * ENNReal.ofReal (exp (-(β * ‖z - c‖))) := by
  rw [outputPerturbation, MetricDP.laplaceMech, Kernel.withDensity_apply _
    ((measurable_const.comp measurable_snd).mul (MetricDP.measurable_expNeg.comp
      (measurable_const.mul measurable_edist))), Kernel.const_apply]
  congr 1
  funext z
  rw [MetricDP.expNeg_of_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top c z)),
    ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    dist_comm, dist_eq_norm]

/-- Output perturbation releases `c + b`: `outputPerturbation β c` is the image of the noise
distribution `outputPerturbation β 0` (density `e^{-β‖b‖} / α`) under `b ↦ c + b`. -/
lemma outputPerturbation_eq_map (β : ℝ≥0) (c : E) :
    outputPerturbation β c = (outputPerturbation β 0).map (c + ·) := by
  ext s hs
  have hf : Measurable fun z : E ↦ (noiseConst E β)⁻¹ * ENNReal.ofReal (exp (-(β * ‖z - c‖))) := by
    fun_prop
  rw [Measure.map_apply (measurable_const_add c) hs, outputPerturbation_apply,
    outputPerturbation_apply, withDensity_apply _ hs,
    withDensity_apply _ (measurable_const_add c hs),
    ← (measurePreserving_add_left volume c).setLIntegral_comp_preimage hs hf]
  simp

/-- Output perturbation is a Markov kernel for `β > 0`: the density `e^{-β‖b‖} / α` of
equation (7) of Chaudhuri–Monteleoni–Sarwate is a probability density. -/
theorem isMarkovKernel_outputPerturbation {β : ℝ≥0} (hβ : 0 < β) :
    IsMarkovKernel (outputPerturbation (E := E) β) := by
  refine ⟨fun c ↦ ⟨?_⟩⟩
  rw [outputPerturbation_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_const_mul _ (by fun_prop),
    lintegral_sub_right_eq_self (fun z ↦ ENNReal.ofReal (exp (-(β * ‖z‖)))) c]
  exact ENNReal.inv_mul_cancel (noiseConst_ne_zero β) (noiseConst_ne_top hβ)

/-- **Privacy of output perturbation in metric form** (the computation (10)–(11) in the proof of
Theorem 1 of Chaudhuri–Monteleoni–Sarwate, an instance of Fact 7 of Chatzikokolakis–Andrés–
Bordenabe–Palamidessi): for `β > 0`, output perturbation is a Markov kernel and, for all centres
`c, c'` and events `S`, `P(c + b ∈ S) ≤ e^{β‖c - c'‖} P(c' + b ∈ S)`. (The inequality holds for
every `β`, but at `β = 0` the kernel is `0` and it is vacuous.) -/
theorem isMetricDP_outputPerturbation {β : ℝ≥0} (hβ : 0 < β) :
    IsMarkovKernel (outputPerturbation (E := E) β) ∧
      IsMetricDP (outputPerturbation (E := E) β) fun c c' ↦ β * edist c c' :=
  ⟨isMarkovKernel_outputPerturbation hβ,
    MetricDP.isMetricDP_laplaceMech_edist volume measurable_const β⟩

/-- The likelihood-ratio bound of the sensitivity method, for every `β` (vacuous at `β = 0`). -/
private lemma le_smul_of_norm_sub_le {β : ℝ≥0} {c c' : E} {Δ ε : ℝ} (hcc' : ‖c - c'‖ ≤ Δ)
    (hβ : β * Δ ≤ ε) :
    outputPerturbation β c ≤ ENNReal.ofReal (exp ε) • outputPerturbation β c' := by
  refine (MetricDP.isMetricDP_laplaceMech_edist volume measurable_const β
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top c c'))).trans <|
      MetricDP.smul_le_smul_of_le (ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)) _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    dist_eq_norm]
  exact (mul_le_mul_of_nonneg_left hcc' β.2).trans hβ

/-- **The sensitivity method with `ℓ₂` noise** (Section 3.1 of Chaudhuri–Monteleoni–Sarwate,
after Dwork–McSherry–Nissim–Smith): for `β > 0`, output perturbation is a Markov kernel, and if
`‖c - c'‖ ≤ Δ` and `β Δ ≤ ε`, then the output distributions satisfy
`P(c + b ∈ S) ≤ e^ε P(c' + b ∈ S)` for every set `S`. -/
theorem outputPerturbation_le_smul {β : ℝ≥0} (hβ : 0 < β) {c c' : E} {Δ ε : ℝ}
    (hcc' : ‖c - c'‖ ≤ Δ) (hβε : β * Δ ≤ ε) :
    IsMarkovKernel (outputPerturbation (E := E) β) ∧
      outputPerturbation β c ≤ ENNReal.ofReal (exp ε) • outputPerturbation β c' :=
  ⟨isMarkovKernel_outputPerturbation hβ, le_smul_of_norm_sub_le hcc' hβε⟩

/-- **The sensitivity method with `ℓ₂` noise is `ε`-differentially private** (Section 3.1 of
Chaudhuri–Monteleoni–Sarwate): if a measurable `A : 𝒟 → E` has `L₂`-sensitivity at most `Δ`
for the neighbouring relation `Adj` (Definition 5) and `β > 0` satisfies `β Δ ≤ ε`, then
`D ↦ A(D) + b`, with `b` of density `∝ e^{-β‖b‖}`, is `ε`-differentially private. -/
theorem isEpsDP_comap_outputPerturbation {𝒟 : Type*} [MeasurableSpace 𝒟] {A : 𝒟 → E}
    (hA : Measurable A) {Adj : 𝒟 → 𝒟 → Prop} {Δ ε : ℝ}
    (hsens : ∀ ⦃D D'⦄, Adj D D' → ‖A D - A D'‖ ≤ Δ) {β : ℝ≥0} (hβ : 0 < β) (hβε : β * Δ ≤ ε) :
    IsEpsDP ((outputPerturbation β).comap A hA) Adj ε := by
  have := isMarkovKernel_outputPerturbation (E := E) hβ
  refine isEpsDP_iff_le_smul.2 fun D D' hD ↦ ?_
  rw [Kernel.comap_apply, Kernel.comap_apply]
  exact le_smul_of_norm_sub_le (hsens hD) hβε

end OutputPerturbation

/-! ### Theorem 1: regularized ERM with output perturbation is differentially private -/

section Theorem1

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [DecidableEq E] {n : ℕ} {ℓ : ℝ → ℝ} {N : E → ℝ} {Λ ε : ℝ}

/-- The neighbouring relation of Section 2.3 of Chaudhuri–Monteleoni–Sarwate: datasets of `n`
points `(x, y)` with `‖x‖ ≤ 1` and `|y| ≤ 1` that differ in exactly one entry
(`MetricDP.HammingAdj`). -/
def Neighbour (D D' : Fin n → E × ℝ) : Prop :=
  (∀ i, ‖(D i).1‖ ≤ 1 ∧ |(D i).2| ≤ 1) ∧ (∀ i, ‖(D' i).1‖ ≤ 1 ∧ |(D' i).2| ≤ 1) ∧
    MetricDP.HammingAdj D D'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The neighbouring relation is symmetric. -/
lemma Neighbour.symm {D D' : Fin n → E × ℝ} (h : Neighbour D D') : Neighbour D' D := by
  have h₃ := h.2.2
  unfold MetricDP.HammingAdj at h₃
  exact ⟨h.2.1, h.1, by rw [MetricDP.HammingAdj, hammingDist_comm, h₃]⟩

/-- **Output perturbation of regularized ERM with an `L`-Lipschitz loss** (generalizing Theorem 1
of Chaudhuri–Monteleoni–Sarwate from `L = 1`): under the hypotheses of Corollary 1 for an
`L`-Lipschitz convex loss, if `β · 2L / (nΛ) ≤ ε`, then for neighbouring datasets `D, D'` and the
minimizers `f₁` of `J(·, D)` and `f₂` of `J(·, D')`, the output distributions of `f₁ + b` and
`f₂ + b` satisfy `P(f₁ + b ∈ S) ≤ e^ε P(f₂ + b ∈ S)` for every set `S`; for `β > 0` the
mechanism is a Markov kernel. -/
theorem outputPerturbation_le_smul_of_lipschitzWith (hn : 0 < n) (hΛ : 0 < Λ)
    (hℓc : ConvexOn ℝ univ ℓ) {L : ℝ≥0} (hℓ : LipschitzWith L ℓ) (hN : StrongConvexOn univ 1 N)
    {D D' : Fin n → E × ℝ} (hDD' : Neighbour D D') {f₁ f₂ : E}
    (h₁ : IsMinOn (objective ℓ N Λ D) univ f₁) (h₂ : IsMinOn (objective ℓ N Λ D') univ f₂)
    {β : ℝ≥0} (hβ : 0 < β) (hβε : β * (2 * L / (n * Λ)) ≤ ε) :
    IsMarkovKernel (outputPerturbation (E := E) β) ∧
      outputPerturbation β f₁ ≤ ENNReal.ofReal (exp ε) • outputPerturbation β f₂ :=
  outputPerturbation_le_smul hβ (norm_sub_le_of_hammingDist_le_one hn hΛ hℓc hℓ hN hDD'.1
    hDD'.2.1 hDD'.2.2.le h₁ h₂) hβε

/-- **Theorem 1** of Chaudhuri–Monteleoni–Sarwate (Algorithm 1, ERM with output perturbation,
satisfies Definition 3 of `ε`-differential privacy), for the output distributions: let `N` be
`1`-strongly convex, `ℓ` convex and differentiable with `|ℓ'(z)| ≤ 1`, `n > 0`, `Λ > 0`,
`ε > 0`, and `β = nΛε/2`. For neighbouring datasets `D, D'` (`Neighbour`) with minimizers `f₁`
of `J(·, D)` and `f₂` of `J(·, D')`, the outputs `f₁ + b` and `f₂ + b` of Algorithm 1, with `b` of
density `∝ e^{-β‖b‖}`, satisfy `P(f₁ + b ∈ S) ≤ e^ε P(f₂ + b ∈ S)` for every set `S` (and, `D`
and `D'` playing symmetric roles, the reverse inequality). The paper also assumes `N`
differentiable; this is not needed. -/
theorem outputPerturbation_le_smul_of_neighbour (hn : 0 < n) (hΛ : 0 < Λ) (hε : 0 < ε)
    (hℓc : ConvexOn ℝ univ ℓ) (hℓd : Differentiable ℝ ℓ) (hℓ' : ∀ z, |deriv ℓ z| ≤ 1)
    (hN : StrongConvexOn univ 1 N) {D D' : Fin n → E × ℝ} (hDD' : Neighbour D D') {f₁ f₂ : E}
    (h₁ : IsMinOn (objective ℓ N Λ D) univ f₁) (h₂ : IsMinOn (objective ℓ N Λ D') univ f₂) :
    outputPerturbation (n * Λ * ε / 2).toNNReal f₁ ≤
      ENNReal.ofReal (exp ε) • outputPerturbation (n * Λ * ε / 2).toNNReal f₂ := by
  refine le_smul_of_norm_sub_le (norm_sub_le_two_div_of_hammingDist_le_one hn hΛ hℓc hℓd hℓ'
    hN hDD'.1 hDD'.2.1 hDD'.2.2.le h₁ h₂) (le_of_eq ?_)
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Real.coe_toNNReal _ (by positivity)]
  field_simp

omit [DecidableEq E] in
/-- Any choice `D ↦ A(D)` of minimizers of `J(·, D)` is measurable (it is continuous,
`continuous_of_isMinOn_objective`). -/
theorem measurable_of_isMinOn_objective (hn : 0 < n) (hΛ : 0 < Λ) (hℓc : ConvexOn ℝ univ ℓ)
    {L : ℝ≥0} (hℓ : LipschitzWith L ℓ) (hN : StrongConvexOn univ 1 N)
    {A : (Fin n → E × ℝ) → E} (hA : ∀ D, IsMinOn (objective ℓ N Λ D) univ (A D)) :
    Measurable A :=
  (continuous_of_isMinOn_objective hn hΛ hℓc hℓ hN hA).measurable

omit [DecidableEq E] in
/-- The regularized ERM solution `D ↦ argmin J(·, D)` is measurable. -/
theorem measurable_erm (hn : 0 < n) (hΛ : 0 < Λ) (hℓc : ConvexOn ℝ univ ℓ) {L : ℝ≥0}
    (hℓ : LipschitzWith L ℓ) (hN : StrongConvexOn univ 1 N) : Measurable (erm (n := n) ℓ N Λ) :=
  measurable_of_isMinOn_objective hn hΛ hℓc hℓ hN (isMinOn_erm hΛ hℓc hN)

/-- **Theorem 1** of Chaudhuri–Monteleoni–Sarwate (Algorithm 1, ERM with output perturbation, is
`ε`-differentially private), kernel form: let `N` be `1`-strongly convex, `ℓ` convex and
differentiable with `|ℓ'(z)| ≤ 1`, `n > 0`, `Λ > 0` and `ε > 0`, and let `A` send each dataset
`D` to a minimizer of `J(·, D)` (in finite dimension one exists, `exists_isMinOn_objective`, and
it is unique, `eq_of_isMinOn_of_isMinOn`; `A` is then measurable,
`measurable_of_isMinOn_objective`). Then the mechanism `D ↦ A(D) + b`, with `b` of density
`∝ e^{-(nΛε/2)‖b‖}`, is a Markov kernel and is `ε`-differentially private (`IsEpsDP`) for the
neighbouring relation `Neighbour`. The paper also assumes `N` differentiable; this is not
needed. -/
theorem isEpsDP_outputPerturbation_comap (hn : 0 < n) (hΛ : 0 < Λ) (hε : 0 < ε)
    (hℓc : ConvexOn ℝ univ ℓ) (hℓd : Differentiable ℝ ℓ) (hℓ' : ∀ z, |deriv ℓ z| ≤ 1)
    (hN : StrongConvexOn univ 1 N) {A : (Fin n → E × ℝ) → E}
    (hA : ∀ D, IsMinOn (objective ℓ N Λ D) univ (A D)) :
    IsMarkovKernel ((outputPerturbation (n * Λ * ε / 2).toNNReal).comap A
        (measurable_of_isMinOn_objective hn hΛ hℓc (lipschitzWith_one_of_abs_deriv_le hℓd hℓ') hN
          hA)) ∧
      IsEpsDP ((outputPerturbation (n * Λ * ε / 2).toNNReal).comap A
        (measurable_of_isMinOn_objective hn hΛ hℓc (lipschitzWith_one_of_abs_deriv_le hℓd hℓ') hN
          hA)) Neighbour ε := by
  have := isMarkovKernel_outputPerturbation (E := E)
    (Real.toNNReal_pos.2 (by positivity : 0 < n * Λ * ε / 2))
  refine ⟨inferInstance, isEpsDP_iff_le_smul.2 fun D D' hD ↦ ?_⟩
  rw [Kernel.comap_apply, Kernel.comap_apply]
  exact outputPerturbation_le_smul_of_neighbour hn hΛ hε hℓc hℓd hℓ' hN hD (hA D) (hA D')

/-- **Theorem 1** of Chaudhuri–Monteleoni–Sarwate for Algorithm 1 itself: under the hypotheses of
`isEpsDP_outputPerturbation_comap`, the mechanism `D ↦ argmin J(·, D) + b` (`erm`), with `b` of
density `∝ e^{-(nΛε/2)‖b‖}`, is a Markov kernel and is `ε`-differentially private for
`Neighbour`. -/
theorem isEpsDP_outputPerturbation_comap_erm (hn : 0 < n) (hΛ : 0 < Λ) (hε : 0 < ε)
    (hℓc : ConvexOn ℝ univ ℓ) (hℓd : Differentiable ℝ ℓ) (hℓ' : ∀ z, |deriv ℓ z| ≤ 1)
    (hN : StrongConvexOn univ 1 N) :
    IsMarkovKernel ((outputPerturbation (n * Λ * ε / 2).toNNReal).comap (erm ℓ N Λ)
        (measurable_erm hn hΛ hℓc (lipschitzWith_one_of_abs_deriv_le hℓd hℓ') hN)) ∧
      IsEpsDP ((outputPerturbation (n * Λ * ε / 2).toNNReal).comap (erm ℓ N Λ)
        (measurable_erm hn hΛ hℓc (lipschitzWith_one_of_abs_deriv_le hℓd hℓ') hN)) Neighbour ε :=
  isEpsDP_outputPerturbation_comap hn hΛ hε hℓc hℓd hℓ' hN (isMinOn_erm hΛ hℓc hN)

/-- **Theorem 1** of Chaudhuri–Monteleoni–Sarwate in the two-sided form of Definition 3,
equation (5): under the hypotheses of `isEpsDP_outputPerturbation_comap`, for neighbouring
datasets `D, D'` and every set `S`, the output `f_priv(D) = argmin J(·, D) + b` of Algorithm 1
satisfies `e^{-ε} P(f_priv(D') ∈ S) ≤ P(f_priv(D) ∈ S) ≤ e^ε P(f_priv(D') ∈ S)`. -/
theorem measureReal_outputPerturbation_erm_mem_Icc (hn : 0 < n) (hΛ : 0 < Λ) (hε : 0 < ε)
    (hℓc : ConvexOn ℝ univ ℓ) (hℓd : Differentiable ℝ ℓ) (hℓ' : ∀ z, |deriv ℓ z| ≤ 1)
    (hN : StrongConvexOn univ 1 N) {D D' : Fin n → E × ℝ} (hDD' : Neighbour D D')
    (S : Set E) :
    (outputPerturbation (n * Λ * ε / 2).toNNReal (erm ℓ N Λ D)).real S ∈
      Icc (exp (-ε) * (outputPerturbation (n * Λ * ε / 2).toNNReal (erm ℓ N Λ D')).real S)
        (exp ε * (outputPerturbation (n * Λ * ε / 2).toNNReal (erm ℓ N Λ D')).real S) := by
  have h := (isEpsDP_outputPerturbation_comap_erm hn hΛ hε hℓc hℓd hℓ' hN).2
  have h₁ := isEpsDP_iff.1 h hDD' S
  have h₂ := isEpsDP_iff.1 h hDD'.symm S
  simp only [Kernel.comap_apply] at h₁ h₂
  refine ⟨?_, h₁⟩
  rw [exp_neg, inv_mul_le_iff₀ (exp_pos ε)]
  exact h₂

end Theorem1

/-! ### Corollary 2: logistic regression -/

section Logistic

open MeasureTheory ProbabilityTheory

/-- The **logistic loss** `ℓ_LR(z) = log(1 + e^{-z})` (Section 3.4.1 of
Chaudhuri–Monteleoni–Sarwate). -/
noncomputable def logisticLoss (z : ℝ) : ℝ :=
  log (1 + exp (-z))

/-- `ℓ'_LR(z) = -1 / (1 + e^z)` (Section 3.4.1 of Chaudhuri–Monteleoni–Sarwate). -/
lemma hasDerivAt_logisticLoss (z : ℝ) : HasDerivAt logisticLoss (-(1 + exp z)⁻¹) z := by
  unfold logisticLoss
  have h := (((hasDerivAt_neg z).exp).const_add 1).log (by positivity)
  convert h using 1
  have := exp_pos z
  rw [exp_neg]
  field_simp
  ring

lemma differentiable_logisticLoss : Differentiable ℝ logisticLoss :=
  fun z ↦ (hasDerivAt_logisticLoss z).differentiableAt

lemma deriv_logisticLoss : deriv logisticLoss = fun z ↦ -(1 + exp z)⁻¹ :=
  funext fun z ↦ (hasDerivAt_logisticLoss z).deriv

/-- `|ℓ'_LR(z)| ≤ 1`. -/
lemma abs_deriv_logisticLoss_le (z : ℝ) : |deriv logisticLoss z| ≤ 1 := by
  rw [deriv_logisticLoss, abs_neg, abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (by linarith [exp_pos z])

/-- The logistic loss is convex (its derivative `-1 / (1 + e^z)` is monotone). -/
lemma convexOn_logisticLoss : ConvexOn ℝ univ logisticLoss := by
  refine Monotone.convexOn_univ_of_deriv differentiable_logisticLoss ?_
  rw [deriv_logisticLoss]
  intro a b hab
  simp only [neg_le_neg_iff]
  gcongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regularizer `N(f) = ‖f‖² / 2` is `1`-strongly convex. -/
lemma strongConvexOn_half_sq_norm : StrongConvexOn univ 1 fun f : E ↦ 1 / 2 * ‖f‖ ^ 2 := by
  rw [strongConvexOn_iff_convex]
  simpa using convexOn_const (0 : ℝ) convex_univ

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq E] {n : ℕ}
  {Λ ε : ℝ}

/-- **Corollary 2** of Chaudhuri–Monteleoni–Sarwate, output perturbation part: Algorithm 1 with
`N(f) = ‖f‖² / 2` and the logistic loss is `ε`-differentially private, i.e. for `n > 0`, `Λ > 0`
and `ε > 0`, the mechanism `D ↦ argmin J(·, D) + b` for
`J(f, D) = (1/n) ∑ᵢ log(1 + e^{-yᵢ ⟪xᵢ, f⟫}) + (Λ/2)‖f‖²`, with `b` of density
`∝ e^{-(nΛε/2)‖b‖}`, is a Markov kernel and is `ε`-DP for `Neighbour`. The objective
perturbation part (Algorithm 2) is not formalized. -/
theorem isEpsDP_outputPerturbation_comap_erm_logisticLoss (hn : 0 < n) (hΛ : 0 < Λ)
    (hε : 0 < ε) :
    IsMarkovKernel ((outputPerturbation (n * Λ * ε / 2).toNNReal).comap
        (erm logisticLoss (fun f : E ↦ 1 / 2 * ‖f‖ ^ 2) Λ)
        (measurable_erm hn hΛ convexOn_logisticLoss (lipschitzWith_one_of_abs_deriv_le
          differentiable_logisticLoss abs_deriv_logisticLoss_le) strongConvexOn_half_sq_norm)) ∧
      IsEpsDP ((outputPerturbation (n * Λ * ε / 2).toNNReal).comap
        (erm logisticLoss (fun f : E ↦ 1 / 2 * ‖f‖ ^ 2) Λ)
        (measurable_erm hn hΛ convexOn_logisticLoss (lipschitzWith_one_of_abs_deriv_le
          differentiable_logisticLoss abs_deriv_logisticLoss_le) strongConvexOn_half_sq_norm))
        Neighbour ε :=
  isEpsDP_outputPerturbation_comap_erm hn hΛ hε convexOn_logisticLoss differentiable_logisticLoss
    abs_deriv_logisticLoss_le strongConvexOn_half_sq_norm

end Logistic

end PrivateERM

end InformationTheory
