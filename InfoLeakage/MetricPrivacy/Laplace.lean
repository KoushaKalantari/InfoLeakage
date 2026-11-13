/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Laplace
public import InfoLeakage.MetricPrivacy.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Laplace mechanisms for metric privacy, and geo-indistinguishability

This file formalizes the Laplace mechanisms of K. Chatzikokolakis, M. E. Andrés,
N. E. Bordenabe and C. Palamidessi, *Broadening the scope of differential privacy using
metrics*, PETS 2013 (HAL hal-00767210v1), Section 4.1 ([CABP]), and the definition of
geo-indistinguishability and the planar Laplace mechanism of M. E. Andrés, N. E. Bordenabe,
K. Chatzikokolakis and C. Palamidessi, *Geo-indistinguishability: differential privacy for
location-based systems*, CCS 2013 ([arXiv:1212.1984](https://arxiv.org/abs/1212.1984), v3),
Sections 3.1 and 4.1 ([ABCP]). Privacy is `IsMetricDP` from `InfoLeakage.MetricPrivacy.Basic`.

## Main definitions

* `MetricDP.laplaceMech ν λ d`: the Laplace mechanism from `(Z, d)` to `Z`, for an extended
  distance `d`, with density `λ(z) e^{-d(y, z)}` (`e^{-∞} = 0`, `MetricDP.expNeg`) with respect
  to `ν` (Definition 6 of [CABP]), when this density is jointly measurable in `(y, z)`; otherwise
  it is the zero kernel.
* `IsGeoInd K ε`: `ε`-geo-indistinguishability (Definition 3.1 of [ABCP]).
* `GeoInd.IsPrivateWithin K ℓ r`: `ℓ`-privacy within radius `r` (Section 3.1 of [ABCP]).
* `planarLaplacePDFReal ε x`, `planarLaplace ε`: the planar Laplacian
  `(ε² / 2π) e^{-ε d(x, z)}` on `ℝ²` and the planar Laplace mechanism (equation (1) of [ABCP];
  Figure 2 (ii) of [CABP]).

## Main statements (paper result → Lean name)

* Fact 7 of [CABP] (every Laplace mechanism from `(Z, d)` is `d`-private), for any jointly
  measurable extended pseudometric `d`: `MetricDP.isMetricDP_laplaceMech`; for `ε · edist` on a
  pseudo-emetric space: `MetricDP.isMetricDP_laplaceMech_edist`.
* Figure 2 (i) of [CABP] (the Laplace mechanism on `ℝ` is `ε d_ℝ`-private), reusing
  `laplaceMechanism` from `InfoLeakage.DP.Laplace`: `isMetricDP_laplaceMechanism_id`, and for a
  query `f` with scale `b`, `isMetricDP_laplaceMechanism` (`|f x - f x'| / b`-privacy).
* [ABCP] Sections 1 and 3 (`ε`-geo-indistinguishability is `εr`-privacy within every radius
  `r > 0`): `isGeoInd_iff_forall_isPrivateWithin`.
* [ABCP] Section 4.1, equation (1): the normalization `ε² / 2π` is correct,
  `integral_planarLaplacePDFReal` (via `MetricDP.integral_exp_neg_mul_dist_fin_two`,
  `∫ e^{-ε d(x, z)} dz = 2π / ε²`), and `isMarkovKernel_planarLaplace`; property (ii), the
  planar Laplace mechanism is `ε`-geo-indistinguishable: `isGeoInd_planarLaplace` (through
  `planarLaplace_eq_laplaceMech` and Fact 7; stated for all `ε ≥ 0`, the paper's `ε > 0` being
  the case of a Markov kernel).

## Implementation notes

In Definition 6 of [CABP] the metric lives on `Y ∪ Z`; here secrets and outputs live in one
space `Z` with an extended distance `d`, which covers instances (i)–(iii) of Figure 2 (for (iii),
`ε · edist` on `WithLp 1 (ℝ × ℝ)` is the scaled Manhattan metric). Secrets in a subset
`Y ⊆ Z` are obtained by restricting the kernel along the (isometric) inclusion with
`IsMetricDP.comap`. Privacy does not need `λ` to normalize the densities; normalization only
makes the kernel Markov. Geo-indistinguishability is stated for any space with an `edist`
(the Euclidean distance on `ℝ²` in [ABCP]); `isGeoInd_iff_forall_isPrivateWithin` needs a
metric space.

## Not formalized

* The normalizing constants of instances (iii) (`λ = ε² / 4`, Manhattan metric on `ℝ²`) and
  (iv) (truncated geometric) of Figure 2 of [CABP]; their privacy is an instance of
  `MetricDP.isMetricDP_laplaceMech`, but we do not instantiate them.
* Property (i) of the planar Laplacian in [ABCP] Section 4.1 (its projection on a vertical
  plane through the centre is a scaled linear Laplacian), the polar-coordinates sampling method
  of Section 4.1, and Sections 4.2–4.4 of [ABCP] (discretization and truncation, Theorems 4.1
  and 4.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace InformationTheory

/-! ### Laplace mechanisms for an extended metric -/

section General

variable {Z : Type*} [MeasurableSpace Z]

/-- A kernel `y ↦ ν.withDensity (f y)` whose densities satisfy `f y ≤ e^{d(y, y')} f y'`
pointwise whenever `d(y, y') < ∞` is `d`-private. -/
lemma MetricDP.isMetricDP_withDensity {Y : Type*} [MeasurableSpace Y] {ν : Measure Z} [SFinite ν]
    {f : Y → Z → ℝ≥0∞} {d : Y → Y → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (h : ∀ ⦃y y'⦄, d y y' ≠ ∞ → ∀ z, f y z ≤ ENNReal.ofReal (exp (d y y').toReal) * f y' z) :
    IsMetricDP ((Kernel.const Y ν).withDensity f) d := by
  intro y y' hd
  rw [Kernel.withDensity_apply _ hf, Kernel.withDensity_apply _ hf, Kernel.const_apply,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  exact withDensity_mono (ae_of_all _ (h hd))

namespace MetricDP

/-- `e^{-t}` for `t ∈ [0, ∞]`, with `e^{-∞} = 0`. -/
noncomputable def expNeg (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = ∞ then 0 else ENNReal.ofReal (exp (-t.toReal))

lemma expNeg_of_ne_top {t : ℝ≥0∞} (ht : t ≠ ∞) : expNeg t = ENNReal.ofReal (exp (-t.toReal)) := by
  simp [expNeg, ht]

lemma measurable_expNeg : Measurable expNeg :=
  Measurable.ite (measurableSet_singleton ∞) measurable_const
    (ENNReal.measurable_ofReal.comp (measurable_exp.comp ENNReal.measurable_toReal.neg))

/-- The likelihood-ratio bound behind Fact 7: if `t ≤ a + s` with `a < ∞`, then
`e^{-s} ≤ e^a e^{-t}`. -/
lemma expNeg_le_mul {a s t : ℝ≥0∞} (ha : a ≠ ∞) (h : t ≤ a + s) :
    expNeg s ≤ ENNReal.ofReal (exp a.toReal) * expNeg t := by
  by_cases hs : s = ∞
  · simp [expNeg, hs]
  have has : a + s ≠ ∞ := ENNReal.add_ne_top.2 ⟨ha, hs⟩
  rw [expNeg_of_ne_top hs, expNeg_of_ne_top (ne_top_of_le_ne_top has h),
    ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
  gcongr
  have := ENNReal.toReal_mono has h
  rw [ENNReal.toReal_add ha hs] at this
  linarith

/-- The **Laplace mechanism** from `(Z, d)` to `Z` (Definition 6 of Chatzikokolakis–Andrés–
Bordenabe–Palamidessi, with secrets and outputs in the same space `Z` and `d` an extended
distance on `Z`): on input `y` it has density `z ↦ λ(z) e^{-d(y, z)}` (with `e^{-∞} = 0`)
with respect to a reference measure `ν`, provided the joint density
`(y, z) ↦ λ(z) e^{-d(y, z)}` is measurable (e.g. `λ` measurable and `d` jointly measurable, as
`isMetricDP_laplaceMech` assumes). No measurability is required here: otherwise
`Kernel.withDensity` returns the zero kernel. The scaling function `λ` is a parameter;
Definition 6 requires it to make every `λ(·) e^{-d(y, ·)}` a probability density, which is
needed only for the kernel to be Markov, not for privacy (`isMetricDP_laplaceMech`). Secrets
in a subset `Y ⊆ Z` are handled by restricting the kernel along the inclusion
(`IsMetricDP.comap`). -/
noncomputable def laplaceMech (ν : Measure Z) [SFinite ν] (lam : Z → ℝ≥0∞)
    (d : Z → Z → ℝ≥0∞) : Kernel Z Z :=
  (Kernel.const Z ν).withDensity fun y z ↦ lam z * expNeg (d y z)

/-- **Fact 7** of Chatzikokolakis–Andrés–Bordenabe–Palamidessi (McSherry–Talwar): every Laplace
mechanism from `(Z, d)` to `Z` satisfies `d`-privacy, for an extended distance
`d : Z → Z → ℝ≥0∞` that is symmetric and satisfies the triangle inequality (an extended
pseudometric; `d(z, z) = 0` is not needed) and is jointly measurable, and a measurable scaling
function `λ`. -/
theorem isMetricDP_laplaceMech (ν : Measure Z) [SFinite ν] {lam : Z → ℝ≥0∞}
    (hlam : Measurable lam) {d : Z → Z → ℝ≥0∞} (hd : Measurable (Function.uncurry d))
    (hsymm : ∀ y y', d y y' = d y' y) (htri : ∀ x y z, d x z ≤ d x y + d y z) :
    IsMetricDP (laplaceMech ν lam d) d := by
  refine isMetricDP_withDensity ((hlam.comp measurable_snd).mul (measurable_expNeg.comp hd))
    fun y y' hyy' z ↦ ?_
  rw [mul_left_comm]
  refine mul_le_mul_right (expNeg_le_mul hyy' ?_) _
  simpa [hsymm y' y] using htri y' y z

/-- **Fact 7** for a scaled (pseudo-e)metric space: the Laplace mechanism from `(Z, ε d)` with
density `λ(z) e^{-ε d(y, z)}` is `ε d`-private. Instances: `Z = ℝ` (Figure 2 (i)), `ℝ²` with
the Euclidean metric (Figure 2 (ii), `isGeoInd_planarLaplace`), or with the Manhattan metric
via `WithLp 1 (ℝ × ℝ)` (Figure 2 (iii)). -/
theorem isMetricDP_laplaceMech_edist [PseudoEMetricSpace Z] [SecondCountableTopology Z]
    [BorelSpace Z] (ν : Measure Z) [SFinite ν] {lam : Z → ℝ≥0∞} (hlam : Measurable lam)
    (ε : ℝ≥0) :
    IsMetricDP (laplaceMech ν lam fun y z ↦ ε * edist y z) fun y y' ↦ ε * edist y y' :=
  isMetricDP_laplaceMech ν hlam (measurable_const.mul measurable_edist)
    (fun y y' ↦ by rw [edist_comm]) fun x y z ↦ by
      rw [← mul_add]
      exact mul_le_mul_right (edist_triangle x y z) _

end MetricDP

end General

/-! ### The one-dimensional Laplace mechanism -/

/-- **Laplace mechanism on `ℝ`** (Figure 2 (i) of Chatzikokolakis–Andrés–Bordenabe–Palamidessi,
via Fact 7), for the mechanism `laplaceMechanism f b` of `InfoLeakage.DP.Laplace`: for a
measurable query `f` and scale `b > 0`, `x ↦ Lap(f(x), b)` satisfies `d`-privacy for
`d(x, x') = |f(x) - f(x')| / b`. With `f = id` and `b = 1 / ε` this is the `ε d_ℝ`-privacy of
the one-dimensional Laplace mechanism (`isMetricDP_laplaceMechanism_id`). -/
theorem isMetricDP_laplaceMechanism {𝒟 : Type*} [MeasurableSpace 𝒟] {f : 𝒟 → ℝ}
    (hf : Measurable f) {b : ℝ} (hb : 0 < b) :
    IsMetricDP (laplaceMechanism f b) fun x x' ↦ ENNReal.ofReal (|f x - f x'| / b) := by
  refine MetricDP.isMetricDP_withDensity (measurable_uncurry_laplacePDF hf b) fun x x' _ y ↦ ?_
  rw [ENNReal.toReal_ofReal (by positivity), laplacePDF, laplacePDF,
    ← ENNReal.ofReal_mul (exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (laplacePDFReal_le_exp_mul hb (by rw [div_mul_cancel₀ _ hb.ne'])
    y)

/-- **The one-dimensional Laplace mechanism is `ε d_ℝ`-private** (Figure 2 (i) of
Chatzikokolakis–Andrés–Bordenabe–Palamidessi): for `ε > 0`, the kernel `y ↦ Lap(y, 1/ε)`
(density `(ε/2) e^{-ε |y - z|}`) satisfies `K(y)(E) ≤ e^{ε |y - y'|} K(y')(E)`. -/
theorem isMetricDP_laplaceMechanism_id {ε : ℝ≥0} (hε : 0 < ε) :
    IsMetricDP (laplaceMechanism id (1 / ε)) fun y y' ↦ ε * edist y y' := by
  refine (isMetricDP_laplaceMechanism measurable_id (by positivity)).mono fun y y' ↦ le_of_eq ?_
  rw [id, id, div_div_eq_mul_div, div_one, edist_dist, Real.dist_eq, mul_comm,
    ENNReal.ofReal_mul (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]

/-! ### Geo-indistinguishability -/

section GeoInd

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- **`ε`-geo-indistinguishability** (Definition 3.1 of Andrés–Bordenabe–Chatzikokolakis–
Palamidessi): `K(x)(E) ≤ e^{ε d(x, x')} K(x')(E)` for all locations `x, x'` and events `E`, i.e.
`ε d`-privacy (`IsMetricDP`) for the distance `d` of the space of locations (the Euclidean
distance in the paper; any extended distance `edist` here). -/
def IsGeoInd [EDist X] (K : Kernel X Z) (ε : ℝ≥0) : Prop :=
  IsMetricDP K fun x x' ↦ ε * edist x x'

/-- **`ℓ`-privacy within `r`** (Section 3.1 of Andrés–Bordenabe–Chatzikokolakis–Palamidessi):
locations at distance at most `r` produce distributions at most `ℓ` apart, `K(x) ≤ e^ℓ K(x')`
(the multiplicative distance `d_P(K(x), K(x')) ≤ ℓ`, both orders of `x, x'` being included). -/
def GeoInd.IsPrivateWithin [PseudoMetricSpace X] (K : Kernel X Z) (ℓ r : ℝ) : Prop :=
  ∀ ⦃x x'⦄, dist x x' ≤ r → K x ≤ ENNReal.ofReal (exp ℓ) • K x'

omit [MeasurableSpace X] in
/-- `ε d(x, x')` computed through `edist`. -/
lemma GeoInd.toReal_coe_mul_edist [PseudoMetricSpace X] (ε : ℝ≥0) (x x' : X) :
    ((ε : ℝ≥0∞) * edist x x').toReal = ε * dist x x' := by
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- **Geo-indistinguishability is privacy proportional to the radius** (Sections 1 and 3 of
Andrés–Bordenabe–Chatzikokolakis–Palamidessi: "for any radius `r > 0`, the user enjoys
`εr`-privacy within `r`"): on a metric space, `K` is `ε`-geo-indistinguishable iff it enjoys
`εr`-privacy within `r` for every `r > 0`. -/
theorem isGeoInd_iff_forall_isPrivateWithin [MetricSpace X] {K : Kernel X Z} {ε : ℝ≥0} :
    IsGeoInd K ε ↔ ∀ r, 0 < r → GeoInd.IsPrivateWithin K (ε * r) r := by
  refine ⟨fun h r _ x x' hxx' ↦ ?_, fun h x x' _ ↦ ?_⟩
  · have := h (x := x) (x' := x') (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top x x'))
    rw [GeoInd.toReal_coe_mul_edist] at this
    exact this.trans <| MetricDP.smul_le_smul_of_le (ENNReal.ofReal_le_ofReal <| exp_le_exp.2 <|
      mul_le_mul_of_nonneg_left hxx' (NNReal.coe_nonneg ε)) _
  · beta_reduce
    rw [GeoInd.toReal_coe_mul_edist]
    rcases eq_or_ne x x' with rfl | hne
    · simp
    · exact h _ (dist_pos.2 hne) le_rfl

end GeoInd

/-! ### The planar Laplace mechanism -/

section Planar

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The density `D_ε(x)(z) = (ε² / 2π) e^{-ε d(x, z)}` of the **planar Laplacian** centred at
`x` (equation (1) of Andrés–Bordenabe–Chatzikokolakis–Palamidessi; Figure 2 (ii) of
Chatzikokolakis–Andrés–Bordenabe–Palamidessi), `d` the Euclidean distance on `ℝ²`. -/
noncomputable def planarLaplacePDFReal (ε : ℝ≥0) (x z : ℝ²) : ℝ :=
  ε ^ 2 / (2 * π) * exp (-(ε * dist x z))

/-- The **planar Laplace mechanism** `x ↦ D_ε(x)` on `ℝ²` (Section 4.1 of
Andrés–Bordenabe–Chatzikokolakis–Palamidessi): the kernel with density `planarLaplacePDFReal ε x`
with respect to Lebesgue measure. It is a Markov kernel for `ε > 0`
(`isMarkovKernel_planarLaplace`). -/
noncomputable def planarLaplace (ε : ℝ≥0) : Kernel ℝ² ℝ² :=
  (Kernel.const ℝ² volume).withDensity fun x z ↦ ENNReal.ofReal (planarLaplacePDFReal ε x z)

/-- The planar Laplace mechanism is the Laplace mechanism of Definition 6 of
Chatzikokolakis–Andrés–Bordenabe–Palamidessi for `(ℝ², ε d₂)`, with constant scaling function
`λ = ε² / 2π`. -/
lemma planarLaplace_eq_laplaceMech (ε : ℝ≥0) :
    planarLaplace ε = MetricDP.laplaceMech volume (fun _ ↦ ENNReal.ofReal (ε ^ 2 / (2 * π)))
      fun x z ↦ ε * edist x z := by
  unfold planarLaplace MetricDP.laplaceMech planarLaplacePDFReal
  congr 1
  funext x z
  rw [MetricDP.expNeg_of_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top x z)),
    GeoInd.toReal_coe_mul_edist, ENNReal.ofReal_mul (by positivity)]

/-- **Andrés–Bordenabe–Chatzikokolakis–Palamidessi, Section 4.1** (property (ii) of the planar
Laplacian, via Fact 7 of Chatzikokolakis–Andrés–Bordenabe–Palamidessi): the planar Laplace
mechanism satisfies `ε`-geo-indistinguishability. The paper takes `ε > 0`, where the mechanism
is a Markov kernel (`isMarkovKernel_planarLaplace`); the statement also holds, trivially, at
`ε = 0`, where `planarLaplace 0` is the zero kernel. -/
theorem isGeoInd_planarLaplace (ε : ℝ≥0) : IsGeoInd (planarLaplace ε) ε := by
  rw [planarLaplace_eq_laplaceMech]
  exact MetricDP.isMetricDP_laplaceMech_edist volume measurable_const ε

/-- `∫ e^{-ε d(x, z)} dz = 2π / ε²` on `ℝ²`, for `ε > 0`. -/
lemma MetricDP.integral_exp_neg_mul_dist_fin_two {ε : ℝ} (hε : 0 < ε) (x : ℝ²) :
    ∫ z, exp (-(ε * dist x z)) = 2 * π / ε ^ 2 := by
  have h₁ : ∫ z, exp (-(ε * dist x z)) = ∫ z : ℝ², exp (-(ε * ‖z‖)) := by
    simp_rw [dist_comm x, dist_eq_norm]
    exact integral_sub_right_eq_self (fun z : ℝ² ↦ exp (-(ε * ‖z‖))) x
  have h₂ : ∫ t in Ioi (0 : ℝ), t * exp (-(ε * t)) = 1 / ε ^ 2 := by
    have := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hε
    norm_num [Real.Gamma_two] at this
    rw [this]
    norm_num
  rw [h₁, integral_fun_norm_addHaar volume fun t ↦ exp (-(ε * t)), finrank_euclideanSpace_fin,
    measureReal_def, EuclideanSpace.volume_ball_fin_two]
  norm_num [ENNReal.toReal_ofReal pi_pos.le, h₂]
  ring

/-- The planar Laplacian `D_ε(x)` is a probability density for `ε > 0`: the normalization factor
`ε² / 2π` of equation (1) of Andrés–Bordenabe–Chatzikokolakis–Palamidessi is correct. -/
theorem integral_planarLaplacePDFReal {ε : ℝ≥0} (hε : 0 < ε) (x : ℝ²) :
    ∫ z, planarLaplacePDFReal ε x z = 1 := by
  have : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  unfold planarLaplacePDFReal
  rw [integral_const_mul, MetricDP.integral_exp_neg_mul_dist_fin_two (by exact_mod_cast hε)]
  field_simp

lemma continuous_planarLaplacePDFReal (ε : ℝ≥0) (x : ℝ²) :
    Continuous (planarLaplacePDFReal ε x) := by
  unfold planarLaplacePDFReal
  fun_prop

lemma measurable_uncurry_planarLaplacePDF (ε : ℝ≥0) :
    Measurable (Function.uncurry fun x z ↦ ENNReal.ofReal (planarLaplacePDFReal ε x z)) :=
  ENNReal.measurable_ofReal.comp <| measurable_const.mul <|
    measurable_exp.comp (measurable_const.mul measurable_dist).neg

lemma lintegral_planarLaplacePDF {ε : ℝ≥0} (hε : 0 < ε) (x : ℝ²) :
    ∫⁻ z, ENNReal.ofReal (planarLaplacePDFReal ε x z) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun z ↦ by unfold planarLaplacePDFReal; positivity)
    (continuous_planarLaplacePDFReal ε x).aestronglyMeasurable, integral_planarLaplacePDFReal hε]

/-- The planar Laplace mechanism is a Markov kernel for `ε > 0`. -/
theorem isMarkovKernel_planarLaplace {ε : ℝ≥0} (hε : 0 < ε) :
    IsMarkovKernel (planarLaplace ε) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  rw [planarLaplace, Kernel.withDensity_apply _ (measurable_uncurry_planarLaplacePDF ε),
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_planarLaplacePDF hε]

end Planar

end InformationTheory
