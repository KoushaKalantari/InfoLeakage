/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.Analysis.Convex.Mul
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Statlib.Divergence.Renyi.Order

/-!
# The χ²-divergence and inequalities between f-divergences

We define the χ²-divergence `χ²(μ ‖ ν)` as the f-divergence of `x ↦ (x - 1)²` and prove some of the
inequalities between f-divergences collected in Section 7.6 of Y. Polyanskiy and Y. Wu,
*Information Theory: From Coding to Learning*, Cambridge University Press (2024). Logarithms are
natural, so the factor `log e` of the book is `1`.

## Conventions

The f-divergences are Statlib's `fDiv f μ ν ∈ ℝ≥0∞` for a `DivFunction f`, an `ℝ≥0∞`-valued
convex function. Polyanskiy–Wu's real-valued `f` fits this framework after adding a linear term
`c (x - 1)` that makes it nonnegative, which by their Proposition 7.2(6) does not change `D_f`
between probability measures: for instance the Kullback–Leibler divergence uses
`klDivFun x = x log x + 1 - x` instead of their `x log x`. The function
`x ↦ (x - 1)²` is `hellingerDivFun 2`, so `χ²(μ ‖ ν)` is the Hellinger divergence of order `2`.
Polyanskiy–Wu's squared Hellinger distance `H²(P, Q) = ∫ (√dP - √dQ)²` ((7.5)) is the Hellinger
divergence of order `1/2`, `hellingerDiv 2⁻¹ μ ν`, which is **twice** Statlib's
`sqHellinger μ ν`.

## Main definitions

* `chiSqDivFun`: the divergence function `x ↦ (x - 1)²` (Polyanskiy–Wu, (7.4)).
* `chiSqDiv μ ν`: the χ²-divergence, `fDiv chiSqDivFun μ ν`.

## Main statements (book result → Lean name)

* (7.4), the χ²-divergence as an f-divergence: `chiSqDivFun_apply`, `chiSqDiv_eq_hellingerDiv`;
  data processing (Theorem 7.4 for `f(x) = (x - 1)²`): `chiSqDiv_comp_right_le`.
* (7.34), `D(P ‖ Q) ≤ log (1 + χ²(P ‖ Q)) ≤ χ²(P ‖ Q)`:
  `klDiv_le_ofReal_log_one_add_toReal_chiSqDiv`, `ofReal_log_one_add_toReal_chiSqDiv_le`, and the
  combined bound `klDiv_le_chiSqDiv` (proved directly, without finiteness assumption).
* (7.33), weak form `D(P ‖ Q) ≥ H²(P, Q)`: `hellingerDiv_inv_two_le_klDiv`,
  `two_mul_sqHellinger_le_klDiv`.
* (7.37), `TV(P, Q) ≤ (1/2) √(χ²(P ‖ Q))`, that is `tvDist μ ν ^ 2 ≤ χ²(μ ‖ ν)` in Mathlib's
  normalization of the total variation distance: `ofReal_sq_tvDist_le_chiSqDiv`,
  `tvDist_le_sqrt_toReal_chiSqDiv`.

## Implementation notes

`KL ≤ log (1 + χ²)` is the monotonicity of the Rényi divergence in its order between the orders
`1` (the Kullback–Leibler divergence) and `2` (`log (1 + χ²)`), Statlib's
`renyiDiv_le_renyiDiv_of_le`. `KL ≤ χ²` and `H² ≤ KL` compare the divergence functions pointwise
(`fDiv_mono`). `TV² ≤ χ²` is Jensen's inequality `(∫ |1 - dμ/dν| dν)² ≤ ∫ (1 - dμ/dν)² dν`.

## References

* Y. Polyanskiy, Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press
  (2024); draft at https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

/-- The divergence function `x ↦ (x - 1)²` of the χ²-divergence (Polyanskiy–Wu, (7.4)). It is the
divergence function `hellingerDivFun 2` of the Hellinger divergence of order `2`. -/
noncomputable def chiSqDivFun : DivFunction := hellingerDivFun 2

lemma chiSqDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) :
    chiSqDivFun x = ENNReal.ofReal ((x.toReal - 1) ^ 2) := by
  rw [chiSqDivFun, hellingerDivFun_apply_of_pos_of_ne_one two_pos (by norm_num) hx, rpow_two]
  congr 1
  ring

@[simp]
lemma derivAtTop_chiSqDivFun : chiSqDivFun.derivAtTop = ∞ :=
  derivAtTop_hellingerDivFun_of_one_le one_le_two

/-- The χ²-divergence `χ²(μ ‖ ν) = ∫ (dμ/dν - 1)² dν` (Polyanskiy–Wu, (7.4)), the f-divergence for
`f(x) = (x - 1)²`. It is infinite if `μ` is not absolutely continuous with respect to `ν`. -/
noncomputable def chiSqDiv (μ ν : Measure α) : ℝ≥0∞ := fDiv chiSqDivFun μ ν

/-- The χ²-divergence is the Hellinger divergence of order `2`. -/
lemma chiSqDiv_eq_hellingerDiv (μ ν : Measure α) : chiSqDiv μ ν = hellingerDiv 2 μ ν := rfl

@[simp]
lemma chiSqDiv_self (μ : Measure α) [SigmaFinite μ] : chiSqDiv μ μ = 0 := fDiv_self μ

/-- **Data processing inequality** for the χ²-divergence. -/
theorem chiSqDiv_comp_right_le (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    chiSqDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ chiSqDiv μ ν :=
  fDiv_comp_right_le μ ν κ

/-- `KL(μ ‖ ν) ≤ χ²(μ ‖ ν)` for finite measures (Polyanskiy–Wu, (7.34), combined), from the
pointwise bound `x log x + 1 - x ≤ (x - 1)²`. -/
theorem klDiv_le_chiSqDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν ≤ chiSqDiv μ ν := by
  rw [klDiv_eq_fDiv]
  refine fDiv_mono (DivFunction.le_of_forall_ne_zero_ne_top fun x hx0 hx ↦ ?_)
  rw [klDivFun_apply hx, chiSqDivFun_apply hx]
  refine ENNReal.ofReal_le_ofReal ?_
  have hr : 0 < x.toReal := ENNReal.toReal_pos hx0 hx
  have h_log := log_le_sub_one_of_pos hr
  nlinarith [mul_le_mul_of_nonneg_left h_log hr.le]

/-- **`KL ≤ log (1 + χ²)`** (Polyanskiy–Wu, (7.34)): for probability measures with finite
χ²-divergence, `KL(μ ‖ ν) ≤ log (1 + χ²(μ ‖ ν))`. -/
theorem klDiv_le_ofReal_log_one_add_toReal_chiSqDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : chiSqDiv μ ν ≠ ∞) :
    klDiv μ ν ≤ ENNReal.ofReal (log (1 + (chiSqDiv μ ν).toReal)) := by
  rw [chiSqDiv_eq_hellingerDiv] at h ⊢
  calc klDiv μ ν = renyiDiv 1 μ ν := (renyiDiv_one_of_isProbabilityMeasure μ ν).symm
    _ ≤ renyiDiv 2 μ ν := renyiDiv_le_renyiDiv_of_le zero_le_one one_le_two
    _ = ENNReal.ofReal (log (1 + (hellingerDiv 2 μ ν).toReal)) := by
      rw [renyiDiv_of_one_lt one_lt_two, ite_eq_right h,
        ← mul_hellingerDiv_add_meas_eq_integral two_pos (by norm_num) h]
      norm_num

/-- `log (1 + χ²) ≤ χ²` (Polyanskiy–Wu, (7.34)), stated in `ℝ≥0∞` so that it is also meaningful
when `χ²(μ ‖ ν) = ∞`. -/
lemma ofReal_log_one_add_toReal_chiSqDiv_le (μ ν : Measure α) :
    ENNReal.ofReal (log (1 + (chiSqDiv μ ν).toReal)) ≤ chiSqDiv μ ν := by
  by_cases h : chiSqDiv μ ν = ∞
  · simp [h]
  refine (ENNReal.ofReal_le_ofReal ?_).trans (ENNReal.ofReal_toReal h).le
  have h_log := log_le_sub_one_of_pos (x := 1 + (chiSqDiv μ ν).toReal) (by positivity)
  linarith

/-- **`H² ≤ KL`** (Polyanskiy–Wu, (7.33), the weaker of the two bounds): the Hellinger divergence of
order `1/2`, which is Polyanskiy–Wu's `H²(μ, ν) = ∫ (√dμ - √dν)²`, is at most `KL(μ ‖ ν)`, from the
pointwise bound `(1 - √x)² ≤ x log x + 1 - x`. -/
theorem hellingerDiv_inv_two_le_klDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv 2⁻¹ μ ν ≤ klDiv μ ν := by
  rw [klDiv_eq_fDiv, hellingerDiv]
  refine fDiv_mono (DivFunction.le_of_forall_ne_zero_ne_top fun x hx0 hx ↦ ?_)
  rw [klDivFun_apply hx,
    hellingerDivFun_apply_of_pos_of_ne_one (by norm_num) (by norm_num) hx]
  refine ENNReal.ofReal_le_ofReal ?_
  set r := x.toReal
  have hr : 0 < r := ENNReal.toReal_pos hx0 hx
  -- write `r = t ^ 2` with `t = √r`
  set t := r ^ (2⁻¹ : ℝ) with ht_def
  have ht : 0 < t := rpow_pos_of_pos hr _
  have htr : r = t ^ 2 := by
    rw [ht_def, ← rpow_natCast, ← rpow_mul hr.le]
    norm_num
  have h_log : log r = 2 * log t := by rw [htr, log_pow]; norm_num
  -- `t - 1 ≤ t log t`
  have h1 : t - 1 ≤ t * log t := by
    have h := one_sub_inv_le_log_of_pos ht
    calc t - 1 = t * (1 - t⁻¹) := by field_simp
      _ ≤ t * log t := mul_le_mul_of_nonneg_left h ht.le
  rw [h_log, htr]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]

/-- **`2 H² ≤ KL`** in Statlib's normalization of the squared Hellinger distance
(Polyanskiy–Wu, (7.33), the weaker of the two bounds; Statlib's `sqHellinger` is half of
Polyanskiy–Wu's `H²`). -/
theorem two_mul_sqHellinger_le_klDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    2 * sqHellinger μ ν ≤ klDiv μ ν := by
  rw [two_mul_sqHellinger]
  exact hellingerDiv_inv_two_le_klDiv

/-- **`TV² ≤ χ²`** (Polyanskiy–Wu, (7.37), and the bound `χ² ≥ 4 TV²` of Proposition 7.15): for
probability measures, `tvDist μ ν ^ 2 ≤ χ²(μ ‖ ν)`. Mathlib's `tvDist μ ν` is twice
Polyanskiy–Wu's `TV(μ, ν)`, so this is `TV(μ, ν) ≤ (1/2) √(χ²(μ ‖ ν))`. -/
theorem ofReal_sq_tvDist_le_chiSqDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tvDist μ ν ^ 2) ≤ chiSqDiv μ ν := by
  by_cases h : chiSqDiv μ ν = ∞
  · simp [h]
  obtain ⟨h_int, hac⟩ := (hellingerDiv_ne_top_iff_of_one_lt one_lt_two μ ν).mp h
  set r : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal with hr
  have h_int1 : Integrable r ν := Measure.integrable_toReal_rnDeriv
  have h_int2 : Integrable (fun x ↦ r x ^ 2) ν := by simpa [rpow_two] using h_int
  have h_mean : ∫ x, r x ∂ν = 1 := by simp [r, Measure.integral_toReal_rnDeriv hac]
  have h_int_lin : Integrable (fun x ↦ 1 - 2 * r x) ν :=
    (integrable_const 1).sub (h_int1.const_mul 2)
  have h_int_sq : Integrable (fun x ↦ (1 - r x) ^ 2) ν :=
    (h_int_lin.add h_int2).congr (ae_of_all _ fun x ↦ by simp only [Pi.add_apply]; ring)
  -- `χ²(μ ‖ ν) = ∫ (1 - r)² dν`
  have h_chi : (chiSqDiv μ ν).toReal = ∫ x, (1 - r x) ^ 2 ∂ν := by
    have h_eq := mul_hellingerDiv_add_meas_eq_integral (μ := μ) (ν := ν) two_pos (by norm_num) h
    simp only [measure_univ, ENNReal.toReal_one, mul_one, rpow_two] at h_eq
    have h_sq : ∫ x, (1 - r x) ^ 2 ∂ν = ∫ x, (1 - 2 * r x + r x ^ 2) ∂ν :=
      integral_congr_ae (ae_of_all _ fun x ↦ by ring)
    rw [h_sq, integral_add h_int_lin h_int2,
      integral_sub (integrable_const 1) (h_int1.const_mul 2), integral_const_mul, h_mean]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [chiSqDiv_eq_hellingerDiv]
    linarith
  -- Jensen's inequality for `t ↦ t²`
  have h_abs_int : Integrable (fun x ↦ |1 - r x|) ν := ((integrable_const 1).sub h_int1).abs
  have h_jensen := (even_two.convexOn_pow (𝕜 := ℝ)).map_integral_le
    (continuous_pow 2).continuousOn isClosed_univ (ae_of_all _ fun x ↦ Set.mem_univ (|1 - r x|))
    h_abs_int (by simpa [Function.comp_def, sq_abs] using h_int_sq)
  rw [← ENNReal.ofReal_toReal h, tvDist_eq_integral_abs_rnDeriv_of_ac hac, h_chi]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [sq_abs] using h_jensen

/-- **`TV ≤ (1/2) √χ²`** (Polyanskiy–Wu, (7.37)), real form: for probability measures with finite
χ²-divergence, `tvDist μ ν ≤ √(χ²(μ ‖ ν))`, where Mathlib's `tvDist μ ν` is twice
Polyanskiy–Wu's `TV(μ, ν)`. -/
theorem tvDist_le_sqrt_toReal_chiSqDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : chiSqDiv μ ν ≠ ∞) :
    tvDist μ ν ≤ √(chiSqDiv μ ν).toReal := by
  have h' := ofReal_sq_tvDist_le_chiSqDiv (μ := μ) (ν := ν)
  rw [ENNReal.ofReal_le_iff_le_toReal h] at h'
  exact le_sqrt_of_sq_le h'

end InformationTheory
