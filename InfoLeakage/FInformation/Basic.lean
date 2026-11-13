/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.FInformation.ChiSquared
public import InfoLeakage.FInformation.Pinsker
public import InfoLeakage.MaximalLeakage.MutualInfo
public import Mathlib.Probability.UniformOn
public import Statlib.Divergence.MutualInformation.Basic
public import Statlib.Divergence.TotalVariation

/-!
# f-information

For a divergence function `f`, the **f-information** between an input `X ∼ μ` and the output `Y`
of a channel `κ` is `I_f(X; Y) = D_f(P_{XY} ‖ P_X ⊗ P_Y)`, where `P_{XY} = μ ⊗ₘ κ` and
`P_X ⊗ P_Y = μ × (κ ∘ₘ μ)`. This is equation (7.46) of Y. Polyanskiy and Y. Wu, *Information
Theory: From Coding to Learning*, Cambridge University Press (2024), Section 7.8. For the
Kullback–Leibler divergence it is the mutual information.

It should be distinguished from the f-informativity of I. Csiszár, *A class of measures of
informativity of observation channels*, Period. Math. Hungar. 2 (1972), Definition 2.3, (2.9): the
infimum `inf_Q ∑_x P_X(x) D_f(P_{Y|x} ‖ Q)` over output laws `Q`, while
`D_f(P_{XY} ‖ P_X ⊗ P_Y) = ∑_x P_X(x) D_f(P_{Y|x} ‖ P_Y)` is its value at `Q = P_Y`, an upper
bound on it. The two differ in general; for the Kullback–Leibler divergence the infimum is attained
at `Q = P_Y` and both are `I(X; Y)`. Csiszár's optimized quantity is not formalized here.

We give two versions. `fMutualInfo f ρ` is defined for an arbitrary joint law `ρ` on `α × β`, as
`D_f(ρ ‖ ρ.fst × ρ.snd)`, and covers (7.46) in full generality. `fInfo f μ κ` is parametrized, as
elsewhere in this library, by an input law `μ` and a channel `κ`, with joint law `μ ⊗ₘ κ`; for a
Markov kernel `κ` the two agree (`fMutualInfo_compProd`). Joint laws that do not disintegrate
(possible outside standard Borel spaces) are covered only by `fMutualInfo`. For a kernel that is
not Markov, `μ.prod (κ ∘ₘ μ)` need not be the product of the marginals of `μ ⊗ₘ κ`, so the
statements of `fInfo` that speak of independence assume `κ` Markov.

## Conventions

The f-divergence is Statlib's `fDiv f ∈ ℝ≥0∞` for a `DivFunction f`, an `ℝ≥0∞`-valued convex
function, and logarithms are natural. Polyanskiy–Wu's real-valued `f` fits this framework after
adding a linear term `c (x - 1)` that makes it nonnegative; by their Proposition 7.2(6) this does
not change `D_f` between probability measures (it can change it between finite measures of
different masses). In particular the Kullback–Leibler divergence uses
`klDivFun x = x log x + 1 - x` rather than their `x log x`. Several statements below assume only
finite input laws or finite kernels; they are statements about Statlib's `fDiv`, and they are
Polyanskiy–Wu's statements (with their real-valued `f`) when the two measures compared are
probability measures, e.g. for a probability input law `μ` and a Markov kernel `κ`.

Mathlib's `etvDist` (total variation norm) is twice Polyanskiy–Wu's `TV`, so `tvInfo μ κ` is twice
their `I_TV(X; Y) = TV(P_{XY}, P_X P_Y)`; and Statlib's `sqHellinger` is half of their `H²` (7.5),
so `sqHellingerInfo μ κ` is half of the f-information (7.46) for their `H²`.

## Main definitions

* `fMutualInfo f ρ`: the f-information `D_f(ρ ‖ ρ.fst × ρ.snd)` of a joint law `ρ`
  (Polyanskiy–Wu, (7.46)).
* `fInfo f μ κ`: the f-information `I_f(X; Y)` of an input `X ∼ μ` and the output `Y` of the
  channel `κ` (Polyanskiy–Wu, (7.46)).
* `tvInfo μ κ`: the total variation information, `etvDist (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))`.
* `chiSqInfo μ κ`: the χ²-information `I_{χ²}(X; Y) = χ²(P_{XY} ‖ P_X P_Y)` (Polyanskiy–Wu, (7.48)).
* `sqHellingerInfo μ κ`: `H²(P_{XY}, P_X P_Y)` with Statlib's normalization of the squared
  Hellinger distance, half of the f-information (7.46) for Polyanskiy–Wu's `H²` (7.5).

## Main statements (book result → Lean name)

* (7.46) for the Kullback–Leibler divergence: `fMutualInfo_klDivFun`, `fInfo_klDivFun`,
  `I_f(X; Y) = I(X; Y)`; the two versions agree: `fMutualInfo_compProd`.
* Theorem 7.16 (data processing, `U → X → Y` gives `I_f(U; Y) ≤ I_f(U; X)`): `fInfo_comp_le`,
  with the special cases `tvInfo_comp_le`, `chiSqInfo_comp_le`, `sqHellingerInfo_comp_le`; for
  joint laws, processing either component: `fMutualInfo_parallelComp_comp_le`.
* Independence gives `I_f = 0` (Polyanskiy–Wu, Section 7.8, and Theorem 7.5(a) and Ex. I.40 for
  the converse): `fMutualInfo_eq_zero_of_eq_prod`, `fInfo_eq_zero_of_compProd_eq_prod`, and for
  the output of a constant channel with a probability output law, `fMutualInfo_compProd_const`
  (from the finite-kernel identity `fInfo_const`); the converse for a divergence function
  strictly convex on a neighbourhood of `1` (stronger than Polyanskiy–Wu's strict convexity at
  `1`): `fMutualInfo_eq_zero_iff`,
  `fInfo_eq_zero_iff`; for the total variation and the mutual information, which are not covered
  by that hypothesis or are covered separately: `tvInfo_eq_zero_iff`,
  `mutualInfo_compProd_eq_zero_iff`.
* For a finite output alphabet and an arbitrary input space, `I(X; Y) ≤ log |𝒴|`:
  `mutualInfo_compProd_le_ofReal_log_card`.
* Pinsker's inequality for f-informations (Theorem 7.10 applied to `P_{XY}` and `P_X P_Y`):
  `sq_tvInfo_le_two_mul_mutualInfo` and `toReal_tvInfo_div_two_le_sqrt`, which is
  `I_TV(X; Y) ≤ √(I(X; Y) / 2)` in Polyanskiy–Wu's normalization; for a finite output alphabet
  the finiteness hypothesis is automatic: `toReal_tvInfo_div_two_le_sqrt_of_finite`.
* (7.34) for f-informations: `mutualInfo_le_chiSqInfo`,
  `mutualInfo_le_ofReal_log_one_add_toReal_chiSqInfo`.
* (7.33), weak form, for f-informations: `two_mul_sqHellingerInfo_le_mutualInfo`.
* (7.37) for f-informations: `sq_tvInfo_le_chiSqInfo`.

## References

* I. Csiszár, *A class of measures of informativity of observation channels*, Period. Math.
  Hungar. 2 (1972), 191–213 (the related, optimized f-informativity; see above).
* Y. Polyanskiy, Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press
  (2024), Section 7.8; draft at https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {f : DivFunction} {μ : Measure α} {κ : Kernel α β}

/-! ### f-information of a joint law -/

section Joint

variable {ρ : Measure (α × β)}

/-- The **f-information** `I_f(X; Y) = D_f(P_{XY} ‖ P_X ⊗ P_Y)` of a joint law `ρ = P_{XY}` on
`α × β` (Polyanskiy–Wu, (7.46)): the f-divergence between `ρ` and the product
`ρ.fst × ρ.snd` of its marginals. Here `f` is an `ℝ≥0∞`-valued `DivFunction`; a real-valued
convex `f` of Polyanskiy–Wu is represented after adding a linear term, which does not change the
divergence between probability measures (their Proposition 7.2(6)). -/
noncomputable def fMutualInfo (f : DivFunction) (ρ : Measure (α × β)) : ℝ≥0∞ :=
  fDiv f ρ (ρ.fst.prod ρ.snd)

/-- For `klDivFun x = x log x + 1 - x` (Polyanskiy–Wu use `x log x`, which gives the same divergence
between probability measures), the f-information of a joint law is its mutual information. -/
theorem fMutualInfo_klDivFun [IsFiniteMeasure ρ] : fMutualInfo klDivFun ρ = mutualInfo ρ := by
  rw [fMutualInfo, mutualInfo, klDiv_eq_fDiv]

/-- **Data processing inequality** for the f-information of a joint law (Polyanskiy–Wu,
Theorem 7.16): processing each component by a Markov kernel cannot increase `I_f`. -/
theorem fMutualInfo_parallelComp_comp_le [IsFiniteMeasure ρ] (κ : Kernel α γ) [IsMarkovKernel κ]
    {δ : Type*} {mδ : MeasurableSpace δ} (η : Kernel β δ) [IsMarkovKernel η] :
    fMutualInfo f ((κ ∥ₖ η) ∘ₘ ρ) ≤ fMutualInfo f ρ := by
  rw [fMutualInfo, fMutualInfo, Measure.fst_parallelComp_comp, Measure.snd_parallelComp_comp,
    Measure.prod_comp_comp]
  exact fDiv_comp_right_le _ _ _

/-- If `X` and `Y` are independent, that is `ρ = ρ.fst × ρ.snd`, then `I_f(X; Y) = 0`. -/
theorem fMutualInfo_eq_zero_of_eq_prod [IsFiniteMeasure ρ] (h : ρ = ρ.fst.prod ρ.snd) :
    fMutualInfo f ρ = 0 := by
  rw [fMutualInfo, ← h, fDiv_self]

/-- For a divergence function `f` that is strictly convex on an open interval around `1`, the
f-information of a joint law vanishes if and only if the two components are independent
(Polyanskiy–Wu, Theorem 7.5(a) and Ex. I.40(i)). The hypothesis is stronger than the strict
convexity at `1` of Polyanskiy–Wu (Theorem 7.5(a), footnote 2): it excludes for instance
`f(x) = |1 - x|`, for which see `tvInfo_eq_zero_iff`. -/
theorem fMutualInfo_eq_zero_iff [IsFiniteMeasure ρ] {a b : ℝ} (ha : a < 1) (hb : 1 < b)
    (hf : StrictConvexOn ℝ (Set.Ioo a b) f.realFun) :
    fMutualInfo f ρ = 0 ↔ ρ = ρ.fst.prod ρ.snd :=
  fDiv_eq_zero_iff ha hb hf

end Joint

/-! ### f-information of an input law and a channel -/

/-- The **f-information** `I_f(X; Y) = D_f(P_{XY} ‖ P_X ⊗ P_Y)` between an input `X ∼ μ` and the
output `Y` of the channel `κ` (Polyanskiy–Wu, (7.46)): the f-divergence between the
joint law `μ ⊗ₘ κ` and `μ × (κ ∘ₘ μ)`, which for a Markov kernel `κ` is the product of the
marginals of `μ ⊗ₘ κ` (`fMutualInfo_compProd`). As for `fMutualInfo`, `f` is an `ℝ≥0∞`-valued
`DivFunction`, which represents a real-valued `f` of Polyanskiy–Wu up to a linear term. -/
noncomputable def fInfo (f : DivFunction) (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  fDiv f (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))

/-- For a Markov kernel, `fInfo f μ κ` is the f-information of the joint law `μ ⊗ₘ κ`. -/
theorem fMutualInfo_compProd [SFinite μ] [IsMarkovKernel κ] :
    fMutualInfo f (μ ⊗ₘ κ) = fInfo f μ κ := by
  rw [fMutualInfo, fInfo, Measure.fst_compProd, Measure.snd_compProd]

/-- For `klDivFun x = x log x + 1 - x` (Polyanskiy–Wu use `x log x`, which gives the same divergence
between probability measures), the f-information is the mutual information `I(X; Y)`
(Polyanskiy–Wu, Section 7.8). -/
theorem fInfo_klDivFun [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    fInfo klDivFun μ κ = mutualInfo (μ ⊗ₘ κ) := by
  rw [fInfo, mutualInfo_compProd, klDiv_eq_fDiv]

/-- **Data processing inequality** for the f-information (Polyanskiy–Wu, Theorem 7.16): for a
Markov chain `U → X → Y` with `U ∼ μ`, `X | U ∼ κ` and `Y | X ∼ η`,
`I_f(U; Y) ≤ I_f(U; X)`. -/
theorem fInfo_comp_le [IsFiniteMeasure μ] [IsMarkovKernel κ] (η : Kernel β γ) [IsMarkovKernel η] :
    fInfo f μ (η ∘ₖ κ) ≤ fInfo f μ κ := by
  have h_joint : μ ⊗ₘ (η ∘ₖ κ) = (Kernel.id ∥ₖ η) ∘ₘ (μ ⊗ₘ κ) :=
    Measure.parallelComp_comp_compProd.symm
  have h_prod : μ.prod ((η ∘ₖ κ) ∘ₘ μ) = (Kernel.id ∥ₖ η) ∘ₘ μ.prod (κ ∘ₘ μ) := by
    rw [← Measure.comp_assoc, ← Measure.prod_comp_comp, Measure.id_comp]
  rw [fInfo, fInfo, h_joint, h_prod]
  exact fDiv_comp_right_le _ _ _

/-- If `X` and `Y` are independent, that is `P_{XY} = P_X ⊗ P_Y` (for the Markov kernel `κ`,
`μ × (κ ∘ₘ μ)` is the product of the marginals of `μ ⊗ₘ κ`), then `I_f(X; Y) = 0`. -/
theorem fInfo_eq_zero_of_compProd_eq_prod [IsFiniteMeasure μ] [IsMarkovKernel κ]
    (h : μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ)) :
    fInfo f μ κ = 0 := by
  rw [fInfo, ← h, fDiv_self]

/-- For a constant kernel `Kernel.const α ξ` with `ξ` a finite measure, `fInfo f μ κ = 0`: the
identity `μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ)` holds. This is an identity about the two measures compared by
`fInfo`; unless `ξ` is a probability measure, the kernel is not Markov and `μ.prod (κ ∘ₘ μ)` need
not be the product of the marginals of `μ ⊗ₘ κ` (for `ξ = 2 • δ_y` the joint law has mass `2` and
the product of its marginals mass `4`). For the independence statement see
`fMutualInfo_compProd_const`. -/
theorem fInfo_const [IsProbabilityMeasure μ] (ξ : Measure β) [IsFiniteMeasure ξ] :
    fInfo f μ (Kernel.const α ξ) = 0 := by
  rw [fInfo, Measure.compProd_const, Measure.const_comp, measure_univ, one_smul, fDiv_self]

/-- The output `Y ∼ ξ` of a constant channel is independent of the input, hence the f-information
of the joint law vanishes: `I_f(X; Y) = 0`. -/
theorem fMutualInfo_compProd_const [IsProbabilityMeasure μ] (ξ : Measure β)
    [IsProbabilityMeasure ξ] :
    fMutualInfo f (μ ⊗ₘ Kernel.const α ξ) = 0 := by
  rw [fMutualInfo_compProd, fInfo_const]

/-- For a divergence function `f` that is strictly convex on an open interval around `1`, the
f-information vanishes if and only if the input and the output are independent, that is
`P_{XY} = P_X ⊗ P_Y` (for the Markov kernel `κ`, `μ × (κ ∘ₘ μ)` is the product of the marginals of
`μ ⊗ₘ κ`); see Polyanskiy–Wu, Theorem 7.5(a) and Ex. I.40(i). The hypothesis is stronger than the
strict convexity at `1` of Polyanskiy–Wu (Theorem 7.5(a), footnote 2): it excludes for instance
`f(x) = |1 - x|`, for which see `tvInfo_eq_zero_iff`. -/
theorem fInfo_eq_zero_iff [IsFiniteMeasure μ] [IsMarkovKernel κ] {a b : ℝ} (ha : a < 1)
    (hb : 1 < b) (hf : StrictConvexOn ℝ (Set.Ioo a b) f.realFun) :
    fInfo f μ κ = 0 ↔ μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ) :=
  fDiv_eq_zero_iff ha hb hf

/-- The mutual information vanishes if and only if the input and the output are independent,
`P_{XY} = P_X ⊗ P_Y`. -/
theorem mutualInfo_compProd_eq_zero_iff [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    mutualInfo (μ ⊗ₘ κ) = 0 ↔ μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ) := by
  rw [mutualInfo_compProd, klDiv_eq_zero_iff]

/-! ### The f-informations for the total variation, χ² and squared Hellinger distances -/

/-- The **total variation information** `‖P_{XY} - P_X ⊗ P_Y‖`, the f-information for
`f(x) = |1 - x|`. With Mathlib's normalization of the total variation distance it is twice the
`I_TV(X; Y) = TV(P_{XY}, P_X P_Y)` of Polyanskiy–Wu (Section 7.8). -/
noncomputable def tvInfo (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ := fInfo tvDivFun μ κ

lemma tvInfo_eq_etvDist [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    tvInfo μ κ = etvDist (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) :=
  fDiv_tvDivFun _ _

/-- The total variation information vanishes if and only if the input and the output are
independent, `P_{XY} = P_X ⊗ P_Y` (Polyanskiy–Wu, Theorem 7.5(a): `f(x) = |1 - x|` is strictly
convex at `1` in their sense, although it is not strictly convex on any interval). -/
theorem tvInfo_eq_zero_iff [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    tvInfo μ κ = 0 ↔ μ ⊗ₘ κ = μ.prod (κ ∘ₘ μ) := by
  rw [tvInfo_eq_etvDist, etvDist_eq_zero_iff]

/-- The **χ²-information** `I_{χ²}(X; Y) = χ²(P_{XY} ‖ P_X P_Y)` (Polyanskiy–Wu, (7.48)). -/
noncomputable def chiSqInfo (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ := fInfo chiSqDivFun μ κ

lemma chiSqInfo_eq_chiSqDiv : chiSqInfo μ κ = chiSqDiv (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ)) := rfl

/-- The squared Hellinger distance `H²(P_{XY}, P_X P_Y)` between the joint law and `μ × (κ ∘ₘ μ)`,
with Statlib's normalization `H²(P, Q) = (1/2) ∫ (√dP - √dQ)²`. It is half of the f-information
(7.46) for Polyanskiy–Wu's squared Hellinger distance `H²(P, Q) = ∫ (√dP - √dQ)²` (7.5). -/
noncomputable def sqHellingerInfo (μ : Measure α) (κ : Kernel α β) : ℝ≥0∞ :=
  sqHellinger (μ ⊗ₘ κ) (μ.prod (κ ∘ₘ μ))

/-- Twice `sqHellingerInfo μ κ` is the f-information (7.46) for `f(x) = (1 - √x)²`, the function of
Polyanskiy–Wu's squared Hellinger distance `H²` (7.5). -/
lemma two_mul_sqHellingerInfo : 2 * sqHellingerInfo μ κ = fInfo (hellingerDivFun 2⁻¹) μ κ :=
  two_mul_sqHellinger _ _

/-- **Data processing inequality** for the total variation information. -/
theorem tvInfo_comp_le [IsFiniteMeasure μ] [IsMarkovKernel κ] (η : Kernel β γ)
    [IsMarkovKernel η] :
    tvInfo μ (η ∘ₖ κ) ≤ tvInfo μ κ :=
  fInfo_comp_le η

/-- **Data processing inequality** for the χ²-information. -/
theorem chiSqInfo_comp_le [IsFiniteMeasure μ] [IsMarkovKernel κ] (η : Kernel β γ)
    [IsMarkovKernel η] :
    chiSqInfo μ (η ∘ₖ κ) ≤ chiSqInfo μ κ :=
  fInfo_comp_le η

/-- **Data processing inequality** for `sqHellingerInfo`. -/
theorem sqHellingerInfo_comp_le [IsFiniteMeasure μ] [IsMarkovKernel κ] (η : Kernel β γ)
    [IsMarkovKernel η] :
    sqHellingerInfo μ (η ∘ₖ κ) ≤ sqHellingerInfo μ κ := by
  have h := fInfo_comp_le (f := hellingerDivFun 2⁻¹) (μ := μ) (κ := κ) η
  rwa [← two_mul_sqHellingerInfo, ← two_mul_sqHellingerInfo,
    ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top] at h

/-! ### Comparisons with the mutual information -/

/-- **Pinsker's inequality for the total variation information** (Polyanskiy–Wu, Theorem 7.10
applied to `P_{XY}` and `P_X P_Y`): `tvInfo μ κ ^ 2 ≤ 2 I(X; Y)`. -/
theorem sq_tvInfo_le_two_mul_mutualInfo [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    tvInfo μ κ ^ 2 ≤ 2 * mutualInfo (μ ⊗ₘ κ) := by
  rw [tvInfo_eq_etvDist, mutualInfo_compProd]
  exact sq_etvDist_le_two_mul_klDiv

/-- **Pinsker's inequality for the total variation information**, in Polyanskiy–Wu's
normalization `I_TV(X; Y) = TV(P_{XY}, P_X P_Y) = tvInfo μ κ / 2`: if `I(X; Y) < ∞`, then
`I_TV(X; Y) ≤ √(I(X; Y) / 2)`. -/
theorem toReal_tvInfo_div_two_le_sqrt [IsProbabilityMeasure μ] [IsMarkovKernel κ]
    (h : mutualInfo (μ ⊗ₘ κ) ≠ ∞) :
    (tvInfo μ κ).toReal / 2 ≤ √((mutualInfo (μ ⊗ₘ κ)).toReal / 2) := by
  rw [mutualInfo_compProd] at h ⊢
  rw [tvInfo_eq_etvDist]
  exact tvDist_div_two_le_sqrt_toReal_klDiv_div_two h

/-- **`I(X; Y) ≤ log |𝒴|`**: for a finite output alphabet `β` and an arbitrary input space, the
mutual information is at most the logarithm of the number of outputs. -/
theorem mutualInfo_compProd_le_ofReal_log_card [Fintype β] [MeasurableSingletonClass β]
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal (log (Fintype.card β)) := by
  have : Nonempty β := nonempty_of_isProbabilityMeasure (κ ∘ₘ μ)
  -- compare the joint law with `μ × uniform`
  set ν : Measure β := uniformOn Set.univ
  have hc : (Fintype.card β : ℝ≥0∞) ≠ 0 := by simp
  calc mutualInfo (μ ⊗ₘ κ) ≤ klDiv (μ ⊗ₘ κ) (μ.prod ν) :=
        le_self_add.trans_eq (klDiv_compProd_prod_eq_mutualInfo_add μ κ ν).symm
    _ = ∫⁻ x, klDiv (κ x) ν ∂μ := by
        rw [← Measure.compProd_const, ← condKL, condKL_eq_lintegral]
        simp
    _ ≤ ∫⁻ _, ENNReal.ofReal (log (Fintype.card β)) ∂μ := by
        refine lintegral_mono fun x ↦ ?_
        have h := klDiv_le_ofReal_log_of_forall_le (μ := κ x) (ν := ν)
          (c := Fintype.card β) (ENNReal.natCast_ne_top _) fun y ↦ ?_
        · simpa using h
        rw [uniformOn_univ, Measure.count_singleton, ENNReal.mul_div_cancel hc
          (ENNReal.natCast_ne_top _)]
        exact prob_le_one
    _ = ENNReal.ofReal (log (Fintype.card β)) := by simp

/-- **Pinsker's inequality for the total variation information**, for a finite output alphabet
(and an arbitrary input space), where `I(X; Y) < ∞` holds automatically
(`mutualInfo_compProd_le_ofReal_log_card`): in Polyanskiy–Wu's normalization,
`I_TV(X; Y) ≤ √(I(X; Y) / 2)`. -/
theorem toReal_tvInfo_div_two_le_sqrt_of_finite [Finite β] [MeasurableSingletonClass β]
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    (tvInfo μ κ).toReal / 2 ≤ √((mutualInfo (μ ⊗ₘ κ)).toReal / 2) := by
  have := Fintype.ofFinite β
  exact toReal_tvInfo_div_two_le_sqrt
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top mutualInfo_compProd_le_ofReal_log_card)

/-- The squared total variation information is at most the χ²-information (Polyanskiy–Wu, (7.37)
applied to `P_{XY}` and `P_X P_Y`; Mathlib's normalization of the total variation distance is twice
theirs). -/
theorem sq_tvInfo_le_chiSqInfo [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    tvInfo μ κ ^ 2 ≤ chiSqInfo μ κ := by
  rw [tvInfo_eq_etvDist, chiSqInfo_eq_chiSqDiv, ← ofReal_tvDist, ← ENNReal.ofReal_pow tvDist_nonneg]
  exact ofReal_sq_tvDist_le_chiSqDiv

/-- The mutual information is at most the χ²-information (Polyanskiy–Wu, (7.34)). -/
theorem mutualInfo_le_chiSqInfo [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    mutualInfo (μ ⊗ₘ κ) ≤ chiSqInfo μ κ := by
  rw [mutualInfo_compProd]
  exact klDiv_le_chiSqDiv

/-- `I(X; Y) ≤ log (1 + I_{χ²}(X; Y))` (Polyanskiy–Wu, (7.34)), if the χ²-information is finite. -/
theorem mutualInfo_le_ofReal_log_one_add_toReal_chiSqInfo [IsProbabilityMeasure μ]
    [IsMarkovKernel κ] (h : chiSqInfo μ κ ≠ ∞) :
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal (log (1 + (chiSqInfo μ κ).toReal)) := by
  rw [mutualInfo_compProd]
  exact klDiv_le_ofReal_log_one_add_toReal_chiSqDiv h

/-- Twice `sqHellingerInfo μ κ`, that is the f-information (7.46) for Polyanskiy–Wu's `H²` (7.5), is
at most the mutual information (Polyanskiy–Wu, (7.33), the weaker of the two bounds). -/
theorem two_mul_sqHellingerInfo_le_mutualInfo [IsFiniteMeasure μ] [IsMarkovKernel κ] :
    2 * sqHellingerInfo μ κ ≤ mutualInfo (μ ⊗ₘ κ) := by
  rw [mutualInfo_compProd]
  exact two_mul_sqHellinger_le_klDiv

end InformationTheory
