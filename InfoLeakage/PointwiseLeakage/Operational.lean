/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.PointwiseLeakage.Basic

/-!
# Operational meaning of pointwise maximal leakage

Saeidian, Cervia, Oechtering and Skoglund (*Pointwise maximal leakage*, IEEE Trans. Inf. Theory
69(12), 2023, [arXiv:2205.04935](https://arxiv.org/abs/2205.04935), Definition 1) define the
pointwise maximal leakage from `X` to an outcome `y` of `Y` operationally, as
`ℓ(X → y) = log sup_{P_{U|X}} (sup_{P_{Û|Y}} P[U = Û | Y = y]) / max_u P_U(u)`,
the supremum ranging over all random variables `U` on a finite alphabet forming the Markov chain
`U - X - Y`, and all guesses `Û` of `U` made from `Y`. It is the logarithm of the largest
multiplicative gain that observing `Y = y` gives an adversary guessing *some* randomized function
`U` of `X`. Their
Theorem 1 evaluates it in closed form,
`ℓ(X → y) = log max_{x ∈ supp P_X} P_{X|Y=y}(x) / P_X(x)`.

We formalize the definition and prove Theorem 1 for finite alphabets. As for maximal leakage
(`InfoLeakage.MaximalLeakage.Operational`), the alphabet of `U` and `Û` ranges over the types
`Fin n`; `guessProbGiven_div_le_opPointwiseMaxLeakageRatio` shows that any other finite alphabet
gives nothing more.

## Main definitions

* `guessLaw μ ρ κ g`: the joint law of `(U, Y, Û)` in the Markov chain `U - X - Y - Û`.
* `guessProbGiven μ ρ κ g y`: `P[U = Û | Y = y]`.
* `opPointwiseMaxLeakageRatio μ κ y`: the supremum in Definition 1 (multiplicative form). The
  denominator `max_u P_U(u)` is `blindGuessProb μ ρ` from `InfoLeakage.MaximalLeakage.Operational`.

## Main statements

* `guessProbGiven_le`: the converse half of Theorem 1,
  `P[U = Û | Y = y] ≤ exp ℓ(X → y) · max_u P_U(u)`.
* `le_opPointwiseMaxLeakageRatio`: the achievability half of Theorem 1.
* `opPointwiseMaxLeakageRatio_eq`, `log_opPointwiseMaxLeakageRatio_eq`: **Theorem 1**, the
  operational definition equals the closed form `pointwiseMaxLeakage`.

## Implementation notes

The paper attains the supremum with the shattering channel of Issa–Wagner–Kamath
(Definition 2), which splits every `x ∈ supp P_X` into symbols of probability
`p_min = min_{x ∈ supp P_X} P_X(x)`, plus possibly one remainder symbol of smaller probability per
input (for prior masses `(0.4, 0.6)` the masses are `(0.4, 0.4, 0.2)`). For a single outcome a
simpler randomization suffices: if `x*` maximizes `P_{Y|X}(y | x)` on `supp P_X`, let
`U = (x*, 0)` when `X = x*`, and `U = (X, J)` with `J` uniform on `{1, …, k}` otherwise, for `k`
large enough that `1 / k < P_X(x*)`; see `le_opPointwiseMaxLeakageRatio`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β} {ρ : Kernel α γ} {g : Kernel β γ}

/-- The joint law of `(U, (Y, Û))` in the Markov chain `U - X - Y - Û`: `X ∼ μ`, `U` is drawn
from `X` through `ρ`, `Y` is drawn from `X` through `κ` (independently of `U` given `X`), and the
guess `Û` is drawn from `Y` through `g`. -/
noncomputable def guessLaw (μ : Measure α) (ρ : Kernel α γ) (κ : Kernel α β) (g : Kernel β γ) :
    Measure (γ × β × γ) :=
  (ρ ×ₖ ((Kernel.id ×ₖ g) ∘ₖ κ)) ∘ₘ μ

/-- `P[U = Û | Y = y] = P[U = Û, Y = y] / P[Y = y]` in the Markov chain `U - X - Y - Û`
(see `guessLaw`). -/
noncomputable def guessProbGiven (μ : Measure α) (ρ : Kernel α γ) (κ : Kernel α β)
    (g : Kernel β γ) (y : β) : ℝ≥0∞ :=
  guessLaw μ ρ κ g {p | p.2.1 = y ∧ p.1 = p.2.2} / (κ ∘ₘ μ) {y}

/-- The operational pointwise maximal leakage of Saeidian–Cervia–Oechtering–Skoglund
(Definition 1), multiplicative form: the supremum over all randomized functions `U` of `X` (with
values in some `Fin n`) of `sup_{P_{Û|Y}} P[U = Û | Y = y] / max_u P_U(u)`. -/
noncomputable def opPointwiseMaxLeakageRatio (μ : Measure α) (κ : Kernel α β) (y : β) :
    ℝ≥0∞ :=
  ⨆ (n : ℕ) (ρ : Kernel α (Fin n)) (_ : IsMarkovKernel ρ),
    (⨆ (g : Kernel β (Fin n)) (_ : IsMarkovKernel g), guessProbGiven μ ρ κ g y) /
      blindGuessProb μ ρ

section Formula

variable [Fintype α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ]

/-- `P[U = Û, Y = y]` as a finite sum. -/
lemma guessLaw_apply_eq_sum [IsMarkovKernel ρ] [IsMarkovKernel κ] [IsMarkovKernel g] (y : β) :
    guessLaw μ ρ κ g {p | p.2.1 = y ∧ p.1 = p.2.2} =
      ∑ x, ∑ u, g y {u} * κ x {y} * ρ x {u} * μ {x} := by
  classical
  have := Fintype.ofFinite β
  have h_pair (x : α) (u : γ) : ((Kernel.id ×ₖ g) ∘ₖ κ) x {(y, u)} = g y {u} * κ x {y} := by
    rw [Kernel.comp_apply_eq_sum _ _ _ (measurableSet_singleton _),
      Finset.sum_eq_single y (fun y' _ hy' ↦ ?_) (by simp)]
    · rw [Kernel.prod_apply, ← Set.singleton_prod_singleton, Measure.prod_prod, Kernel.id_apply,
        Measure.dirac_apply_of_mem rfl, one_mul]
    · rw [Kernel.prod_apply, ← Set.singleton_prod_singleton, Measure.prod_prod, Kernel.id_apply,
        Measure.dirac_apply' _ (measurableSet_singleton _)]
      simp [Ne.symm hy']
  have h_slice (x : α) :
      (ρ ×ₖ ((Kernel.id ×ₖ g) ∘ₖ κ)) x {p | p.2.1 = y ∧ p.1 = p.2.2} =
        ∑ u, g y {u} * κ x {y} * ρ x {u} := by
    rw [Kernel.prod_apply, Measure.prod_apply (Set.toFinite _).measurableSet, lintegral_fintype]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have : Prod.mk u ⁻¹' {p : γ × β × γ | p.2.1 = y ∧ p.1 = p.2.2} = {(y, u)} := by
      ext ⟨y', u'⟩
      simp [eq_comm]
    rw [this, h_pair]
  rw [guessLaw, Measure.bind_apply (Set.toFinite _).measurableSet
    (ρ ×ₖ ((Kernel.id ×ₖ g) ∘ₖ κ)).measurable.aemeasurable, lintegral_fintype]
  simp only [h_slice, Finset.sum_mul]

end Formula

section Converse

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [Finite γ] [MeasurableSingletonClass γ] [IsProbabilityMeasure μ] [IsMarkovKernel κ]

/-- **Converse half of Theorem 1** of Saeidian–Cervia–Oechtering–Skoglund: observing the
outcome `Y = y` multiplies the chance of guessing any randomized function `U` of `X` by at most
`exp ℓ(X → y)`, i.e. `P[U = Û | Y = y] ≤ exp ℓ(X → y) · max_u P_U(u)`. -/
theorem guessProbGiven_le [IsMarkovKernel ρ] [IsMarkovKernel g] (y : β) :
    guessProbGiven μ ρ κ g y ≤ pointwiseMaxLeakageRatio μ κ y * blindGuessProb μ ρ := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  set M := pointwiseMaxLeakageRatio μ κ y * (κ ∘ₘ μ) {y}
  refine ENNReal.div_le_of_le_mul ?_
  rw [guessLaw_apply_eq_sum]
  calc ∑ x, ∑ u, g y {u} * κ x {y} * ρ x {u} * μ {x}
      ≤ ∑ x, ∑ u, g y {u} * M * ρ x {u} * μ {x} :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦ by
          by_cases hx : μ {x} = 0
          · simp [hx]
          · gcongr
            exact apply_le_pointwiseMaxLeakageRatio_mul hx y
    _ = ∑ u, g y {u} * M * (ρ ∘ₘ μ) {u} := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [comp_apply_singleton, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by ring
    _ ≤ ∑ u, g y {u} * M * blindGuessProb μ ρ := by
        gcongr with u _
        exact le_iSup (fun u ↦ (ρ ∘ₘ μ) {u}) u
    _ = pointwiseMaxLeakageRatio μ κ y * blindGuessProb μ ρ * (κ ∘ₘ μ) {y} := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ,
          measure_univ, one_mul]
        ring

end Converse

section Relabel

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSingletonClass γ] [IsMarkovKernel κ]

omit [Fintype γ] in
/-- The guessing ratio of any finite alphabet `γ` for `U` and `Û` is bounded by the operational
pointwise maximal leakage, whose definition only ranges over the alphabets `Fin n`. -/
lemma guessProbGiven_div_le_opPointwiseMaxLeakageRatio [Finite γ] [IsMarkovKernel ρ]
    [IsMarkovKernel g] (y : β) :
    guessProbGiven μ ρ κ g y / blindGuessProb μ ρ ≤ opPointwiseMaxLeakageRatio μ κ y := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  set e := Fintype.equivFin γ
  have he : Measurable e := measurable_of_finite _
  have h_preimage (u : γ) : e ⁻¹' {e u} = {u} := by
    ext v
    simp
  have h_mapρ (a : α) (u : γ) : ρ.map e a {e u} = ρ a {u} := by
    rw [Kernel.map_apply' _ he _ (measurableSet_singleton _), h_preimage]
  have h_mapg (b : β) (u : γ) : g.map e b {e u} = g b {u} := by
    rw [Kernel.map_apply' _ he _ (measurableSet_singleton _), h_preimage]
  have hρ' := Kernel.IsMarkovKernel.map ρ he
  have hg' := Kernel.IsMarkovKernel.map g he
  have h_guess : guessProbGiven μ (ρ.map e) κ (g.map e) y = guessProbGiven μ ρ κ g y := by
    rw [guessProbGiven, guessProbGiven, guessLaw_apply_eq_sum, guessLaw_apply_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← e.sum_comp]
    simp [h_mapρ, h_mapg]
  have h_blind : blindGuessProb μ (ρ.map e) = blindGuessProb μ ρ := by
    rw [blindGuessProb, blindGuessProb, ← e.iSup_comp]
    simp_rw [comp_apply_singleton, h_mapρ]
  rw [← h_guess, ← h_blind]
  refine le_iSup_of_le (Fintype.card γ) <| le_iSup₂_of_le (ρ.map e) hρ' ?_
  refine ENNReal.div_le_div_right ?_ _
  exact le_iSup₂_of_le (f := fun g' (_ : IsMarkovKernel g') ↦ guessProbGiven μ (ρ.map e) κ g' y)
    (g.map e) hg' le_rfl

end Relabel

section Achievability

variable [Finite α] [MeasurableSingletonClass α] [Finite β] [MeasurableSingletonClass β]
  [IsProbabilityMeasure μ] [IsMarkovKernel κ]

/-- **Achievability half of Theorem 1** of Saeidian–Cervia–Oechtering–Skoglund. Let `x*` be an
atom of `μ` maximizing `κ x {y}`, and `k` an integer with `1 / k < P_X(x*)`. Take `U = (X, J)`
with `J ∈ {0, …, k}`: given `X = x*`, `U` is the *signal* symbol `(x*, 0)`, and given any other
`X = x`, `J` is uniform on `{1, …, k}`. Then `P_U(x*, 0) = P_X(x*)` and every other symbol has
probability at most `1 / k < P_X(x*)`, so `max_u P_U(u) ≤ P_X(x*)`, while always guessing
`(x*, 0)` succeeds with probability `P[U = Û | Y = y] = P_X(x*) · exp ℓ(X → y)`. This is a
simplification of the paper's construction through the shattering channel (Definition 2). -/
lemma le_opPointwiseMaxLeakageRatio {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    pointwiseMaxLeakageRatio μ κ y ≤ opPointwiseMaxLeakageRatio μ κ y := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  -- An atom `x*` of `μ` maximizing `κ x {y}`, and an integer `k` with `1 / k < P_X(x*)`.
  set S := Finset.univ.filter fun x : α ↦ μ {x} ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := μ.exists_measure_singleton_ne_zero
    exact ⟨x, by simpa [S] using hx⟩
  obtain ⟨xs, hxsS, hxs_max⟩ := S.exists_max_image (fun x ↦ κ x {y}) hS
  have hxs : μ {xs} ≠ 0 := by simpa [S] using hxsS
  have hR : pointwiseMaxLeakageRatio μ κ y = κ xs {y} / (κ ∘ₘ μ) {y} :=
    le_antisymm (iSup₂_le fun x hx ↦
        ENNReal.div_le_div_right (hxs_max x (by simpa [S] using hx)) _)
      (div_le_pointwiseMaxLeakageRatio hxs y)
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hxs
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by
    rintro h
    simp [h] at hk
  -- The randomization `ρ` producing `U = (X, J)`.
  set t : α → ℝ≥0∞ := fun x ↦ if x = xs then 1 else 0
  set w : α → α × Fin (k + 1) → ℝ≥0∞ := fun x p ↦
    if p.1 = x then (if p.2 = 0 then t x else (1 - t x) / k) else 0
  set ρ : Kernel α (α × Fin (k + 1)) :=
    Kernel.ofFunOfCountable fun x ↦ ∑ p, w x p • Measure.dirac p
  have hρ (x : α) (p : α × Fin (k + 1)) : ρ x {p} = w x p := by
    simp [ρ, Kernel.ofFunOfCountable, Measure.dirac_apply' _ (measurableSet_singleton p),
      Set.indicator]
  have ht_le (x : α) : t x ≤ 1 := by
    by_cases hx : x = xs <;> simp [t, hx]
  have hw_sum (x : α) : ∑ p, w x p = 1 := by
    rw [Fintype.sum_prod_type_right]
    simp only [w, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Fin.sum_univ_succ]
    simp only [ite_true, Fin.succ_ne_zero, ite_false, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm, ENNReal.div_mul_cancel hk0 (ENNReal.natCast_ne_top k),
      add_tsub_cancel_of_le (ht_le x)]
  have : IsMarkovKernel ρ := ⟨fun x ↦ ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton]
    simp_rw [hρ, hw_sum]⟩⟩
  -- The guessing rule: always guess the signal symbol `(x*, 0)`.
  set g : Kernel β (α × Fin (k + 1)) := Kernel.deterministic (fun _ ↦ (xs, 0)) measurable_const
  have hg : g y {(xs, 0)} = 1 := by simp [g, Kernel.deterministic_apply]
  -- `P_U(u) ≤ P_X(x*)` for every `u`.
  have h_blind : blindGuessProb μ ρ ≤ μ {xs} := by
    refine iSup_le fun p ↦ ?_
    rw [comp_apply_singleton, Finset.sum_eq_single p.1
      (fun x _ hx ↦ by simp [hρ, w, Ne.symm hx]) (by simp), hρ]
    by_cases hp : p.2 = 0
    · by_cases hx : p.1 = xs
      · simp [w, t, hp, hx]
      · simp [w, t, hp, hx]
    · simp only [w, ite_true, hp, ite_false]
      calc (1 - t p.1) / k * μ {p.1} ≤ 1 / k * 1 := by
            gcongr
            · exact tsub_le_self
            · exact prob_le_one
        _ ≤ μ {xs} := by simpa using hk.le
  -- `P[U = Û | Y = y] ≥ P_X(x*) · exp ℓ(X → y)`.
  have h_guess : pointwiseMaxLeakageRatio μ κ y * μ {xs} ≤ guessProbGiven μ ρ κ g y := by
    rw [guessProbGiven, ENNReal.le_div_iff_mul_le (Or.inl hy) (Or.inl (measure_ne_top _ _)), hR,
      mul_right_comm, ENNReal.div_mul_cancel hy (measure_ne_top _ _), guessLaw_apply_eq_sum]
    calc κ xs {y} * μ {xs} = g y {(xs, 0)} * κ xs {y} * ρ xs {(xs, 0)} * μ {xs} := by
          simp [hg, hρ, w, t]
      _ ≤ ∑ u, g y {u} * κ xs {y} * ρ xs {u} * μ {xs} :=
          Finset.single_le_sum (f := fun u ↦ g y {u} * κ xs {y} * ρ xs {u} * μ {xs})
            (fun _ _ ↦ zero_le) (Finset.mem_univ _)
      _ ≤ ∑ x, ∑ u, g y {u} * κ x {y} * ρ x {u} * μ {x} :=
          Finset.single_le_sum (f := fun x ↦ ∑ u, g y {u} * κ x {y} * ρ x {u} * μ {x})
            (fun _ _ ↦ zero_le) (Finset.mem_univ xs)
  calc pointwiseMaxLeakageRatio μ κ y = pointwiseMaxLeakageRatio μ κ y * μ {xs} / μ {xs} :=
        (ENNReal.mul_div_cancel_right hxs (measure_ne_top _ _)).symm
    _ ≤ guessProbGiven μ ρ κ g y / blindGuessProb μ ρ := ENNReal.div_le_div h_guess h_blind
    _ ≤ opPointwiseMaxLeakageRatio μ κ y := guessProbGiven_div_le_opPointwiseMaxLeakageRatio y

/-- **Theorem 1** of Saeidian–Cervia–Oechtering–Skoglund, multiplicative form: for finite
alphabets and every outcome `y` with `P_Y(y) > 0`, the operational pointwise maximal leakage
(Definition 1) equals `max_{x ∈ supp P_X} P_{Y|X}(y | x) / P_Y(y)`. -/
theorem opPointwiseMaxLeakageRatio_eq {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    opPointwiseMaxLeakageRatio μ κ y = pointwiseMaxLeakageRatio μ κ y := by
  refine le_antisymm (iSup_le fun n ↦ iSup₂_le fun ρ _ ↦ ?_) (le_opPointwiseMaxLeakageRatio hy)
  exact ENNReal.div_le_of_le_mul (iSup₂_le fun g _ ↦ guessProbGiven_le y)

/-- **Theorem 1** of Saeidian–Cervia–Oechtering–Skoglund: for finite alphabets and every outcome
`y` with `P_Y(y) > 0`, the operational pointwise maximal leakage of Definition 1,
`log sup_{P_{U|X}} (sup_{P_{Û|Y}} P[U = Û | Y = y]) / max_u P_U(u)`, equals the closed form
`ℓ(X → y) = log max_{x ∈ supp P_X} P_{X|Y=y}(x) / P_X(x)`. -/
theorem log_opPointwiseMaxLeakageRatio_eq {y : β} (hy : (κ ∘ₘ μ) {y} ≠ 0) :
    Real.log (opPointwiseMaxLeakageRatio μ κ y).toReal = pointwiseMaxLeakage μ κ y := by
  rw [opPointwiseMaxLeakageRatio_eq hy, pointwiseMaxLeakage]

end Achievability

end InformationTheory
