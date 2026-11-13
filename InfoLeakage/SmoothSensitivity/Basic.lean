/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Local sensitivity and smooth sensitivity

This file formalizes the sensitivity notions of K. Nissim, S. Raskhodnikova and A. Smith,
*Smooth sensitivity and sampling in private data analysis*, STOC 2007. Result numbers refer to
the full version (Draft Full Version v1.0, May 17, 2011, available from the authors' web pages).

A database is a vector `x : ι → D` of `n = |ι|` entries from a finite domain `D`, and the
distance `d(x, y)` between databases is the Hamming distance `hammingDist x y`; `x` and `y` are
neighbours if `d(x, y) = 1`. A query is a real-valued function `f : (ι → D) → ℝ` (the case
`d = 1` of the paper's `f : Dⁿ → ℝᵈ`).

**Restriction.** The paper allows an arbitrary domain `D` (its examples use `D = [0, Λ]`); here
`D` is **finite** in every result (`[Finite D]`). The definitions are stated for any `D`, but for
infinite `D` the `iSup`s may be unbounded, and then they take the junk value `0`.

## Main definitions

* `localSensitivity f x`: the local sensitivity `LS_f(x) = max_{y : d(x,y)=1} |f(x) - f(y)|`
  (Definition 1.6, real-valued case).
* `IsSmoothUpperBound f β S`: `S` is a `β`-smooth upper bound on `LS_f` (Definition 2.1).
* `smoothSensitivity f β x`: the `β`-smooth sensitivity
  `S*_{f,β}(x) = max_y LS_f(y) e^{-β d(x,y)}` (Definition 2.2).

## Main statements (paper result → Lean name)

* Lemma 2.3: `isSmoothUpperBound_smoothSensitivity` (for `β ≥ 0`, `S*_{f,β}` is a `β`-smooth
  upper bound on `LS_f`) and `IsSmoothUpperBound.smoothSensitivity_le` (it lies below every
  `β`-smooth upper bound); together, `isLeast_smoothSensitivity`.
* The global sensitivity of Definition 1.3 is a `0`-smooth upper bound (remark after
  Definition 2.1): `isSmoothUpperBound_const`.

## Implementation notes

The maxima of the paper are `iSup`s over finite index types (the domain `D` is finite), so they
are attained and the junk value of `sSup` on unbounded sets never occurs. An empty maximum (a
database without neighbours, i.e. `|D| = 1` or `n = 0`) has value `0`, the natural convention
for a nonnegative quantity.
-/

@[expose] public section

open Real

namespace InformationTheory

variable {ι D : Type*} [Fintype ι] [DecidableEq D] {f : (ι → D) → ℝ} {β : ℝ}

/-! ### Local sensitivity -/

/-- The **local sensitivity** `LS_f(x) = max_{y : d(x,y) = 1} |f(x) - f(y)|` of a real-valued
query `f` at the database `x` (Nissim–Raskhodnikova–Smith, Definition 1.6, with `d = 1`), where
`d` is the Hamming distance. It is `0` if `x` has no neighbour. For infinite `D` and unbounded
differences the `iSup` takes the junk value `0`; all results assume `[Finite D]`. -/
noncomputable def localSensitivity (f : (ι → D) → ℝ) (x : ι → D) : ℝ :=
  ⨆ y : {y : ι → D // hammingDist x y = 1}, |f x - f y|

lemma localSensitivity_nonneg (f : (ι → D) → ℝ) (x : ι → D) : 0 ≤ localSensitivity f x :=
  Real.iSup_nonneg fun _ ↦ abs_nonneg _

lemma abs_sub_le_localSensitivity [Finite D] {x y : ι → D} (h : hammingDist x y = 1) :
    |f x - f y| ≤ localSensitivity f x :=
  le_ciSup (f := fun y : {y : ι → D // hammingDist x y = 1} ↦ |f x - f y|)
    (Set.finite_range _).bddAbove ⟨y, h⟩

lemma localSensitivity_le {x : ι → D} {c : ℝ} (h : ∀ y, hammingDist x y = 1 → |f x - f y| ≤ c)
    (hc : 0 ≤ c) : localSensitivity f x ≤ c :=
  Real.iSup_le (fun y ↦ h y.1 y.2) hc

/-! ### Smooth upper bounds -/

/-- `S` is a **`β`-smooth upper bound** on the local sensitivity of `f`
(Nissim–Raskhodnikova–Smith, Definition 2.1): `S(x) ≥ LS_f(x)` for every database `x`
(requirement (1)), and `S(x) ≤ e^β S(y)` for all neighbours `x, y` (requirement (2)). The paper
takes `S` with values in `ℝ⁺` and `β > 0`; nonnegativity follows from (1) (`nonneg`), and we
allow any real `β`. -/
structure IsSmoothUpperBound (f : (ι → D) → ℝ) (β : ℝ) (S : (ι → D) → ℝ) : Prop where
  localSensitivity_le (x : ι → D) : localSensitivity f x ≤ S x
  le_exp_mul ⦃x y : ι → D⦄ : hammingDist x y = 1 → S x ≤ exp β * S y

namespace IsSmoothUpperBound

variable {S : (ι → D) → ℝ}

lemma nonneg (hS : IsSmoothUpperBound f β S) (x : ι → D) : 0 ≤ S x :=
  (localSensitivity_nonneg f x).trans (hS.localSensitivity_le x)

lemma abs_sub_le [Finite D] (hS : IsSmoothUpperBound f β S) {x y : ι → D}
    (h : hammingDist x y = 1) : |f x - f y| ≤ S x :=
  (abs_sub_le_localSensitivity h).trans (hS.localSensitivity_le x)

/-- A `β`-smooth upper bound is `β'`-smooth for every `β' ≥ β`. -/
lemma mono {β' : ℝ} (hS : IsSmoothUpperBound f β S) (hβ : β ≤ β') :
    IsSmoothUpperBound f β' S where
  localSensitivity_le := hS.localSensitivity_le
  le_exp_mul x y h := (hS.le_exp_mul h).trans <| by
    gcongr
    exact hS.nonneg y

end IsSmoothUpperBound

/-- A constant upper bound `c` on `|f(x) - f(y)|` over all neighbours (for instance the global
sensitivity of Definition 1.3) is a `0`-smooth upper bound on `LS_f` (remark after
Nissim–Raskhodnikova–Smith, Definition 2.1). -/
lemma isSmoothUpperBound_const {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y : ι → D, hammingDist x y = 1 → |f x - f y| ≤ c) :
    IsSmoothUpperBound f 0 fun _ ↦ c where
  localSensitivity_le x := localSensitivity_le (h x) hc
  le_exp_mul _ _ _ := by simp

/-! ### Smooth sensitivity -/

namespace SmoothSensitivity

/-- If `d(x, y) = k + 1`, there is a neighbour `x'` of `x` with `d(x', y) = k`: change one
coordinate where `x` and `y` differ. -/
lemma exists_hammingDist_eq_one {x y : ι → D} {k : ℕ} (h : hammingDist x y = k + 1) :
    ∃ x', hammingDist x x' = 1 ∧ hammingDist x' y = k := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! hc
    simp [funext hc] at h
  refine ⟨Function.update x i (y i), ?_, ?_⟩
  · rw [hammingDist, ← Finset.card_singleton i]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]
  · have hfilter : Finset.univ.filter (fun j ↦ Function.update x i (y i) j ≠ y j) =
        (Finset.univ.filter fun j ↦ x j ≠ y j).erase i := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [hammingDist] at h
    rw [hammingDist, hfilter, Finset.card_erase_of_mem (by simpa using hi), h, Nat.add_sub_cancel]

end SmoothSensitivity

open SmoothSensitivity

/-- The **`β`-smooth sensitivity** `S*_{f,β}(x) = max_y LS_f(y) e^{-β d(x,y)}` of `f` at `x`
(Nissim–Raskhodnikova–Smith, Definition 2.2), the maximum ranging over all databases `y`. For
infinite `D` the `iSup` may be unbounded and then takes the junk value `0`; all results assume
`[Finite D]`. -/
noncomputable def smoothSensitivity (f : (ι → D) → ℝ) (β : ℝ) (x : ι → D) : ℝ :=
  ⨆ y : ι → D, localSensitivity f y * exp (-(β * hammingDist x y))

lemma le_smoothSensitivity [Finite D] (x y : ι → D) :
    localSensitivity f y * exp (-(β * hammingDist x y)) ≤ smoothSensitivity f β x :=
  le_ciSup (f := fun y ↦ localSensitivity f y * exp (-(β * hammingDist x y)))
    (Set.finite_range _).bddAbove y

/-- Requirement (1) of Definition 2.1 for `S*_{f,β}` (first part of the proof of
Nissim–Raskhodnikova–Smith, Lemma 2.3). -/
lemma localSensitivity_le_smoothSensitivity [Finite D] (x : ι → D) :
    localSensitivity f x ≤ smoothSensitivity f β x := by
  simpa using le_smoothSensitivity (f := f) (β := β) x x

/-- Requirement (2) of Definition 2.1 for `S*_{f,β}` with `β ≥ 0` (second part of the proof of
Nissim–Raskhodnikova–Smith, Lemma 2.3). -/
lemma smoothSensitivity_le_exp_mul [Finite D] (hβ : 0 ≤ β) {x y : ι → D}
    (h : hammingDist x y = 1) : smoothSensitivity f β x ≤ exp β * smoothSensitivity f β y := by
  have : Nonempty (ι → D) := ⟨x⟩
  refine ciSup_le fun z ↦ ?_
  have htri : (hammingDist y z : ℝ) ≤ 1 + hammingDist x z := by
    have := hammingDist_triangle y x z
    rw [hammingDist_comm y x, h] at this
    exact_mod_cast this
  have hexp : exp (-(β * hammingDist x z)) ≤ exp β * exp (-(β * hammingDist y z)) := by
    rw [← exp_add]
    exact exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left htri hβ])
  calc localSensitivity f z * exp (-(β * hammingDist x z))
      ≤ localSensitivity f z * (exp β * exp (-(β * hammingDist y z))) :=
        mul_le_mul_of_nonneg_left hexp (localSensitivity_nonneg f z)
    _ = exp β * (localSensitivity f z * exp (-(β * hammingDist y z))) := by ring
    _ ≤ exp β * smoothSensitivity f β y := by
        gcongr
        exact le_smoothSensitivity y z

/-- **Nissim–Raskhodnikova–Smith, Lemma 2.3** (first part): for `β ≥ 0`, the smooth sensitivity
`S*_{f,β}` is a `β`-smooth upper bound on the local sensitivity of `f`. (The paper takes
`β > 0`.) -/
theorem isSmoothUpperBound_smoothSensitivity [Finite D] (hβ : 0 ≤ β) :
    IsSmoothUpperBound f β (smoothSensitivity f β) where
  localSensitivity_le := localSensitivity_le_smoothSensitivity
  le_exp_mul _ _ h := smoothSensitivity_le_exp_mul hβ h

/-- **Nissim–Raskhodnikova–Smith, Lemma 2.3** (second part): every `β`-smooth upper bound `S` on
the local sensitivity of `f` satisfies `S*_{f,β}(x) ≤ S(x)` for all `x`. As in the paper, the
proof shows `S(x) ≥ LS_f(y) e^{-β d(x,y)}` by induction on `d(x, y)`; it needs no sign
condition on `β`. -/
theorem IsSmoothUpperBound.smoothSensitivity_le {S : (ι → D) → ℝ}
    (hS : IsSmoothUpperBound f β S) (x : ι → D) : smoothSensitivity f β x ≤ S x := by
  have : Nonempty (ι → D) := ⟨x⟩
  refine ciSup_le fun y ↦ ?_
  suffices H : ∀ k : ℕ, ∀ x : ι → D, hammingDist x y = k →
      localSensitivity f y * exp (-(β * k)) ≤ S x from H _ x rfl
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [hammingDist_eq_zero.1 hx]
    simpa using hS.localSensitivity_le y
  | succ k ih =>
    intro x hx
    obtain ⟨x', hxx', hx'y⟩ := exists_hammingDist_eq_one hx
    have h₁ := hS.le_exp_mul (by rwa [hammingDist_comm] : hammingDist x' x = 1)
    calc localSensitivity f y * exp (-(β * ↑(k + 1)))
        = exp (-β) * (localSensitivity f y * exp (-(β * k))) := by
          rw [mul_left_comm, ← exp_add]
          congr 2
          push_cast
          ring
      _ ≤ exp (-β) * S x' := by
          gcongr
          exact ih x' hx'y
      _ ≤ exp (-β) * (exp β * S x) := by gcongr
      _ = S x := by rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- **Nissim–Raskhodnikova–Smith, Lemma 2.3**: for `β ≥ 0`, the smooth sensitivity `S*_{f,β}`
is the smallest `β`-smooth upper bound on the local sensitivity of `f`. -/
theorem isLeast_smoothSensitivity [Finite D] (hβ : 0 ≤ β) :
    IsLeast {S | IsSmoothUpperBound f β S} (smoothSensitivity f β) :=
  ⟨isSmoothUpperBound_smoothSensitivity hβ, fun _ hS x ↦ hS.smoothSensitivity_le x⟩

lemma smoothSensitivity_nonneg [Finite D] (hβ : 0 ≤ β) (x : ι → D) :
    0 ≤ smoothSensitivity f β x :=
  (isSmoothUpperBound_smoothSensitivity hβ).nonneg x

end InformationTheory
