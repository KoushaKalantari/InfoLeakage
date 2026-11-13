/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.DP.Basic
public import InfoLeakage.DirectedInfo.Basic
public import InfoLeakage.FInformation.Pinsker
public import Mathlib.InformationTheory.Hamming

/-!
# Differential privacy as a mutual information constraint

This file formalizes the main results of P. Cuff and L. Yu, *Differential privacy as a mutual
information constraint*, Proc. ACM CCS 2016 ([arXiv:1608.03677](https://arxiv.org/abs/1608.03677));
numbers refer to arXiv v1.

A database `X = (X_i)_{i ∈ ι}` has its `i`-th entry in a finite alphabet `𝓧 i`, and a mechanism is
a Markov kernel `M` from databases to a finite output alphabet `𝓨`. Two databases are neighbours
(Definition 3) if their Hamming distance is one, and `(ε, δ)`-DP (Definitions 1, 4 and 5) is
`IsEpsDeltaDP M (fun x x' ↦ hammingDist x x' = 1) ε δ`; the two inequalities (5)–(6) of
`(ε, δ)`-closeness are its two instances for the symmetric neighbour relation. Information is
measured in nats.

## Main definitions

* `entryCondMutualInfo P M i`: the conditional mutual information `I(X_i; Y | X^{-i})` under the
  joint law `P ⊗ₘ M` of the database and the output, as a finite sum
  (`DirectedInfo.condMutualInfoSum`).
* `IsMIDP M ε`: `ε`-mutual-information differential privacy, `sup_{i, P} I(X_i; Y | X^{-i}) ≤ ε`
  (Definition 2).
* `IsKLDP M ε`: `ε`-KL differential privacy (Definition 7).

## Main statements (paper result → Lean name)

* Property 1, (11) → `klDivSum_le_of_forall_le_exp_mul`; (10) →
  `klDivSum_le_min_of_forall_le_exp_mul`; the relaxation (82) →
  `MutualInfoDP.capacity_bound_le_min`.
* Lemma 1, (21) → `IsEpsDP.isKLDP_min`; (22) → `IsKLDP.isMIDP`; (23) → `IsEpsDP.isMIDP_min`
  (and the weaker bound `ε` in `IsEpsDP.isMIDP`).
* Lemma 2, (27) → `IsMIDP.isEpsDeltaDP`: `ε`-MI-DP implies `(0, √(2ε))`-DP.
* Theorem 1, (17), in the sense of Definition 8 →
  `isEpsDP_succeeds_isMIDP_succeeds_isEpsDeltaDP`, with the explicit witnesses `α = β` and
  `α = δ² / 2`, which depend on neither the mechanism nor the (finite) alphabets.
* The formula `I(X_i; Y | X^{-i}) = ∑_{x,y} P(x) M(y | x) log (M(y | x) / M̄(y | x^{-i}))` behind
  (24) → `MutualInfoDP.entryCondMutualInfo_eq`; for a uniform law on two neighbours it is a
  Jensen–Shannon divergence → `MutualInfoDP.entryCondMutualInfo_twoPoint`.

## Implementation notes

* Property 1 is stated for probability vectors on a finite alphabet and `klDivSum`; it transfers
  to Mathlib's `klDiv` through `klDiv_eq_ofReal_klDivSum`, as in `IsEpsDP.isKLDP_min`.
* (23) is proved directly rather than by chaining (21) and (22): in
  `I(X_i; Y | X^{-i}) = E[D(M(X) ‖ M̄(X^{-i}))]` the mixture `M̄(x^{-i})` of the output laws of the
  databases agreeing with `x` outside entry `i` is itself `(ε, 0)`-close to `M x`, so Property 1
  applies to it (`MutualInfoDP.entryCondMutualInfo_le_min_of_forall`). The paper's route is also
  formalized, (22) by Jensen's inequality for `log`.
* Lemma 2 is proved with the uniform prior on two neighbouring databases, under which
  `I(X_i; Y | X^{-i})` is the Jensen–Shannon divergence of the two output laws
  (`MutualInfoDP.entryCondMutualInfo_twoPoint`), and Pinsker's inequality
  (`ofReal_two_mul_sq_measureReal_sub_le_klDiv`) for each of its two halves. This is neither the
  paper's binary-channel reduction nor exactly Appendix C's alternative argument (Pinsker against
  the centre of the information ball), but gives the same constant `√(2ε)` of (27).
* The agreement of `DirectedInfo.condMutualInfoSum` with Statlib's `condMutualInfo` is not
  formalized (see `InfoLeakage.DirectedInfo.Basic`).

## Notes on the paper

* Section 4.2, proofs of Corollary 2 ((43)) and Corollary 4 ((44)): the left-hand sides read
  `I(X_i; Y^k | X^{-1})`, a misprint for `I(X_i; Y^k | X^{-i})`. The corollaries are unaffected
  (they are not formalized here).

## Not formalized

* The tightness of (11) (equality for a pair of binary distributions), the tight forms (28) and
  (33) of Lemma 2, Properties 2 and 3, and Lemma 3 (the reverse direction
  `(δ)-DP ⟹ ε'-MI-DP` under a cardinality bound, i.e. (18) of Theorem 1), which needs a
  continuity bound for entropy; Example 2; the strictness of the orderings (A) and (B).
* Section 4 (Corollaries 1–4), Section 5 (Example 5, Corollary 5) and Sections 6–7 (variants of
  DP, Lemma 4 and Corollary 6 on Rényi information).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

namespace InformationTheory

variable {ι : Type*} {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {𝓨 : Type*} [MeasurableSpace 𝓨]

namespace MutualInfoDP

/-- The database `x^{-i}` with its `i`-th entry removed. -/
def rest (i : ι) (x : (j : ι) → 𝓧 j) : (j : {j // j ≠ i}) → 𝓧 j := fun j ↦ x j

omit [∀ i, MeasurableSpace (𝓧 i)] in
/-- `x^{-i} = x'^{-i}` iff `x` and `x'` agree outside the `i`-th entry. -/
lemma rest_eq_rest_iff {i : ι} {x x' : (j : ι) → 𝓧 j} :
    rest i x = rest i x' ↔ ∀ j, j ≠ i → x j = x' j := by
  refine ⟨fun h j hj ↦ congrFun h ⟨j, hj⟩, fun h ↦ funext fun j ↦ h j j.2⟩

omit [∀ i, MeasurableSpace (𝓧 i)] in
/-- A database is determined by its `i`-th entry and the other entries. -/
lemma apply_eq_and_rest_eq_iff {i : ι} {x x' : (j : ι) → 𝓧 j} :
    x i = x' i ∧ rest i x = rest i x' ↔ x = x' := by
  refine ⟨fun ⟨h₁, h₂⟩ ↦ funext fun j ↦ ?_, fun h ↦ h ▸ ⟨rfl, rfl⟩⟩
  by_cases hj : j = i
  · subst hj; exact h₁
  · exact rest_eq_rest_iff.1 h₂ j hj

end MutualInfoDP

open MutualInfoDP

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (𝓧 i)] [Fintype 𝓨]

/-- The conditional mutual information `I(X_i; Y | X^{-i})` (in nats) between the `i`-th entry
of a database `X ∼ P` and the output `Y` of the mechanism `M`, given the other entries. -/
noncomputable def entryCondMutualInfo (P : Measure ((i : ι) → 𝓧 i)) (M : Kernel ((i : ι) → 𝓧 i) 𝓨)
    (i : ι) : ℝ :=
  DirectedInfo.condMutualInfoSum (P ⊗ₘ M) (fun ω ↦ ω.1 i) Prod.snd (fun ω ↦ rest i ω.1)

namespace MutualInfoDP

variable {P : Measure ((i : ι) → 𝓧 i)} {M : Kernel ((i : ι) → 𝓧 i) 𝓨}

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (𝓧 i)] [Fintype 𝓨] in
/-- The point masses of the joint law `P ⊗ₘ M`. -/
private lemma compProd_real_singleton {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] {P : Measure α} {M : Kernel α β}
    [IsFiniteMeasure P] [IsMarkovKernel M] (x : α) (y : β) :
    (P ⊗ₘ M).real {(x, y)} = P.real {x} * (M x).real {y} := by
  rw [← Set.singleton_prod_singleton, measureReal_def,
    Measure.compProd_apply_prod (.singleton x) (.singleton y), lintegral_singleton,
    ENNReal.toReal_mul, mul_comm]
  rfl

/-- The probability of a set under the joint law `P ⊗ₘ M`, as a finite sum. -/
private lemma compProd_real_eq_sum [∀ i, MeasurableSingletonClass (𝓧 i)]
    [MeasurableSingletonClass 𝓨] [IsFiniteMeasure P] [IsMarkovKernel M]
    (T : Set (((i : ι) → 𝓧 i) × 𝓨)) [DecidablePred (· ∈ T)] :
    (P ⊗ₘ M).real T = ∑ x, ∑ y, if (x, y) ∈ T then P.real {x} * (M x).real {y} else 0 := by
  classical
  have : (P ⊗ₘ M).real T = ∑ ω with ω ∈ T, (P ⊗ₘ M).real {ω} := by
    rw [sum_measureReal_singleton]; congr 1; ext; simp
  rw [this, sum_filter, Fintype.sum_prod_type]
  simp only [compProd_real_singleton]

variable [∀ i, DecidableEq (𝓧 i)] [∀ i, MeasurableSingletonClass (𝓧 i)]
  [MeasurableSingletonClass 𝓨] [IsProbabilityMeasure P] [IsMarkovKernel M]

/-- The explicit form of `I(X_i; Y | X^{-i})`: writing `A(x) = P(X^{-i} = x^{-i})` and
`B(x, y) = P(X^{-i} = x^{-i}, Y = y)`, it is
`∑_{x,y} P(x) M(y | x) log (P(x) M(y | x) A(x) / (P(x) B(x, y)))`, i.e. the average of
`log (M(y | x) / M̄(y | x^{-i}))` with `M̄(y | x^{-i}) = B(x, y) / A(x)`, as in (24). -/
theorem entryCondMutualInfo_eq (i : ι) :
    entryCondMutualInfo P M i = ∑ x, ∑ y, P.real {x} * (M x).real {y} *
      log (P.real {x} * (M x).real {y} * (∑ a with rest i a = rest i x, P.real {a}) /
        (P.real {x} * ∑ a with rest i a = rest i x, P.real {a} * (M a).real {y})) := by
  classical
  rw [entryCondMutualInfo, DirectedInfo.condMutualInfoSum, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
  have hrest : (P ⊗ₘ M).real ((fun ω ↦ rest i ω.1) ⁻¹' {rest i x}) =
      ∑ a with rest i a = rest i x, P.real {a} := by
    rw [compProd_real_eq_sum, sum_filter]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    split_ifs <;> simp [← mul_sum]
  have happ : (P ⊗ₘ M).real ((fun ω ↦ (ω.1 i, rest i ω.1)) ⁻¹' {(x i, rest i x)}) =
      P.real {x} := by
    rw [compProd_real_eq_sum]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, apply_eq_and_rest_eq_iff]
    simp [← mul_sum]
  have hsnd : (P ⊗ₘ M).real ((fun ω ↦ (ω.2, rest i ω.1)) ⁻¹' {(y, rest i x)}) =
      ∑ a with rest i a = rest i x, P.real {a} * (M a).real {y} := by
    rw [compProd_real_eq_sum, sum_filter]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    split_ifs with h <;> simp [h]
  have hfull : (fun ω : ((i : ι) → 𝓧 i) × 𝓨 ↦ (ω.1 i, ω.2, rest i ω.1)) ⁻¹'
      {(x i, y, rest i x)} = {(x, y)} := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    rw [← apply_eq_and_rest_eq_iff (i := i)]
    tauto
  simp only [DirectedInfo.probEq, compProd_real_singleton, hfull, hrest, happ, hsnd]

omit [∀ i, DecidableEq (𝓧 i)] in
/-- A bound on `I(X_i; Y | X^{-i})` from a pointwise lower bound on the likelihood of the output
when the `i`-th entry is changed. -/
theorem entryCondMutualInfo_le_of_forall {ε : ℝ} (i : ι)
    (h : ∀ x a, rest i a = rest i x → ∀ y, exp (-ε) * (M x).real {y} ≤ (M a).real {y}) :
    entryCondMutualInfo P M i ≤ ε := by
  classical
  rw [entryCondMutualInfo_eq]
  have htot : ∑ x, ∑ y, P.real {x} * (M x).real {y} * ε = ε := by
    simp [← mul_sum, ← sum_mul]
  rw [← htot]
  refine sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ ?_
  set A := ∑ a with rest i a = rest i x, P.real {a}
  set B := ∑ a with rest i a = rest i x, P.real {a} * (M a).real {y}
  have hW := measureReal_nonneg (μ := M x) (s := {y})
  have hPx := measureReal_nonneg (μ := P) (s := {x})
  rcases (mul_nonneg hPx hW).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  have hPx' : 0 < P.real {x} := lt_of_le_of_ne hPx fun h ↦ by simp [← h] at hpos
  have hW' : 0 < (M x).real {y} := lt_of_le_of_ne hW fun h ↦ by simp [← h] at hpos
  have hA : P.real {x} ≤ A :=
    single_le_sum (f := fun a ↦ P.real {a}) (fun _ _ ↦ measureReal_nonneg) (by simp)
  have hB : exp (-ε) * (M x).real {y} * A ≤ B := by
    rw [mul_sum]
    refine sum_le_sum fun a ha ↦ ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (h x a (mem_filter.1 ha).2 y) measureReal_nonneg
  have hApos : 0 < A := hPx'.trans_le hA
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hB
  rw [log_le_iff_le_exp (by positivity), div_le_iff₀ (by positivity)]
  calc P.real {x} * (M x).real {y} * A
      = exp ε * P.real {x} * (exp (-ε) * (M x).real {y} * A) := by
        rw [show exp ε * P.real {x} * (exp (-ε) * (M x).real {y} * A) =
          (exp ε * exp (-ε)) * (P.real {x} * (M x).real {y} * A) by ring, ← exp_add]
        simp
    _ ≤ exp ε * P.real {x} * B := mul_le_mul_of_nonneg_left hB (mul_pos (exp_pos _) hPx').le
    _ = exp ε * (P.real {x} * B) := by ring

end MutualInfoDP

/-! ### Hamming neighbours -/

namespace MutualInfoDP

variable [∀ i, DecidableEq (𝓧 i)]

omit [DecidableEq ι] [∀ i, MeasurableSpace (𝓧 i)] [∀ i, Fintype (𝓧 i)] in
/-- Two distinct databases that agree outside the `i`-th entry are Hamming neighbours. -/
lemma hammingDist_eq_one_of_rest_eq {i : ι} {x x' : (j : ι) → 𝓧 j} (h : rest i x = rest i x')
    (hne : x ≠ x') : hammingDist x x' = 1 := by
  classical
  refine le_antisymm ?_ (Nat.one_le_iff_ne_zero.2 (hammingDist_ne_zero.2 hne))
  calc hammingDist x x' ≤ ({i} : Finset ι).card := by
        refine card_le_card fun j hj ↦ ?_
        by_contra hji
        exact (mem_filter.1 hj).2 (rest_eq_rest_iff.1 h j (by simpa using hji))
    _ = 1 := card_singleton i

omit [DecidableEq ι] [∀ i, MeasurableSpace (𝓧 i)] [∀ i, Fintype (𝓧 i)] in
/-- Hamming neighbours differ in exactly one entry `i`, and agree outside it. -/
lemma exists_rest_eq_of_hammingDist_eq_one {x x' : (j : ι) → 𝓧 j} (h : hammingDist x x' = 1) :
    ∃ i, x i ≠ x' i ∧ rest i x = rest i x' := by
  obtain ⟨i, hi⟩ := card_eq_one.1 h
  have hmem (j : ι) : x j ≠ x' j ↔ j = i := by
    simpa using Finset.ext_iff.1 hi j
  refine ⟨i, (hmem i).2 rfl, rest_eq_rest_iff.2 fun j hj ↦ ?_⟩
  by_contra hne
  exact hj ((hmem j).1 hne)

end MutualInfoDP

/-! ### Property 1: `(ε, 0)`-closeness bounds the Kullback–Leibler divergence -/

namespace MutualInfoDP

/-- The chord bound for the convex function `t ↦ t log t` on `[a, b]`. -/
private lemma mul_log_le_chord {a b t : ℝ} (ha : 0 < a) (hab : a < b) (hat : a ≤ t)
    (htb : t ≤ b) :
    t * log t ≤ ((b - t) * (a * log a) + (t - a) * (b * log b)) / (b - a) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h := convexOn_mul_log.2 (Set.mem_Ici.2 ha.le) (Set.mem_Ici.2 (ha.trans hab).le)
    (div_nonneg (sub_nonneg.2 htb) hba.le) (div_nonneg (sub_nonneg.2 hat) hba.le)
    (by field_simp; ring)
  have ht : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by
    field_simp; ring
  simp only [smul_eq_mul, ht] at h
  refine h.trans_eq ?_
  field_simp

end MutualInfoDP

open MutualInfoDP in
/-- **Cuff–Yu, Property 1, (11)**, for distributions on a finite alphabet: if `p` and `q` are
`(ε, 0)`-close, i.e. `p ≤ e^ε q` and `q ≤ e^ε p` pointwise, then
`D(p ‖ q) ≤ ε (e^ε - 1)(1 - e^{-ε}) / ((e^ε - 1) + (1 - e^{-ε}))` nats. The proof is the one of
Appendix A: `z ↦ z log z` lies below its chord on `[e^{-ε}, e^ε]`. -/
theorem klDivSum_le_of_forall_le_exp_mul {β : Type*} [Fintype β] {p q : β → ℝ}
    (hp₀ : ∀ z, 0 ≤ p z) (hq₀ : ∀ z, 0 ≤ q z) (hp₁ : ∑ z, p z = 1) (hq₁ : ∑ z, q z = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (h₁ : ∀ z, p z ≤ exp ε * q z) (h₂ : ∀ z, q z ≤ exp ε * p z) :
    klDivSum p q ≤ ε * (exp ε - 1) * (1 - exp (-ε)) / ((exp ε - 1) + (1 - exp (-ε))) := by
  rcases hε.eq_or_lt with rfl | hε
  · have hpq (z : β) : p z = q z := le_antisymm (by simpa using h₁ z) (by simpa using h₂ z)
    simp [klDivSum, hpq]
  set a := exp (-ε)
  set b := exp ε
  have ha : 0 < a := exp_pos _
  have hab : a < b := exp_lt_exp.2 (by linarith)
  have hp_zero (z : β) (hz : q z = 0) : p z = 0 := le_antisymm (by simpa [hz] using h₁ z) (hp₀ z)
  have key (z : β) : p z * log (p z / q z) ≤
      ((b * q z - p z) * (a * log a) + (p z - a * q z) * (b * log b)) / (b - a) := by
    rcases (hq₀ z).eq_or_lt with hz | hz
    · simp [hp_zero z hz.symm, ← hz]
    have hlo : a ≤ p z / q z := by
      rw [le_div_iff₀ hz]
      have := h₂ z
      have hab' : a * b = 1 := by rw [← exp_add]; simp
      nlinarith [exp_pos ε]
    have hhi : p z / q z ≤ b := by rw [div_le_iff₀ hz]; linarith [h₁ z]
    have := mul_log_le_chord ha hab hlo hhi
    have hpz : p z = q z * (p z / q z) := by field_simp
    calc p z * log (p z / q z) = q z * (p z / q z * log (p z / q z)) := by
          rw [← mul_assoc, ← hpz]
      _ ≤ q z * (((b - p z / q z) * (a * log a) + (p z / q z - a) * (b * log b)) / (b - a)) :=
          mul_le_mul_of_nonneg_left this hz.le
      _ = _ := by field_simp
  calc klDivSum p q ≤ ∑ z, ((b * q z - p z) * (a * log a) + (p z - a * q z) * (b * log b)) /
        (b - a) := sum_le_sum fun z _ ↦ key z
    _ = ((b - 1) * (a * log a) + (1 - a) * (b * log b)) / (b - a) := by
        rw [← sum_div]
        simp only [sub_mul, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hp₁, hq₁]
        ring_nf
    _ = _ := by
        have hab1 : a * b = 1 := by rw [← exp_add]; simp
        simp only [a, b, log_exp] at hab1 ⊢
        field_simp
        rw [show exp ε - 1 + (1 - exp (-ε)) = exp ε - exp (-ε) by ring]
        congr 1
        linear_combination (-1 : ℝ) * hab1

/-- The relaxation (82) of Cuff–Yu: `ε (e^ε - 1)(1 - e^{-ε}) / ((e^ε - 1) + (1 - e^{-ε}))` is at
most `min {ε, ε²}` for `ε ≥ 0`. -/
lemma MutualInfoDP.capacity_bound_le_min {ε : ℝ} (hε : 0 ≤ ε) :
    ε * (exp ε - 1) * (1 - exp (-ε)) / ((exp ε - 1) + (1 - exp (-ε))) ≤ min ε (ε ^ 2) := by
  set u := exp ε - 1
  set v := 1 - exp (-ε)
  have hu : 0 ≤ u := sub_nonneg.2 (one_le_exp hε)
  have hv : 0 ≤ v := sub_nonneg.2 (exp_le_one_iff.2 (by linarith))
  have hv₁ : v ≤ 1 := by have := exp_pos (-ε); linarith
  have hvε : v ≤ ε := by have := add_one_le_exp (-ε); linarith
  have h : ε * u * v / (u + v) ≤ ε * v := by
    rcases (add_nonneg hu hv).eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; positivity
    rw [div_le_iff₀ h0]
    nlinarith [mul_nonneg hε hv]
  refine h.trans (le_min ?_ ?_)
  · nlinarith
  · rw [sq]; exact mul_le_mul_of_nonneg_left hvε hε

/-- **Cuff–Yu, Property 1, (10)**, for distributions on a finite alphabet: if `p` and `q` are
`(ε, 0)`-close, then `D(p ‖ q) ≤ min {ε, ε²}` nats. -/
theorem klDivSum_le_min_of_forall_le_exp_mul {β : Type*} [Fintype β] {p q : β → ℝ}
    (hp₀ : ∀ z, 0 ≤ p z) (hq₀ : ∀ z, 0 ≤ q z) (hp₁ : ∑ z, p z = 1) (hq₁ : ∑ z, q z = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (h₁ : ∀ z, p z ≤ exp ε * q z) (h₂ : ∀ z, q z ≤ exp ε * p z) :
    klDivSum p q ≤ min ε (ε ^ 2) :=
  (klDivSum_le_of_forall_le_exp_mul hp₀ hq₀ hp₁ hq₁ hε h₁ h₂).trans
    (MutualInfoDP.capacity_bound_le_min hε)

/-! ### Mutual-information differential privacy -/

/-- **Mutual-information differential privacy** (Cuff–Yu, Definition 2): a mechanism `M` from
databases `X = (X_i)_i` to outputs `Y` is `ε`-MI-DP if `sup_{i, P_X} I(X_i; Y | X^{-i}) ≤ ε`
nats, the supremum being over all entries `i` and all laws `P_X` of the database. -/
def IsMIDP (M : Kernel ((i : ι) → 𝓧 i) 𝓨) (ε : ℝ) : Prop :=
  ∀ (P : Measure ((i : ι) → 𝓧 i)) [IsProbabilityMeasure P] (i : ι), entryCondMutualInfo P M i ≤ ε

variable [∀ i, DecidableEq (𝓧 i)] [∀ i, MeasurableSingletonClass (𝓧 i)]
  [MeasurableSingletonClass 𝓨] {M : Kernel ((i : ι) → 𝓧 i) 𝓨} [IsMarkovKernel M] {ε : ℝ}

omit [∀ i, DecidableEq (𝓧 i)] in
/-- A bound on `I(X_i; Y | X^{-i})` by `min {ε, ε²}` when changing the `i`-th entry changes the
likelihood of each output by a factor at most `e^ε`. -/
theorem MutualInfoDP.entryCondMutualInfo_le_min_of_forall {P : Measure ((i : ι) → 𝓧 i)}
    [IsProbabilityMeasure P] (hε : 0 ≤ ε) (i : ι)
    (h : ∀ x a, rest i a = rest i x → ∀ y, (M x).real {y} ≤ exp ε * (M a).real {y}) :
    entryCondMutualInfo P M i ≤ min ε (ε ^ 2) := by
  classical
  rw [entryCondMutualInfo_eq]
  have htot : ∑ x, P.real {x} * min ε (ε ^ 2) = min ε (ε ^ 2) := by simp [← sum_mul]
  rw [← htot]
  refine sum_le_sum fun x _ ↦ ?_
  set A := ∑ a with rest i a = rest i x, P.real {a}
  rcases (measureReal_nonneg : 0 ≤ P.real {x}).eq_or_lt with h0 | hPx
  · simp [← h0]
  have hA : P.real {x} ≤ A :=
    single_le_sum (f := fun a ↦ P.real {a}) (fun _ _ ↦ measureReal_nonneg) (by simp)
  have hApos : 0 < A := hPx.trans_le hA
  have hterm (y : 𝓨) : P.real {x} * (M x).real {y} * log (P.real {x} * (M x).real {y} * A /
      (P.real {x} * ∑ a with rest i a = rest i x, P.real {a} * (M a).real {y})) =
        P.real {x} * ((M x).real {y} * log ((M x).real {y} /
          ((∑ a with rest i a = rest i x, P.real {a} * (M a).real {y}) / A))) := by
    rw [mul_assoc (P.real {x}), mul_assoc (P.real {x}), mul_div_mul_left _ _ hPx.ne',
      div_div_eq_mul_div]
  simp_rw [hterm, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hPx.le
  have hB₁ : ∑ y, (∑ a with rest i a = rest i x, P.real {a} * (M a).real {y}) / A = 1 := by
    rw [← sum_div, div_eq_one_iff_eq hApos.ne', sum_comm]
    simp [A, ← mul_sum]
  refine klDivSum_le_min_of_forall_le_exp_mul (fun y ↦ measureReal_nonneg)
    (fun y ↦ div_nonneg (sum_nonneg fun a _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg)
      hApos.le) (by simp) hB₁ hε (fun y ↦ ?_) (fun y ↦ ?_)
  · rw [mul_div_assoc', le_div_iff₀ hApos, mul_sum, mul_sum]
    refine sum_le_sum fun a ha ↦ ?_
    calc (M x).real {y} * P.real {a} ≤ exp ε * (M a).real {y} * P.real {a} :=
          mul_le_mul_of_nonneg_right (h x a (mem_filter.1 ha).2 y) measureReal_nonneg
      _ = exp ε * (P.real {a} * (M a).real {y}) := by ring
  · rw [div_le_iff₀ hApos, mul_assoc, mul_sum, mul_sum]
    refine sum_le_sum fun a ha ↦ ?_
    calc P.real {a} * (M a).real {y} ≤ P.real {a} * (exp ε * (M x).real {y}) :=
          mul_le_mul_of_nonneg_left (h a x (mem_filter.1 ha).2.symm y) measureReal_nonneg
      _ = exp ε * ((M x).real {y} * P.real {a}) := by ring

/-- **Cuff–Yu, Lemma 1, (23)**, for finite alphabets: an `ε`-DP mechanism (for the Hamming
neighbour relation of Definition 3) is `min {ε, ε²}`-MI-DP, for `ε ≥ 0`. The paper goes through
KL-DP ((21) and (22)); here the average `∑_a π(a) M(x^{-i}, a)` against which `M x` is compared in
`I(X_i; Y | X^{-i})` is itself `(ε, 0)`-close to `M x`, and Property 1
(`klDivSum_le_min_of_forall_le_exp_mul`) applies to it directly. -/
theorem IsEpsDP.isMIDP_min (hε : 0 ≤ ε) (h : IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε) :
    IsMIDP M (min ε (ε ^ 2)) := by
  intro P _ i
  refine entryCondMutualInfo_le_min_of_forall hε i fun x a hxa y ↦ ?_
  by_cases hax : a = x
  · subst hax
    exact le_mul_of_one_le_left measureReal_nonneg (one_le_exp hε)
  exact isEpsDP_iff_forall_singleton.1 h (hammingDist_eq_one_of_rest_eq hxa.symm (Ne.symm hax)) y

/-- **Cuff–Yu, Lemma 1, (23)**, for finite alphabets, with the bound `ε` instead of
`min {ε, ε²}`: an `ε`-DP mechanism (for the Hamming neighbour relation of Definition 3) is
`ε`-MI-DP, for `ε ≥ 0`. -/
theorem IsEpsDP.isMIDP (hε : 0 ≤ ε) (h : IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε) :
    IsMIDP M ε := by
  intro P _ i
  refine entryCondMutualInfo_le_of_forall i fun x a hxa y ↦ ?_
  by_cases hax : a = x
  · subst hax
    exact mul_le_of_le_one_left measureReal_nonneg (exp_le_one_iff.2 (by linarith))
  have hd := hammingDist_eq_one_of_rest_eq hxa.symm (Ne.symm hax)
  calc exp (-ε) * (M x).real {y} ≤ exp (-ε) * (exp ε * (M a).real {y}) :=
        mul_le_mul_of_nonneg_left (isEpsDP_iff_forall_singleton.1 h hd y) (exp_pos _).le
    _ = (M a).real {y} := by rw [← mul_assoc, ← exp_add]; simp

namespace MutualInfoDP

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (𝓧 i)] [∀ i, DecidableEq (𝓧 i)]
  [∀ i, MeasurableSingletonClass (𝓧 i)] in
/-- The equal-weight mixture of two probability measures is a probability measure. -/
lemma isProbabilityMeasure_half_add {α : Type*} [MeasurableSpace α] (μ₁ μ₂ : Measure α)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • (μ₁ + μ₂)) := by
  constructor
  simp only [smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (𝓧 i)] [∀ i, DecidableEq (𝓧 i)]
  [∀ i, MeasurableSingletonClass (𝓧 i)] in
/-- The masses of the equal-weight mixture of two finite measures. -/
lemma half_add_real {α : Type*} [MeasurableSpace α] (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (s : Set α) :
    ((2⁻¹ : ℝ≥0∞) • (μ₁ + μ₂)).real s = (μ₁.real s + μ₂.real s) / 2 := by
  rw [measureReal_def, smul_apply, add_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_inv]
  simp only [measureReal_def, ENNReal.toReal_ofNat]
  ring

/-- The uniform law on two databases `x, x'`. -/
noncomputable def twoPoint (x x' : (i : ι) → 𝓧 i) : Measure ((i : ι) → 𝓧 i) :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac x + Measure.dirac x')

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (𝓧 i)] [∀ i, DecidableEq (𝓧 i)]
  [∀ i, MeasurableSingletonClass (𝓧 i)] in
/-- The uniform law on two databases is a probability measure. -/
instance (x x' : (i : ι) → 𝓧 i) : IsProbabilityMeasure (twoPoint x x') :=
  isProbabilityMeasure_half_add _ _

omit [DecidableEq ι] [∀ i, Fintype (𝓧 i)] in
/-- The point masses of the uniform law on `{x, x'}` (for `x = x'` this is the Dirac mass). -/
lemma twoPoint_real_singleton (x x' a : (i : ι) → 𝓧 i) :
    (twoPoint x x').real {a} = (if a = x then 1 / 2 else 0) + (if a = x' then 1 / 2 else 0) := by
  have h (z : (i : ι) → 𝓧 i) : Measure.dirac z {a} = if a = z then 1 else 0 := by
    rw [Measure.dirac_apply]; by_cases hz : a = z <;> simp [hz, eq_comm]
  rw [measureReal_def, twoPoint, smul_apply, add_apply, h, h, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (by split_ifs <;> simp) (by split_ifs <;> simp)]
  split_ifs <;> norm_num

omit [∀ i, DecidableEq (𝓧 i)] in
/-- Under the uniform law on two databases `x ≠ x'` that differ only in the `i`-th entry,
`I(X_i; Y | X^{-i})` is the Jensen–Shannon divergence
`(D(M x ‖ m) + D(M x' ‖ m)) / 2` of the two output laws, with `m = (M x + M x') / 2`. -/
theorem entryCondMutualInfo_twoPoint {i : ι} {x x' : (i : ι) → 𝓧 i} (hne : x ≠ x')
    (hxx' : rest i x = rest i x') :
    entryCondMutualInfo (twoPoint x x') M i =
      (klDivSum (fun y ↦ (M x).real {y}) (fun y ↦ ((M x).real {y} + (M x').real {y}) / 2) +
        klDivSum (fun y ↦ (M x').real {y}) (fun y ↦ ((M x).real {y} + (M x').real {y}) / 2)) /
        2 := by
  classical
  have hP := twoPoint_real_singleton x x'
  have hmem : ∀ z, rest i z = rest i x → (x ∈ ({a | rest i a = rest i z} : Finset _) ∧
      x' ∈ ({a | rest i a = rest i z} : Finset _)) := fun z hz ↦ by
    simp [hz, hxx']
  have hA (z) (hz : rest i z = rest i x) :
      ∑ a with rest i a = rest i z, (twoPoint x x').real {a} = 1 := by
    simp only [hP, sum_add_distrib, sum_ite_eq', (hmem z hz).1, (hmem z hz).2, ite_true]
    norm_num
  have hB (z) (hz : rest i z = rest i x) (y : 𝓨) :
      ∑ a with rest i a = rest i z, (twoPoint x x').real {a} * (M a).real {y} =
        ((M x).real {y} + (M x').real {y}) / 2 := by
    simp only [hP, add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', (hmem z hz).1,
      (hmem z hz).2, ite_true]
    ring
  rw [entryCondMutualInfo_eq, Fintype.sum_eq_add x x' hne (fun c hc ↦ by simp [hP, hc.1, hc.2]),
    hA x rfl, hA x' hxx'.symm, klDivSum, klDivSum, add_div, sum_div, sum_div]
  simp only [hB x rfl, hB x' hxx'.symm]
  simp only [hP, hne, (Ne.symm hne), ite_true, ite_false]
  congr 1 <;> refine sum_congr rfl fun y _ ↦ ?_ <;>
    simp only [add_zero, zero_add, mul_one] <;>
    rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)] <;> ring

end MutualInfoDP

open MutualInfoDP in
/-- **Cuff–Yu, Lemma 2, (27)**, for finite alphabets: an `ε`-MI-DP mechanism is
`(0, √(2ε))`-DP. Proof: under the uniform prior on two neighbouring databases,
`I(X_i; Y | X^{-i})` is the Jensen–Shannon divergence of their output laws, and Pinsker's
inequality bounds each of its two halves (a variant of the argument of Appendix C). -/
theorem IsMIDP.isEpsDeltaDP (h : IsMIDP M ε) :
    IsEpsDeltaDP M (fun x x' ↦ hammingDist x x' = 1) 0 √(2 * ε) := by
  intro x x' hxx' E
  obtain ⟨i, hi, hrest⟩ := exists_rest_eq_of_hammingDist_eq_one hxx'
  have hne : x ≠ x' := fun h ↦ hi (h ▸ rfl)
  have hI := h (twoPoint x x') i
  rw [entryCondMutualInfo_twoPoint hne hrest] at hI
  set ν : Measure 𝓨 := (2⁻¹ : ℝ≥0∞) • (M x + M x') with hν_def
  have := isProbabilityMeasure_half_add (M x) (M x')
  have hν : (fun y ↦ ((M x).real {y} + (M x').real {y}) / 2) = fun y ↦ ν.real {y} :=
    funext fun y ↦ (half_add_real _ _ _).symm
  have hc : (2⁻¹ : ℝ≥0∞) ≠ 0 := by simp
  have hK₁ := klDiv_eq_ofReal_klDivSum (μ := M x) (ν := ν)
    (((Measure.AbsolutelyContinuous.refl _).add_right _).trans
      (Measure.absolutelyContinuous_smul hc))
  have hK₂ := klDiv_eq_ofReal_klDivSum (μ := M x') (ν := ν)
    (((Measure.AbsolutelyContinuous.refl _).add_right' _).trans
      (Measure.absolutelyContinuous_smul hc))
  have P₁ := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := M x) (ν := ν) (s := E) .of_discrete
  have P₂ := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := M x') (ν := ν) (s := E) .of_discrete
  rw [hK₁, ENNReal.ofReal_le_ofReal_iff', hν_def, half_add_real] at P₁
  rw [hK₂, ENNReal.ofReal_le_ofReal_iff', hν_def, half_add_real] at P₂
  rw [hν] at hI
  rw [exp_zero, one_mul, ← sub_le_iff_le_add']
  set Δ := (M x).real E - (M x').real E
  rcases le_or_gt Δ 0 with hΔ | hΔ
  · exact hΔ.trans (sqrt_nonneg _)
  have hpos : 0 < 2 * (Δ / 2) ^ 2 := by positivity
  have h₁ : (M x).real E - ((M x).real E + (M x').real E) / 2 = Δ / 2 := by ring
  have h₂ : (M x').real E - ((M x).real E + (M x').real E) / 2 = -(Δ / 2) := by ring
  rw [h₁] at P₁
  rw [h₂, neg_sq] at P₂
  rcases P₁ with P₁ | P₁ <;> rcases P₂ with P₂ | P₂ <;> try linarith
  rw [le_sqrt hΔ.le (by linarith)]
  linarith

/-! ### KL differential privacy -/

/-- **KL differential privacy** (Cuff–Yu, Definition 7): `ε ≥ 0` and `D(M x ‖ M x') ≤ ε` nats
for all neighbouring databases `x, x'`. (The condition `ε ≥ 0` excludes the junk value
`ENNReal.ofReal ε = 0` for `ε < 0`.) -/
def IsKLDP (M : Kernel ((i : ι) → 𝓧 i) 𝓨) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ ⦃x x'⦄, hammingDist x x' = 1 → klDiv (M x) (M x') ≤ ENNReal.ofReal ε

omit [DecidableEq ι] [∀ i, Fintype (𝓧 i)] [Fintype 𝓨] [∀ i, MeasurableSingletonClass (𝓧 i)] in
/-- **Cuff–Yu, Lemma 1, (21)**, for finite alphabets: an `ε`-DP mechanism is
`min {ε, ε²}`-KL-DP, for `ε ≥ 0` (by Property 1). -/
theorem IsEpsDP.isKLDP_min [Finite 𝓨] (hε : 0 ≤ ε)
    (h : IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) ε) : IsKLDP M (min ε (ε ^ 2)) := by
  have := Fintype.ofFinite 𝓨
  refine ⟨le_min hε (sq_nonneg ε), fun x x' hxx' ↦ ?_⟩
  have hac : M x ≪ M x' := fun s hs ↦ by
    have := h.measure_le hxx' s
    rw [hs, mul_zero, zero_add, ENNReal.ofReal_zero] at this
    exact nonpos_iff_eq_zero.1 this
  rw [klDiv_eq_ofReal_klDivSum hac]
  refine ENNReal.ofReal_le_ofReal (klDivSum_le_min_of_forall_le_exp_mul (fun _ ↦ measureReal_nonneg)
    (fun _ ↦ measureReal_nonneg) (by simp) (by simp) hε (fun y ↦ ?_) (fun y ↦ ?_))
  · exact isEpsDP_iff_forall_singleton.1 h hxx' y
  · exact isEpsDP_iff_forall_singleton.1 h (by rwa [hammingDist_comm]) y

omit [∀ i, DecidableEq (𝓧 i)] in
/-- A bound on `I(X_i; Y | X^{-i})` by the largest divergence `D(M x ‖ M a)` between output laws
of databases that agree outside the `i`-th entry. -/
theorem MutualInfoDP.entryCondMutualInfo_le_of_klDivSum_le {P : Measure ((i : ι) → 𝓧 i)}
    [IsProbabilityMeasure P] (i : ι)
    (hac : ∀ x a, rest i a = rest i x → ∀ y, (M a).real {y} = 0 → (M x).real {y} = 0)
    (hKL : ∀ x a, rest i a = rest i x →
      klDivSum (fun y ↦ (M x).real {y}) (fun y ↦ (M a).real {y}) ≤ ε) :
    entryCondMutualInfo P M i ≤ ε := by
  classical
  rw [entryCondMutualInfo_eq]
  have htot : ∑ x, P.real {x} * ε = ε := by simp [← sum_mul]
  rw [← htot]
  refine sum_le_sum fun x _ ↦ ?_
  set S : Finset ((i : ι) → 𝓧 i) := {a | rest i a = rest i x}
  set A := ∑ a ∈ S, P.real {a}
  rcases (measureReal_nonneg : 0 ≤ P.real {x}).eq_or_lt with h0 | hPx
  · simp [← h0]
  have hA : P.real {x} ≤ A :=
    single_le_sum (f := fun a ↦ P.real {a}) (fun _ _ ↦ measureReal_nonneg) (by simp [S])
  have hApos : 0 < A := hPx.trans_le hA
  have hterm (y : 𝓨) : P.real {x} * (M x).real {y} * log (P.real {x} * (M x).real {y} * A /
      (P.real {x} * ∑ a ∈ S, P.real {a} * (M a).real {y})) =
        P.real {x} * ((M x).real {y} * log ((M x).real {y} * A /
          ∑ a ∈ S, P.real {a} * (M a).real {y})) := by
    rw [mul_assoc (P.real {x}), mul_assoc (P.real {x}), mul_div_mul_left _ _ hPx.ne']
  simp_rw [hterm, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hPx.le
  have hw₀ : ∀ a ∈ S, 0 ≤ P.real {a} / A := fun a _ ↦ div_nonneg measureReal_nonneg hApos.le
  have hw₁ : ∑ a ∈ S, P.real {a} / A = 1 := by rw [← sum_div, div_self hApos.ne']
  -- Jensen's inequality for `log`, output by output
  have hy (y : 𝓨) : (M x).real {y} * log ((M x).real {y} * A /
      ∑ a ∈ S, P.real {a} * (M a).real {y}) ≤
        ∑ a ∈ S, P.real {a} / A * ((M x).real {y} * log ((M x).real {y} / (M a).real {y})) := by
    rcases (measureReal_nonneg : 0 ≤ (M x).real {y}).eq_or_lt with hW | hW
    · simp [← hW]
    have hpos : ∀ a ∈ S, (M a).real {y} / (M x).real {y} ∈ Set.Ioi (0 : ℝ) := fun a ha ↦ by
      refine div_pos (lt_of_le_of_ne measureReal_nonneg fun h0 ↦ ?_) hW
      exact hW.ne' (hac x a (by simpa [S] using ha) y h0.symm)
    have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum hw₀ hw₁ hpos
    simp only [smul_eq_mul] at hJ
    have hsum : ∑ a ∈ S, P.real {a} / A * ((M a).real {y} / (M x).real {y}) =
        (∑ a ∈ S, P.real {a} * (M a).real {y}) / ((M x).real {y} * A) := by
      rw [sum_div]
      refine sum_congr rfl fun a _ ↦ ?_
      field_simp
    rw [hsum] at hJ
    have hR : ∑ a ∈ S, P.real {a} / A * ((M x).real {y} * log ((M x).real {y} / (M a).real {y})) =
        (M x).real {y} * -∑ a ∈ S, P.real {a} / A * log ((M a).real {y} / (M x).real {y}) := by
      rw [mul_neg, mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [show (M x).real {y} / (M a).real {y} = ((M a).real {y} / (M x).real {y})⁻¹ from
        (inv_div _ _).symm, log_inv]
      ring
    have hL : log ((M x).real {y} * A / ∑ a ∈ S, P.real {a} * (M a).real {y}) =
        -log ((∑ a ∈ S, P.real {a} * (M a).real {y}) / ((M x).real {y} * A)) := by
      rw [← log_inv, inv_div]
    rw [hR, hL]
    exact mul_le_mul_of_nonneg_left (neg_le_neg hJ) hW.le
  calc ∑ y, (M x).real {y} * log ((M x).real {y} * A / ∑ a ∈ S, P.real {a} * (M a).real {y})
      ≤ ∑ y, ∑ a ∈ S, P.real {a} / A * ((M x).real {y} * log ((M x).real {y} / (M a).real {y})) :=
        sum_le_sum fun y _ ↦ hy y
    _ = ∑ a ∈ S, P.real {a} / A *
          klDivSum (fun y ↦ (M x).real {y}) (fun y ↦ (M a).real {y}) := by
        rw [sum_comm]; simp_rw [klDivSum, mul_sum]
    _ ≤ ∑ a ∈ S, P.real {a} / A * ε :=
        sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left (hKL x a (by simpa [S] using ha))
          (hw₀ a ha)
    _ = ε := by rw [← sum_mul, hw₁, one_mul]

/-- **Cuff–Yu, Lemma 1, (22)**, for finite alphabets: an `ε`-KL-DP mechanism is `ε`-MI-DP. -/
theorem IsKLDP.isMIDP (h : IsKLDP M ε) : IsMIDP M ε := by
  obtain ⟨hε, h⟩ := h
  intro P _ i
  have hne {x a : (i : ι) → 𝓧 i} (hxa : rest i a = rest i x) (hax : a ≠ x) :
      klDiv (M x) (M a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h (hammingDist_eq_one_of_rest_eq hxa.symm
      (Ne.symm hax)))
  refine entryCondMutualInfo_le_of_klDivSum_le i (fun x a hxa y hy ↦ ?_) (fun x a hxa ↦ ?_)
  · by_cases hax : a = x
    · rwa [← hax]
    have hac := (klDiv_ne_top_iff.1 (hne hxa hax)).1
    have : M a {y} = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hy
      exact hy.resolve_right (measure_ne_top _ _)
    simp [measureReal_def, hac this]
  · by_cases hax : a = x
    · subst hax
      have h0 : klDivSum (fun y ↦ (M a).real {y}) (fun y ↦ (M a).real {y}) = 0 :=
        sum_eq_zero fun y _ ↦ by rcases eq_or_ne ((M a).real {y}) 0 with h | h <;> simp [h]
      rw [h0]
      exact hε
    have hac := (klDiv_ne_top_iff.1 (hne hxa hax)).1
    have := h (hammingDist_eq_one_of_rest_eq hxa.symm (Ne.symm hax))
    rwa [klDiv_eq_ofReal_klDivSum hac, ENNReal.ofReal_le_ofReal_iff hε] at this

omit [IsMarkovKernel M] in
/-- **Cuff–Yu, Theorem 1, (17)**, for finite alphabets, in the sense of their Definition 8:
`ε-DP ⪰ MI-DP ⪰ (ε, δ)-DP`. The witnesses are explicit and depend on neither the mechanism nor
the alphabets: for `β > 0`, `β`-DP implies `β`-MI-DP (`α = β`), and for `ε' ≥ 0` and `δ > 0`,
`(δ² / 2)`-MI-DP implies `(ε', δ)`-DP (`α = δ² / 2`). -/
theorem isEpsDP_succeeds_isMIDP_succeeds_isEpsDeltaDP :
    (∀ β > 0, ∀ (M : Kernel ((i : ι) → 𝓧 i) 𝓨) [IsMarkovKernel M],
      IsEpsDP M (fun x x' ↦ hammingDist x x' = 1) β → IsMIDP M β) ∧
    (∀ ε' ≥ 0, ∀ δ > 0, ∀ (M : Kernel ((i : ι) → 𝓧 i) 𝓨) [IsMarkovKernel M],
      IsMIDP M (δ ^ 2 / 2) → IsEpsDeltaDP M (fun x x' ↦ hammingDist x x' = 1) ε' δ) := by
  refine ⟨fun β hβ M _ h ↦ h.isMIDP hβ.le, fun ε' hε' δ hδ M _ h ↦ ?_⟩
  have h₂ : √(2 * (δ ^ 2 / 2)) = δ := by
    rw [show 2 * (δ ^ 2 / 2) = δ ^ 2 by ring, sqrt_sq hδ.le]
  exact h₂ ▸ h.isEpsDeltaDP.mono hε' le_rfl

end InformationTheory
