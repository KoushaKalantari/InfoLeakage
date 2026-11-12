/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.PerfectSecrecy.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Probability.UniformOn

/-!
# Perfect secrecy: key count, Latin squares and the Vernam system

This file formalizes the combinatorial consequences of Theorem 6 drawn in §10 of C. E. Shannon,
*Communication Theory of Secrecy Systems*, Bell System Technical Journal 28(4), 656–715, 1949
(not on arXiv): perfect secrecy needs at least as many keys as messages, this many keys suffice,
when messages, keys and cryptograms are equally many the perfect systems are exactly the
"Latin squares" with equally likely keys, and the finite-block form of `R_M L_M ≤ R_K L_K`.

As in the paper, the enciphering transformations `T k : M → E` are assumed uniquely reversible
(injective) where this is needed.

## Main statements

* `encard_le_encard_of_isPerfectlySecret`: for a fixed a priori law, perfect secrecy needs at
  least as many keys of positive probability as messages of positive probability.
* `card_le_ncard_of_isPerfectSystem`, `card_le_card_of_isPerfectSystem`: a perfect system has at
  least as many keys of positive probability, hence at least as many keys, as messages.
* `pow_card_le_pow_card_of_isPerfectSystem`, `mul_log_card_le_mul_log_card_of_isPerfectSystem`:
  for messages and keys that are blocks of letters, `R_M L_M ≤ R_K L_K`.
* `isPerfectSystem_of_existsUnique`: if each message is enciphered into each cryptogram by
  exactly one key and all keys are equally likely, the system is perfect.
* `isPerfectSystem_iff_existsUnique_and_eq_inv`: Shannon's characterization of perfect systems
  with equally many messages, keys and cryptograms by these two properties.
* `isPerfectSystem_add`: adding a uniform key in a finite group is perfect. Special cases:
  `isPerfectSystem_zmod` (Shannon's example `Tᵢ Mⱼ = E_{i + j mod n}` with `n` keys) and
  `isPerfectSystem_vernam` (the Vernam system `eᵢ = mᵢ + kᵢ mod a` on blocks of `N` letters).
* `cipherKernel_zmod_apply`, `comp_cipherKernel_zmod_apply`: in Shannon's example
  `P_M(E) = 1 / n = P(E)`.
* `exists_cond_ne_inv_zmod`: in Shannon's example the a posteriori probability `P_E(M)` is not
  `1 / n` in general (see the notes below).
* `exists_isPerfectSystem_comp_apply_eq_zero`: a step of the key-count argument implicitly assumes
  a key of positive probability (see the notes below).

## Mapping from the paper

* §10, "there must be as many `E`'s as there are `M`'s" → `card_le_card_cryptogram`.
* §10, "the number of different keys is at least as great as the number of `M`'s" →
  `card_le_card_of_isPerfectSystem` (and the refinements above).
* §10, example `Tᵢ Mⱼ = E_s`, `s = i + j (mod n)` → `isPerfectSystem_zmod`,
  `cipherKernel_zmod_apply`, `comp_cipherKernel_zmod_apply`.
* §10, Latin-square characterization → `isPerfectSystem_iff_existsUnique_and_eq_inv`.
* §10, `R_M L_M ≤ R_K L_K` "from the finite case" →
  `mul_log_card_le_mul_log_card_of_isPerfectSystem` (finite blocks only).
* §4.3 and §10, the Vernam system → `isPerfectSystem_vernam` (finite-block special case, with
  message, key and cryptogram over the same alphabet).

## Not formalized

* The remark that, in perfect systems with `n` keys, the key uncertainty `H(K)` must be at least
  `log n` to conceal the message information (an informal remark, not a stated result).
* `R_M L_M ≤ R_K L_K` for messages and keys generated as infinite sequences (only the finite-block
  form above is formalized), and the Vernam system with an unlimited key.
* The remark that, for a message source of rate `R`, the key needed per letter can be reduced by
  the factor `R / R_M` by first removing redundancy, and that this is optimal.
* Footnote 9 (the "blank" message).

## Notes on the paper

For the example `Tᵢ Mⱼ = E_{i + j mod n}` the paper states "`P_E(M) = 1/n = P(E)`" (p. 681 of
the journal version). What holds is `P_M(E) = 1/n = P(E)` (`cipherKernel_zmod_apply`,
`comp_cipherKernel_zmod_apply`), whence `P_E(M) = P(M)`, which is `1/n` only when
`P(M) = 1/n`; `exists_cond_ne_inv_zmod` shows that `P_E(M) ≠ 1/n` for `n ≥ 2` and an a priori law
concentrated on one message. The conclusion
"we have perfect secrecy" is correct (`isPerfectSystem_zmod`).

The key-count argument in the paper fixes a key `i` and uses `P(E) ≠ 0` for the cryptograms
`E = Tᵢ M`, with the implicit hypothesis that `i` has positive probability (Shannon may intend
the "possible" keys to have `pᵢ > 0`). `exists_isPerfectSystem_comp_apply_eq_zero` gives a perfect
system and a key `i` with `pᵢ = 0` and `P(Tᵢ M) = 0` for all `M`. The conclusion is unaffected,
since some key has positive probability; the proofs below choose such a key.

## Implementation notes

Cardinalities are `Nat.card`, `Set.ncard` and `Set.encard`, which need no `Fintype` instances.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {M K E : Type*} [MeasurableSpace M] [MeasurableSpace K] [MeasurableSpace E]
  [Countable M] [MeasurableSingletonClass M] [Countable K] [MeasurableSingletonClass K]
  [MeasurableSingletonClass E] {T : K → M → E} {μ : Measure M} {ν : Measure K}

section KeyCount

omit [MeasurableSpace M] [MeasurableSpace E] [Countable M] [MeasurableSingletonClass M]
  [MeasurableSingletonClass E] [MeasurableSingletonClass K] in
/-- A set of positive measure in a countable space contains an atom. -/
lemma exists_mem_measure_singleton_ne_zero {s : Set K} (hs : ν s ≠ 0) :
    ∃ k ∈ s, ν {k} ≠ 0 := by
  by_contra! h
  exact hs ((measure_null_iff_singleton s.to_countable).2 h)

omit [MeasurableSpace M] [MeasurableSpace K] [MeasurableSpace E] [Countable M]
  [MeasurableSingletonClass M] [Countable K] [MeasurableSingletonClass K]
  [MeasurableSingletonClass E] in
/-- There are at least as many cryptograms as messages (Shannon 1949, §10), since each
transformation `T k` is one-to-one. -/
lemma card_le_card_cryptogram [Finite E] [Nonempty K] (hT : ∀ k, Function.Injective (T k)) :
    Nat.card M ≤ Nat.card E :=
  Nat.card_le_card_of_injective _ (hT (Classical.arbitrary K))

/-- **Key-count bound** (Shannon 1949, §10) for a fixed a priori law `μ`: if the system is
perfectly secret for `μ`, there are at least as many keys of positive probability as messages of
positive a priori probability. Cardinalities are in `ℕ∞`, so this also covers infinite sets. -/
theorem encard_le_encard_of_isPerfectlySecret (hT : ∀ k, Function.Injective (T k))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : IsPerfectlySecret μ T ν) :
    {m | μ {m} ≠ 0}.encard ≤ {k | ν {k} ≠ 0}.encard := by
  obtain ⟨k₀, hk₀⟩ := ν.exists_measure_singleton_ne_zero
  obtain ⟨m₀, hm₀⟩ := μ.exists_measure_singleton_ne_zero
  have h_six := isPerfectlySecret_iff.1 h m₀ hm₀
  -- Every message `m` of positive probability is enciphered by `k₀` into a cryptogram of positive
  -- probability, which some key of positive probability must therefore produce from `m₀`.
  have h_key (m : M) (hm : μ {m} ≠ 0) : ∃ k, ν {k} ≠ 0 ∧ T k m₀ = T k₀ m := by
    have hκ : cipherKernel T ν m {T k₀ m} ≠ 0 := by
      rw [cipherKernel_apply_singleton]
      exact ((pos_iff_ne_zero.2 hk₀).trans_le
        (measure_mono (Set.singleton_subset_iff.2 rfl))).ne'
    have hP := Measure.comp_apply_ne_zero (measurableSet_singleton _) hm hκ
    rw [← h_six, cipherKernel_apply_singleton] at hP
    obtain ⟨k, hk, hkν⟩ := exists_mem_measure_singleton_ne_zero hP
    exact ⟨k, hkν, hk⟩
  have : Nonempty K := ⟨k₀⟩
  choose! f hf using h_key
  -- Keys sending `m₀` to the distinct cryptograms `T k₀ m` are distinct.
  refine Set.encard_le_encard_of_injOn (fun m hm ↦ (hf m hm).1) fun m hm m' hm' hmm' ↦ hT k₀ ?_
  rw [← (hf m hm).2, ← (hf m' hm').2, hmm']

/-- **Key-count bound** (Shannon 1949, §10): a perfect system has at least as many keys of
positive probability as messages. -/
theorem card_le_ncard_of_isPerfectSystem [Finite M] [Finite K]
    (hT : ∀ k, Function.Injective (T k)) [IsProbabilityMeasure ν] (h : IsPerfectSystem T ν) :
    Nat.card M ≤ {k | ν {k} ≠ 0}.ncard := by
  cases isEmpty_or_nonempty M
  · simp
  have := Fintype.ofFinite M
  -- Apply the bound for a fixed a priori law to the uniform law, which charges every message.
  have h_ne (m : M) : uniformOn (Set.univ : Set M) {m} ≠ 0 := by simp [uniformOn_univ]
  have h_supp : {m | uniformOn (Set.univ : Set M) {m} ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall h_ne
  have h_enc := encard_le_encard_of_isPerfectlySecret hT (h (uniformOn Set.univ))
  rw [h_supp] at h_enc
  rw [← Set.ncard_univ, Set.ncard_def, Set.ncard_def]
  exact ENat.toNat_le_toNat h_enc (Set.encard_ne_top_iff.2 (Set.toFinite _))

/-- **Key-count bound** (Shannon 1949, §10): "the number of different keys is at least as great as
the number of `M`'s" in a perfect system. -/
theorem card_le_card_of_isPerfectSystem [Finite M] [Finite K]
    (hT : ∀ k, Function.Injective (T k)) [IsProbabilityMeasure ν] (h : IsPerfectSystem T ν) :
    Nat.card M ≤ Nat.card K :=
  (card_le_ncard_of_isPerfectSystem hT h).trans (Set.ncard_le_card _)

omit [Countable M] [MeasurableSingletonClass M] [Countable K] [MeasurableSingletonClass K] in
/-- Finite-block form of Shannon's bound `R_M L_M ≤ R_K L_K` (§10), multiplicative form: if the
messages are blocks of `L_M` letters from an alphabet `A`, the keys are blocks of `L_K` letters
from an alphabet `B`, and the system is perfect, then `|A| ^ L_M ≤ |B| ^ L_K`. -/
theorem pow_card_le_pow_card_of_isPerfectSystem {A B : Type*} [Finite A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Finite B] [MeasurableSpace B] [MeasurableSingletonClass B]
    {L_M L_K : ℕ} {T : (Fin L_K → B) → (Fin L_M → A) → E} (hT : ∀ k, Function.Injective (T k))
    {ν : Measure (Fin L_K → B)} [IsProbabilityMeasure ν] (h : IsPerfectSystem T ν) :
    Nat.card A ^ L_M ≤ Nat.card B ^ L_K := by
  simpa [Nat.card_fun] using card_le_card_of_isPerfectSystem hT h

omit [Countable M] [MeasurableSingletonClass M] [Countable K] [MeasurableSingletonClass K] in
/-- **Shannon's bound `R_M L_M ≤ R_K L_K`** (§10), in its finite-block form: if the messages are
blocks of `L_M` letters from an alphabet `A` with `R_M = log |A|`, the keys are blocks of `L_K`
letters from an alphabet `B` with `R_K = log |B|`, and the system is perfect, then
`R_M L_M ≤ R_K L_K` (natural logarithms; the inequality does not depend on the base). -/
theorem mul_log_card_le_mul_log_card_of_isPerfectSystem {A B : Type*} [Finite A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Finite B] [MeasurableSpace B]
    [MeasurableSingletonClass B] {L_M L_K : ℕ} {T : (Fin L_K → B) → (Fin L_M → A) → E}
    (hT : ∀ k, Function.Injective (T k)) {ν : Measure (Fin L_K → B)} [IsProbabilityMeasure ν]
    (h : IsPerfectSystem T ν) :
    L_M * Real.log (Nat.card A) ≤ L_K * Real.log (Nat.card B) := by
  rw [← Real.log_pow, ← Real.log_pow]
  exact Real.log_le_log (pow_pos (Nat.cast_pos.2 Nat.card_pos) _)
    (by exact_mod_cast pow_card_le_pow_card_of_isPerfectSystem hT h)

end KeyCount

section LatinSquare

/-- Sufficiency in Shannon's Latin-square characterization (§10): if each message is enciphered
into each cryptogram by exactly one key and all keys are equally likely, the system is perfect.
No cardinality or injectivity assumption is needed. -/
theorem isPerfectSystem_of_existsUnique [Countable E] [IsProbabilityMeasure ν] {c : ℝ≥0∞}
    (hT : ∀ m e, ∃! k, T k m = e) (hν : ∀ k, ν {k} = c) :
    IsPerfectSystem T ν := by
  rw [isPerfectSystem_iff_forall_measure_setOf_eq]
  intro m m' e
  obtain ⟨k, hk, hk_unique⟩ := hT m e
  obtain ⟨k', hk', hk'_unique⟩ := hT m' e
  rw [(Set.eq_singleton_iff_unique_mem (s := {k | T k m = e})).2 ⟨hk, hk_unique⟩,
    (Set.eq_singleton_iff_unique_mem (s := {k | T k m' = e})).2 ⟨hk', hk'_unique⟩, hν, hν]

/-- **Latin squares** (Shannon 1949, §10): "Perfect systems in which the number of cryptograms,
the number of messages, and the number of keys are all equal are characterized by the properties
that (1) each `M` is connected to each `E` by exactly one line, (2) all keys are equally likely."
Here the enciphering transformations are one-to-one, as in the paper. -/
theorem isPerfectSystem_iff_existsUnique_and_eq_inv [Finite M] [Finite K] [Finite E]
    (hT : ∀ k, Function.Injective (T k)) [IsProbabilityMeasure ν]
    (hMK : Nat.card M = Nat.card K) (hKE : Nat.card K = Nat.card E) :
    IsPerfectSystem T ν ↔ (∀ m e, ∃! k, T k m = e) ∧ ∀ k, ν {k} = (Nat.card K : ℝ≥0∞)⁻¹ := by
  refine ⟨fun h ↦ ?_, fun h ↦ isPerfectSystem_of_existsUnique h.1 h.2⟩
  have h_row := isPerfectSystem_iff_forall_measure_setOf_eq.1 h
  obtain ⟨k₀, -⟩ := ν.exists_measure_singleton_ne_zero
  have : Nonempty K := ⟨k₀⟩
  -- By the key-count bound, every key has positive probability.
  have h_pos (k : K) : ν {k} ≠ 0 := by
    have h_univ : {k | ν {k} ≠ 0} = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ, ← hMK]; exact card_le_ncard_of_isPerfectSystem hT h)
    exact (Set.ext_iff.1 h_univ k).2 (Set.mem_univ k)
  -- Each transformation is a bijection between messages and cryptograms.
  have h_bij (k : K) : Function.Bijective (T k) :=
    (hT k).bijective_of_nat_card_le (hMK.trans hKE).ge
  -- Some key takes any message to any cryptogram.
  have h_ex (m : M) (e : E) : ∃ k, T k m = e := by
    obtain ⟨m', hm'⟩ := (h_bij k₀).2 e
    have h_ne : ν {k | T k m' = e} ≠ 0 :=
      ((pos_iff_ne_zero.2 (h_pos k₀)).trans_le
        (measure_mono (Set.singleton_subset_iff.2 hm'))).ne'
    rw [h_row m' m e] at h_ne
    exact nonempty_of_measure_ne_zero h_ne
  -- Hence `k ↦ T k m` is onto, so one-to-one as well: (1).
  have h_unique (m : M) (e : E) : ∃! k, T k m = e := by
    obtain ⟨k, hk⟩ := h_ex m e
    have h_inj := (Function.Surjective.bijective_of_nat_card_le (f := fun k ↦ T k m)
      (fun e ↦ h_ex m e) hKE.le).1
    exact ⟨k, hk, fun k' hk' ↦ h_inj (hk'.trans hk.symm)⟩
  refine ⟨h_unique, ?_⟩
  -- (2): for a fixed cryptogram `e₀`, the key `k` is the only key taking `T k⁻¹ e₀` to `e₀`.
  obtain ⟨m₀⟩ : Nonempty M := (Nat.card_pos_iff.1 (hMK ▸ Nat.card_pos)).1
  set e₀ := T k₀ m₀
  have h_const (k : K) : ν {k} = ν {k' | T k' m₀ = e₀} := by
    obtain ⟨m, hm⟩ := (h_bij k).2 e₀
    obtain ⟨_, -, hk_unique⟩ := h_unique m e₀
    rw [← h_row m m₀ e₀, (Set.eq_singleton_iff_unique_mem (s := {k' | T k' m = e₀})).2
      ⟨hm, fun k' hk' ↦ (hk_unique k' hk').trans (hk_unique k hm).symm⟩]
  have := Fintype.ofFinite K
  have h_sum : (Nat.card K : ℝ≥0∞) * ν {k' | T k' m₀ = e₀} = 1 := by
    rw [← measure_univ (μ := ν), ← Finset.coe_univ, ← sum_measure_singleton,
      Finset.sum_congr rfl fun k _ ↦ h_const k, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  intro k
  rw [h_const k]
  exact ENNReal.eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans h_sum)

end LatinSquare

section Examples

omit [MeasurableSpace M] [MeasurableSpace K] [MeasurableSpace E] [Countable M]
  [MeasurableSingletonClass M] [Countable K] [MeasurableSingletonClass K]
  [MeasurableSingletonClass E] in
/-- The uniform law on a finite type gives each point probability `1 / |α|`. -/
lemma uniformOn_univ_singleton {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) :
    uniformOn (Set.univ : Set α) {a} = (Nat.card α : ℝ≥0∞)⁻¹ := by
  have := Fintype.ofFinite α
  simp [uniformOn_univ, Nat.card_eq_fintype_card]

variable {G : Type*} [AddGroup G] [Finite G] [MeasurableSpace G] [MeasurableSingletonClass G]

/-- Enciphering by adding a uniformly distributed key in a finite group, `T k m = k + m`, is a
perfect system: each message is taken to each cryptogram by exactly one key, `e - m`. -/
theorem isPerfectSystem_add : IsPerfectSystem (fun k m : G ↦ k + m) (uniformOn Set.univ) :=
  isPerfectSystem_of_existsUnique
    (fun m e ↦ ⟨e - m, sub_add_cancel e m, fun _ hk ↦ eq_sub_of_add_eq hk⟩)
    uniformOn_univ_singleton

/-- **The Vernam system** (Shannon 1949, §4.3 and §10) is perfect, in its finite-block,
same-alphabet form: messages, keys and cryptograms are blocks of `N` letters from an alphabet of
size `a`, enciphered by `eᵢ = mᵢ + kᵢ (mod a)`, with the key uniform on the `a ^ N` key blocks.
(Shannon's Vernam system uses an unlimited, never-repeating key; that is not formalized.) -/
theorem isPerfectSystem_vernam (N a : ℕ) [NeZero a] :
    IsPerfectSystem (fun k m : Fin N → ZMod a ↦ k + m) (uniformOn Set.univ) :=
  isPerfectSystem_add

variable (n : ℕ) [NeZero n]

/-- **Shannon's perfect system with `n` keys** (§10): messages, keys and cryptograms numbered
modulo `n`, `Tᵢ Mⱼ = E_s` with `s = i + j (mod n)` and equally likely keys. Together with
`card_le_card_of_isPerfectSystem`, it shows that `n` keys are necessary and sufficient. -/
theorem isPerfectSystem_zmod :
    IsPerfectSystem (fun i j : ZMod n ↦ i + j) (uniformOn Set.univ) :=
  isPerfectSystem_add

/-- In Shannon's example `Tᵢ Mⱼ = E_{i + j mod n}`, `P_M(E) = 1 / n`. -/
theorem cipherKernel_zmod_apply (m e : ZMod n) :
    cipherKernel (fun i j : ZMod n ↦ i + j) (uniformOn Set.univ) m {e} = (n : ℝ≥0∞)⁻¹ := by
  rw [cipherKernel_apply_singleton,
    (Set.eq_singleton_iff_unique_mem (s := {k : ZMod n | k + m = e})).2
      ⟨sub_add_cancel e m, fun _ hk ↦ eq_sub_of_add_eq hk⟩,
    uniformOn_univ_singleton, Nat.card_zmod]

/-- In Shannon's example `Tᵢ Mⱼ = E_{i + j mod n}`, `P(E) = 1 / n` for every a priori law. -/
theorem comp_cipherKernel_zmod_apply (μ : Measure (ZMod n)) [IsProbabilityMeasure μ]
    (e : ZMod n) :
    (cipherKernel (fun i j : ZMod n ↦ i + j) (uniformOn Set.univ) ∘ₘ μ) {e} = (n : ℝ≥0∞)⁻¹ := by
  rw [← isPerfectSystem_iff_forall_cipherKernel_eq_comp.1 (isPerfectSystem_zmod n) μ ‹_› 0 e,
    cipherKernel_zmod_apply]

/-- In Shannon's example `Tᵢ Mⱼ = E_{i + j mod n}` the a posteriori probabilities are not `1 / n`
in general, contrary to the formula "`P_E(M) = 1/n = P(E)`" printed in §10 (which holds for
`P_M(E)`, see `cipherKernel_zmod_apply`): for `n ≥ 2` there is an a priori law charging every
message (half the mass on the message `0`, the other half spread uniformly) for which the
cryptogram `0` has positive probability and `P_E(M) = 1/2 + 1/(2n) ≠ 1 / n` at `M = 0`. -/
theorem exists_cond_ne_inv_zmod (hn : 2 ≤ n) :
    ∃ (μ : Measure (ZMod n)) (_ : IsProbabilityMeasure μ), (∀ m, μ {m} ≠ 0) ∧ ∃ m e : ZMod n,
      (cipherKernel (fun i j : ZMod n ↦ i + j) (uniformOn Set.univ) ∘ₘ μ) {e} ≠ 0 ∧
      ProbabilityTheory.cond (μ ⊗ₘ cipherKernel (fun i j : ZMod n ↦ i + j) (uniformOn Set.univ))
        (Prod.snd ⁻¹' {e}) (Prod.fst ⁻¹' {m}) ≠ (n : ℝ≥0∞)⁻¹ := by
  set μ : Measure (ZMod n) := (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • uniformOn Set.univ
  have : IsProbabilityMeasure μ := ⟨by simp [μ, ENNReal.inv_two_add_inv_two]⟩
  have hμ (m : ZMod n) : μ {m} = 2⁻¹ * Measure.dirac 0 {m} + 2⁻¹ * (n : ℝ≥0∞)⁻¹ := by
    simp [μ, uniformOn_univ_singleton]
  have h_half_ne_top : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 two_ne_zero
  have h_pos : (2 : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  have hP : (cipherKernel (fun i j : ZMod n ↦ i + j) (uniformOn Set.univ) ∘ₘ μ) {0} ≠ 0 := by
    simp [comp_cipherKernel_zmod_apply]
  refine ⟨μ, this, fun m ↦ ?_, 0, 0, hP, ?_⟩
  · rw [hμ]
    exact fun h ↦ h_pos (add_eq_zero.1 h).2
  rw [isPerfectSystem_zmod n μ 0 hP 0, hμ, Measure.dirac_apply_of_mem (Set.mem_singleton 0),
    mul_one]
  -- `1 / n ≤ 1 / 2 < 1 / 2 + 1 / (2 n)`.
  refine (lt_of_le_of_lt ?_ (ENNReal.lt_add_right h_half_ne_top h_pos)).ne'
  exact ENNReal.inv_le_inv.2 (by exact_mod_cast hn)

/-- The key-count argument of §10 fixes a key `i` and asserts `P(E) ≠ 0` for the cryptograms
`E = Tᵢ M`; this implicitly assumes that `i` has positive probability. Here is a perfect system
with one-to-one transformations (two messages, four keys, four cryptograms:
`T (k, b) m = (k + m, b)`, with `k` uniform and `b = false` almost surely) and a key `i` of
probability zero such that `P(Tᵢ M) = 0` for every message `M` and every a priori law. -/
theorem exists_isPerfectSystem_comp_apply_eq_zero :
    ∃ (T : ZMod 2 × Bool → ZMod 2 → ZMod 2 × Bool) (ν : Measure (ZMod 2 × Bool))
      (_ : IsProbabilityMeasure ν) (i : ZMod 2 × Bool),
      ν {i} = 0 ∧ (∀ k, Function.Injective (T k)) ∧ IsPerfectSystem T ν ∧
      ∀ μ : Measure (ZMod 2), IsProbabilityMeasure μ → ∀ m,
        (cipherKernel T ν ∘ₘ μ) {T i m} = 0 := by
  set T : ZMod 2 × Bool → ZMod 2 → ZMod 2 × Bool := fun k m ↦ (k.1 + m, k.2)
  set ν : Measure (ZMod 2 × Bool) := (uniformOn Set.univ).prod (Measure.dirac false)
  have h_ker (m x : ZMod 2) (b : Bool) :
      cipherKernel T ν m {(x, b)} = 2⁻¹ * Measure.dirac false {b} := by
    have h_set : {k | T k m = (x, b)} = {x - m} ×ˢ {b} := by
      ext ⟨k, c⟩
      simp [T, eq_sub_iff_add_eq]
    rw [cipherKernel_apply_singleton, h_set, Measure.prod_prod, uniformOn_univ_singleton,
      Nat.card_zmod, Nat.cast_ofNat]
  refine ⟨T, ν, inferInstance, (0, true), ?_, fun k m m' h ↦ ?_, ?_, fun μ _ m ↦ ?_⟩
  · rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    simp
  · simpa [T] using congrArg Prod.fst h
  · exact isPerfectSystem_iff.2 fun m m' ↦ Measure.ext_of_singleton fun ⟨x, b⟩ ↦ by
      rw [h_ker, h_ker]
  · rw [comp_apply_singleton_eq_lintegral, lintegral_congr fun m' ↦ h_ker m' _ _]
    simp

end Examples

end InformationTheory
