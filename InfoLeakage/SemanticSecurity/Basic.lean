/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.LocalPrivacy.Basic
public import InfoLeakage.MaximalLeakage.Operational
public import InfoLeakage.QIF.GainFunctions
public import InfoLeakage.QIF.MinEntropy

/-!
# Semantic security for the wiretap channel

Bellare, Tessaro and Vardy (*A cryptographic treatment of the wiretap channel*, arXiv:1201.2205,
full version of *Semantic security for the wiretap channel*, CRYPTO 2012) compare three security
metrics for an encryption function `E` followed by an adversary channel `ChA`. All three depend only
on the composed channel `κ = ChA ∘ E` from messages `M` to adversary ciphertexts `C`, which we take
to be a Markov kernel `κ : Kernel α β` between finite alphabets:

* mutual-information security, `Adv^mis = max_M I(M; C)` (eq. (2));
* distinguishing security, `Adv^ds = max_{m₀, m₁} SD(κ m₀; κ m₁)` (eqs. (5)–(6));
* semantic security, `Adv^ss = max_{f, M} (max_A P[A(C) = f(M)] - max_S P[S = f(M)])` (eq. (3)).

They show `Adv^ss ≤ Adv^ds ≤ 2 Adv^ss` (Theorem 4.1), `Adv^ds ≤ √(2 Adv^mis)` (Theorem 4.5) and
`Adv^mis ≤ 2 ε log (N / ε)` with `ε = Adv^ds` (Theorem 4.9), so that, asymptotically, MIS-security
and semantic security are equivalent *when* `ε_k log N_k → 0` (e.g. polynomial lengths and
exponentially small `ε_k`): MIS ⇒ SS holds unconditionally, but SS (or DS) ⇒ MIS needs this rate
condition and can fail without it (see "Which implications form the equivalence" below).

## Scope

We formalize Sections 3–4.4 of the paper: the metrics `Adv^mis`, `Adv^ss`, `Adv^ds` (eqs. (2),
(3), (5), (6)) and the relations of Sections 4.1–4.4, with the asymptotic corollaries for plain
XS-security (`Adv^xs → 0`). Not formalized: strong XS-security (Section 3.2) and the
"(respectively, strongly)" parts of the corollaries; the random-message metric `Adv^mis-r`
(eq. (1)); the guessing-probability form (4) of `Adv^ss`; Proposition 4.10 (tightness of
Lemma 4.6); and everything from Section 4.5 on (MIS-R versus MIS, Theorem 4.12, the schemes).

## Main definitions

* `dsAdvantage κ`: `Adv^ds`, as the largest statistical distance between two rows of `κ`
  (eq. (6)). The statistical distance is the library's `tvDistSum p q = (1/2) ∑ |p - q|`, the
  paper's `SD`.
* `dsGameSuccess κ m₀ m₁ A`: the success probability in the distinguishing game of eq. (5).
* `ssAdvantage κ`: `Adv^ss` (eq. (3)), over all message distributions, all randomized functions
  `f` of the message with values in a finite set `Fin n`, and all randomized adversaries, built on
  `guessProb` and `blindGuessProb`.
* `Adv^mis` is the Shannon capacity `shannonCapacity κ = sup_μ I(M; C)` (eq. (2)), with Statlib's
  `mutualInfo`, in nats.

## Main statements

* `ssAdvantage_le_dsAdvantage`, `dsAdvantage_le_two_mul_ssAdvantage`: Theorem 4.1.
* `isGreatest_dsGameAdvantage`, `dsAdvantage_eq_iSup_sSup_dsGame`: eq. (5) = eq. (6).
* `SemanticSecurity.two_mul_sq_tvDistSum_le`,
  `SemanticSecurity.ofReal_two_mul_sq_tvDistSum_le_klDiv`: Pinsker's inequality
  `D(P ‖ Q) ≥ 2 SD(P; Q)²` on a finite alphabet (Lemma 4.3).
* `SemanticSecurity.tvDistSum_joint_twoPoint`: Lemma 4.4.
* `dsAdvantage_le_sqrt_two_mul_shannonCapacity`: Theorem 4.5.
* `SemanticSecurity.sum_negMulLog_sub_le`: Lemma 4.6, `H(P) - H(Q) ≤ 2 ε log (N / ε)`.
* `SemanticSecurity.abs_negMulLog_add_sub_le`: Lemma 4.7.
* `SemanticSecurity.tvDistSum_outputLaw_le`, `SemanticSecurity.tvDistSum_outputLaw_le_of_forall`:
  Lemma 4.8.
* `shannonCapacity_le_dsAdvantage`, `toReal_shannonCapacity_le_dsAdvantage`: Theorem 4.9.
* Asymptotic corollaries for families of channels (Section 4), with "XS-secure" meaning
  `Adv^xs → 0` (Section 3.2): `tendsto_ssAdvantage_iff_tendsto_dsAdvantage` (SS ⇔ DS),
  `tendsto_dsAdvantage_of_tendsto_shannonCapacity` (MIS ⇒ DS),
  `tendsto_ssAdvantage_of_tendsto_shannonCapacity` (MIS ⇒ SS),
  `tendsto_shannonCapacity_of_tendsto_mul_log` (DS at rate `o(1 / log |C_k|)` ⇒ MIS), and
  `tendsto_shannonCapacity_of_le_exp` (the paper's "usual" case: `log |C_k| ≤ C k^a` and
  `Adv^ds_k ≤ exp (-d k^e)` ⇒ MIS).

## Which implications form the "equivalence"

The paper calls SS and DS equivalent (Theorem 4.1, unconditionally and up to a factor `2`), and
calls MIS and SS equivalent (abstract, Section 1 and Figure 2) by combining Theorem 4.1 with
MIS → DS (Theorem 4.5, unconditional) and DS → MIS (Theorem 4.9). The last implication holds, as
the paper says after Theorem 4.9, only "usually": it needs `2 ε_k log (N_k / ε_k) → 0`, which
holds when the lengths are polynomial and `ε_k` is exponentially small, but can fail for a
DS-secure family (e.g. if `ε_k = 1/k` and `N_k = 2^k`, then `ε_k log N_k = log 2`).
Accordingly we do not state an unconditional "MIS ⇔ SS": we prove SS ⇔ DS and MIS ⇒ DS ⇒ SS
unconditionally, and DS ⇒ MIS when `ε_k log N_k → 0` (a hypothesis which by itself forces
`ε_k → 0`, see `tendsto_dsAdvantage_of_tendsto_mul_log`), in particular in the paper's "usual"
case.

## Implementation notes

* Logarithms are natural (nats); the paper uses `lg`. Lemma 4.6, Lemma 4.7 and Theorem 4.9 scale by
  `ln 2` on both sides, so their nat forms are equivalent to the paper's; Theorem 4.5 in nats,
  `Adv^ds ≤ √(2 I_nats)`, is stronger than the bit form since `I_nats ≤ I_bits`.
* `Adv^ds` is defined by the statistical-distance formula (6); the paper defines it by the game (5)
  and states (5) = (6), which is `isGreatest_dsGameAdvantage`. In `ssAdvantage` the simulator term
  is `blindGuessProb`, the largest `P[f(M) = u]`; `blindGuessProb_eq_iSup_simulator` shows it is
  the best success probability of a simulator `S`, as in eq. (3).
* `ssAdvantage` lets `f` range over randomized functions into finite sets `Fin n`. The paper's
  transforms `f` have arbitrary (countable) ranges, but no generality is lost: given `η > 0`, merge
  all values of `f(M)` outside a finite set of probability at least `1 - η` into one symbol; the
  adversary term and the simulator term each change by at most `η`. We record this as a remark
  and do not formalize it.
* Theorem 4.5 is proved with Pinsker's inequality applied to each row,
  `I(M; C) = ∑_m P_M(m) D(P_{C|M=m} ‖ P_C)`, rather than to the joint law (Lemma 4.2, which is the
  definition of Statlib's `mutualInfo`); the bound is the same, and Lemma 4.4 is formalized
  separately. Pinsker's inequality is proved from the pointwise bound
  `3 (t - 1)² ≤ 2 (t + 2) (t log t - t + 1)` and the Cauchy–Schwarz inequality.
* Lemma 4.8 is proved in an averaged form, `SD(P_{C|M=m}; P_C) ≤ ∑_{m'} P_M(m') SD(P_{C|M=m};
  P_{C|M=m'})` (`SemanticSecurity.tvDistSum_outputLaw_le`); since only `m' ∈ supp P_M` contribute,
  it implies the paper's bound by the pairwise distance `PSD(M; C)` over the support. The corollary
  `SemanticSecurity.tvDistSum_outputLaw_le_of_forall` assumes the bound for all pairs of messages,
  which is what `Adv^ds` provides.

## Notes on the paper

References are to arXiv:1201.2205v2 (23 January 2012).

* **Theorem 4.9, statement (Section 4.4, p. 15).** The bound is stated as `2 ε lg (2^c / ε)`, with
  `c` the length of the *sender* ciphertext. The proof applies Lemma 4.6 to the laws of the
  *adversary* ciphertext `ChA(E(M)) ∈ {0, 1}^d`, so it yields `2 ε lg (2^d / ε)`. We formalize this
  form, with `N = |β|` the size of the adversary alphabet; it agrees with the paper's when `d = c`
  (e.g. for the binary channels `B^c` with a binary base channel). The paper's argument does not
  establish the `2^c` form when `d > c`, and we do not claim it. *Unverified side remark (from a
  review of this file, not checked here):* applying Lemma 4.6 on the message alphabet instead,
  to `P_M` and `P_{M|C=c}`, seems to give a bound `2 ε lg (2^m / ε)`, which would recover the
  `2^c` form whenever `m ≤ c`. A second review (OpenAI Codex) likewise says the sender-alphabet
  form can be recovered separately, via a reduction of the support of a capacity-achieving input;
  this is also not checked here.
* **Theorem 4.9, proof (p. 15).** The proof sets `f(x) = min(2x lg(2^c / x), 1)` and asserts
  `H(P_C) - H(P_{C|M=M}) ≤ f(x)`. Lemma 4.6 does not give the cap `1`, and the claim is false in
  general: for a channel whose row at `M` is a point mass while `P_C` is uniform on four symbols,
  the left side is `2` bits. The theorem is nevertheless true: if `ε ≥ 1/2` (or `N = 1`) then
  `I(M; C) ≤ H(C) ≤ log N ≤ 2 ε log (N / ε)`, and otherwise `t ↦ t log (N / t)` is increasing on
  `[0, ε]` because `ε / N ≤ 1/4 < e⁻¹`. This is the proof of
  `SemanticSecurity.sum_mul_sum_mul_log_le`.
* **Lemma 4.6, proof (p. 14).** "If `P(y) ≥ Q(y)` then `P(y)/2 + δ(y) = Q(y)/2`" should read
  `Q(y)/2 + δ(y) = P(y)/2` (and symmetrically in the other case). This is a typo; the argument and
  the lemma are correct.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- The **distinguishing advantage** `Adv^ds(κ) = max_{m₀, m₁} SD(κ m₀; κ m₁)` of the channel `κ`
from messages to adversary ciphertexts (eq. (6) of Bellare–Tessaro–Vardy, where `κ` is the
composition `ChA ∘ E`). -/
noncomputable def dsAdvantage [Fintype β] (κ : Kernel α β) : ℝ :=
  ⨆ (m₀ : α) (m₁ : α), tvDistSum (fun y ↦ (κ m₀ {y}).toReal) (fun y ↦ (κ m₁ {y}).toReal)

/-- The success probability `P[A(m₀, m₁, C) = b]` in the distinguishing game of eq. (5) of
Bellare–Tessaro–Vardy: the challenge bit `b` is uniform on `{false, true}` (standing for `0, 1`),
`C ∼ κ m_b`, and the adversary `A : Kernel β Bool` sees `C` (it may depend on `m₀`, `m₁`, which
are fixed here). See `isGreatest_dsGameAdvantage` for eq. (5) = eq. (6). -/
noncomputable def dsGameSuccess [Fintype β] (κ : Kernel α β) (m₀ m₁ : α) (A : Kernel β Bool) :
    ℝ :=
  (∑ y, (κ m₀ {y}).toReal * (A y {false}).toReal +
    ∑ y, (κ m₁ {y}).toReal * (A y {true}).toReal) / 2

/-- The **semantic-security advantage** `Adv^ss(κ)` (eq. (3) of Bellare–Tessaro–Vardy): the
supremum, over message distributions `μ` and randomized functions `ρ` of the message with values in
a finite set `Fin n`, of the best probability `max_A P[A(C) = f(M)]` that an adversary `A` observing
`C ∼ κ M` computes `f(M)`, minus the best probability `max_u P[f(M) = u]` of a simulator that sees
nothing (see `blindGuessProb_eq_iSup_simulator`). Restricting `f` to finite ranges loses no
generality (merge the values outside a finite set of probability `≥ 1 - η` into one symbol; both
terms move by at most `η`); this remark is not formalized. -/
noncomputable def ssAdvantage (κ : Kernel α β) : ℝ :=
  sSup {a | ∃ (n : ℕ) (μ : Measure α) (ρ : Kernel α (Fin n)), IsProbabilityMeasure μ ∧
    IsMarkovKernel ρ ∧ a = (⨆ (g : Kernel β (Fin n)) (_ : IsMarkovKernel g),
      guessProb μ ρ κ g).toReal - (blindGuessProb μ ρ).toReal}

end InformationTheory

namespace InformationTheory.SemanticSecurity

/-- The auxiliary function `(t + 1) log t - 2 (t - 1)` is monotone on `(0, ∞)`. -/
private lemma monotoneOn_aux :
    MonotoneOn (fun t : ℝ ↦ (t + 1) * log t - 2 * (t - 1)) (Set.Ioi 0) := by
  have hd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ ↦ (t + 1) * log t - 2 * (t - 1)) (log t + (t + 1) / t - 2) t := by
    intro t ht
    have h1 := ((hasDerivAt_id t).add_const 1).mul (hasDerivAt_log ht.ne')
    have h2 := ((hasDerivAt_id t).sub_const 1).const_mul 2
    convert h1.sub h2 using 1
    · ext s
      simp
    · simp only [id]
      field_simp
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro t ht
    rw [(hd t ht).deriv]
    have := one_sub_inv_le_log_of_pos (Set.mem_Ioi.1 ht)
    have h : (t + 1) / t = 1 + t⁻¹ := by field_simp [(Set.mem_Ioi.1 ht).ne']
    rw [h]
    linarith


/-- The scalar inequality behind Pinsker's inequality:
`3 (t - 1)² ≤ 2 (t + 2) (t log t - t + 1)` for `t ≥ 0`. -/
private lemma three_mul_sq_le (t : ℝ) (ht : 0 ≤ t) :
    3 * (t - 1) ^ 2 ≤ 2 * (t + 2) * (t * log t - t + 1) := by
  set G : ℝ → ℝ := fun t ↦ 2 * (t + 2) * (t * log t - t + 1) - 3 * (t - 1) ^ 2 with hG
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt G (4 * ((t + 1) * log t - 2 * (t - 1))) t := by
    intro t ht
    have h1 := (((hasDerivAt_id t).add_const 2).const_mul 2).mul
      ((((hasDerivAt_id t).mul (hasDerivAt_log ht.ne')).sub (hasDerivAt_id t)).add_const 1)
    have h2 := (((hasDerivAt_id t).sub_const 1).pow 2).const_mul 3
    convert h1.sub h2 using 1
    · ext s
      simp [hG]
    · simp only [id, Pi.mul_apply, Pi.sub_apply]
      field_simp
      ring
  have hcont : Continuous G := by
    simp only [hG]
    fun_prop
  have aux := monotoneOn_aux
  have haux1 : (1 + 1) * log 1 - 2 * (1 - 1) = (0 : ℝ) := by simp
  have hG1 : G 1 = 0 := by simp [hG]
  rcases le_total t 1 with h | h
  · have hanti : AntitoneOn G (Set.Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont.continuousOn ?_ ?_
      · rw [interior_Icc]
        exact fun s hs ↦ (hd s hs.1).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro s hs
        rw [(hd s hs.1).deriv]
        have := aux hs.1 (Set.mem_Ioi.2 one_pos) hs.2.le
        simp only at this
        linarith
    have := hanti ⟨ht, h⟩ ⟨zero_le_one, le_rfl⟩ h
    simp only [hG] at this hG1
    linarith
  · have hmono : MonotoneOn G (Set.Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont.continuousOn ?_ ?_
      · rw [interior_Ici]
        exact fun s hs ↦ (hd s (one_pos.trans hs)).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]
        intro s hs
        rw [(hd s (one_pos.trans hs)).deriv]
        have := aux (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 (one_pos.trans hs)) hs.le
        simp only at this
        linarith
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
    simp only [hG] at this hG1
    linarith


/-- Pointwise form of `three_mul_sq_le`: `3 (p - q)² ≤ 2 (p + 2q) (p log (p / q) - p + q)` for
`p ≥ 0` and `q > 0`. -/
private lemma three_mul_sq_sub_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    3 * (p - q) ^ 2 ≤ 2 * (p + 2 * q) * (p * log (p / q) - p + q) := by
  have h := three_mul_sq_le (p / q) (div_nonneg hp hq.le)
  have e1 : 3 * (p - q) ^ 2 = q ^ 2 * (3 * (p / q - 1) ^ 2) := by
    field_simp
  have e2 : 2 * (p + 2 * q) * (p * log (p / q) - p + q) =
      q ^ 2 * (2 * (p / q + 2) * (p / q * log (p / q) - p / q + 1)) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg q)

end InformationTheory.SemanticSecurity

namespace InformationTheory

open SemanticSecurity in
/-- **Pinsker's inequality** on a finite alphabet, in nats: for probability vectors `p`, `q` with
`p ≪ q`, `2 ‖p - q‖²_TV ≤ D(p ‖ q) = ∑_y p y log (p y / q y)`, where `‖p - q‖_TV` is
`tvDistSum p q = (1/2) ∑_y |p y - q y|`. -/
theorem SemanticSecurity.two_mul_sq_tvDistSum_le {β : Type*} [Fintype β] {p q : β → ℝ}
    (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 ≤ q y) (hp₁ : ∑ y, p y = 1) (hq₁ : ∑ y, q y = 1)
    (hpq : ∀ y, q y = 0 → p y = 0) :
    2 * tvDistSum p q ^ 2 ≤ ∑ y, p y * log (p y / q y) := by
  set D : β → ℝ := fun y ↦ p y * log (p y / q y) - p y + q y with hD_def
  have hD : ∑ y, D y = ∑ y, p y * log (p y / q y) := by
    simp only [D, sum_add_distrib, sum_sub_distrib, hp₁, hq₁, sub_add_cancel]
  have hpt : ∀ y, 0 ≤ D y ∧ |p y - q y| ^ 2 ≤ 2 * D y * ((p y + 2 * q y) / 3) := by
    intro y
    rcases (hq y).eq_or_lt with h | h
    · simp [D, ← h, hpq y h.symm]
    · have key := three_mul_sq_sub_le (hp y) h
      have hpos : 0 < p y + 2 * q y := by linarith [hp y]
      have hD0 : 0 ≤ D y := by
        by_contra! hneg
        nlinarith [sq_nonneg (p y - q y)]
      refine ⟨hD0, ?_⟩
      rw [sq_abs]
      simp only [D] at key ⊢
      linarith
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (r := fun y ↦ |p y - q y|)
    (f := fun y ↦ 2 * D y) (g := fun y ↦ (p y + 2 * q y) / 3)
    (fun y _ ↦ by linarith [(hpt y).1]) (fun y _ ↦ by linarith [hp y, hq y])
    (fun y _ ↦ (hpt y).2)
  have hg : ∑ y, (p y + 2 * q y) / 3 = 1 := by
    rw [← sum_div, sum_add_distrib, ← mul_sum, hp₁, hq₁]
    norm_num
  rw [hg, mul_one, ← mul_sum, hD] at hcs
  have htv : ∑ y, |p y - q y| = 2 * tvDistSum p q := by
    rw [tvDistSum]
    ring
  rw [htv] at hcs
  nlinarith

end InformationTheory

namespace InformationTheory.SemanticSecurity

/-- The tangent-line bound for the concave function `negMulLog`:
`negMulLog a ≤ negMulLog b + (-log b - 1) (a - b)` for `a ≥ 0` and `b > 0`. -/
lemma negMulLog_le_tangent {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    negMulLog a ≤ negMulLog b + (-log b - 1) * (a - b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [negMulLog]
    nlinarith
  have h := log_le_sub_one_of_pos (div_pos hb ha)
  rw [log_div hb.ne' ha.ne'] at h
  have h' : a * (log b - log a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h ha.le
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ ha.ne'] at h'
  simp only [negMulLog]
  nlinarith

/-- `negMulLog` is subadditive on `[0, ∞)`. -/
lemma negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negMulLog (a + b) ≤ negMulLog a + negMulLog b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have h1 : log a ≤ log (a + b) := log_le_log ha (by linarith)
  have h2 : log b ≤ log (a + b) := log_le_log hb (by linarith)
  simp only [negMulLog]
  nlinarith

/-- `negMulLog` is monotone on `[0, e⁻¹]`. -/
lemma negMulLog_le_negMulLog {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ exp (-1)) :
    negMulLog a ≤ negMulLog b := by
  rcases (ha.trans hab).eq_or_lt with h | hb0
  · rw [le_antisymm hab (h ▸ ha)]
  have hlog : log b ≤ -1 := by
    rw [← log_exp (-1)]
    exact log_le_log hb0 hb
  have := negMulLog_le_tangent ha hb0
  nlinarith

/-- **Lemma 4.7 of Bellare–Tessaro–Vardy** (Cover–Thomas (16.24)), in nats: for `p, x ≥ 0` with
`p + x ≤ 1/2`, `|h(p + x) - h(p)| ≤ h(x)` where `h = negMulLog`. -/
theorem abs_negMulLog_add_sub_le {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) (hpx : p + x ≤ 1 / 2) :
    |negMulLog (p + x) - negMulLog p| ≤ negMulLog x := by
  rw [abs_le]
  refine ⟨?_, by linarith [negMulLog_add_le hp hx]⟩
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have ht := negMulLog_le_tangent hp (show 0 < p + x by linarith)
  -- `x (log (p + x) + 1) ≤ -x log x`, since `x (p + x) ≤ 1/4 ≤ e⁻¹`.
  have h4 : 1 < log 4 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have := exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hprod : log (x * (p + x)) ≤ log (1 / 4) :=
    log_le_log (by positivity) (by nlinarith)
  rw [log_mul hx.ne' (by linarith), one_div, log_inv] at hprod
  have : x * (log (p + x) + 1) ≤ -(x * log x) := by nlinarith
  simp only [negMulLog] at ht ⊢
  nlinarith


/-- Jensen's inequality for `negMulLog`: `∑_{y ∈ s} h(δ y) ≤ |s| h((∑_{y ∈ s} δ y) / |s|)`. -/
lemma sum_negMulLog_le_card_mul {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {δ : ι → ℝ}
    (hδ : ∀ y ∈ s, 0 ≤ δ y) :
    ∑ y ∈ s, negMulLog (δ y) ≤ #s * negMulLog ((∑ y ∈ s, δ y) / #s) := by
  have hn : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have hJ := concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ ↦ (#s : ℝ)⁻¹) (p := δ)
    (fun _ _ ↦ by positivity) (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hn.ne'])
    (fun y hy ↦ Set.mem_Ici.2 (hδ y hy))
  simp only [smul_eq_mul, inv_mul_eq_div, ← sum_div] at hJ
  calc ∑ y ∈ s, negMulLog (δ y) = #s * ((∑ y ∈ s, negMulLog (δ y)) / #s) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ hn.le

/-- `n h(ε / n) = ε log (n / ε)` for `n > 0`. -/
lemma mul_negMulLog_div {n ε : ℝ} (hn : 0 < n) :
    n * negMulLog (ε / n) = ε * log (n / ε) := by
  have : log (ε / n) = -log (n / ε) := by rw [← log_inv, inv_div]
  simp only [negMulLog, this]
  field_simp

variable {β : Type*} [Fintype β] {P Q : β → ℝ}

/-- The first step of the proof of Lemma 4.6: `H(P) - H(Q) ≤ 2 ∑_y h(|P y - Q y| / 2)`. -/
lemma sum_negMulLog_sub_le_two_mul_sum (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hP₁ : ∑ y, P y = 1) (hQ₁ : ∑ y, Q y = 1) :
    ∑ y, negMulLog (P y) - ∑ y, negMulLog (Q y) ≤
      2 * ∑ y, negMulLog (|P y - Q y| / 2) := by
  have hQ1 : ∀ y, Q y ≤ 1 := fun y ↦ hQ₁ ▸ single_le_sum (fun y _ ↦ hQ y) (mem_univ y)
  have half (t : ℝ) : negMulLog t = 2 * negMulLog (t / 2) - t * log 2 := by
    rw [div_eq_mul_inv, negMulLog_mul]
    simp only [negMulLog, log_inv]
    ring
  have key (y : β) :
      negMulLog (P y / 2) - negMulLog (Q y / 2) ≤ negMulLog (|P y - Q y| / 2) := by
    rcases le_total (Q y) (P y) with h | h
    · have e : P y / 2 = Q y / 2 + |P y - Q y| / 2 := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [e]
      linarith [negMulLog_add_le (by linarith [hQ y] : 0 ≤ Q y / 2)
        (by positivity : 0 ≤ |P y - Q y| / 2)]
    · have e : Q y / 2 = P y / 2 + |P y - Q y| / 2 := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have := abs_negMulLog_add_sub_le (p := P y / 2) (x := |P y - Q y| / 2)
        (by linarith [hP y]) (by positivity) (by rw [← e]; linarith [hQ1 y])
      rw [← e] at this
      linarith [(abs_le.1 this).1]
  have hsum : ∑ y, negMulLog (P y) - ∑ y, negMulLog (Q y) =
      2 * ∑ y, (negMulLog (P y / 2) - negMulLog (Q y / 2)) := by
    have : ∑ y, (negMulLog (P y) - negMulLog (Q y)) = ∑ y,
        (2 * (negMulLog (P y / 2) - negMulLog (Q y / 2)) - (P y - Q y) * log 2) :=
      sum_congr rfl fun y _ ↦ by rw [half (P y), half (Q y)]; ring
    rw [← sum_sub_distrib, this, sum_sub_distrib, ← sum_mul, sum_sub_distrib, hP₁, hQ₁, mul_sum]
    ring
  rw [hsum]
  exact mul_le_mul_of_nonneg_left (sum_le_sum fun y _ ↦ key y) zero_le_two

/-- The statistical distance as a sum of halved absolute differences. -/
lemma tvDistSum_eq_sum : tvDistSum P Q = ∑ y, |P y - Q y| / 2 := by
  rw [tvDistSum, sum_div]

/-- **Lemma 4.6 of Bellare–Tessaro–Vardy**, in nats: for probability vectors `P`, `Q` with
`ε = SD(P; Q)` and `N = |supp P ∪ supp Q|`, `H(P) - H(Q) ≤ 2 ε log (N / ε)`. -/
theorem sum_negMulLog_sub_le (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hP₁ : ∑ y, P y = 1) (hQ₁ : ∑ y, Q y = 1) :
    ∑ y, negMulLog (P y) - ∑ y, negMulLog (Q y) ≤
      2 * tvDistSum P Q * log (#{y | P y ≠ 0 ∨ Q y ≠ 0} / tvDistSum P Q) := by
  classical
  set S : Finset β := {y | P y ≠ 0 ∨ Q y ≠ 0}
  have hS : S.Nonempty := by
    obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := P) (by rw [hP₁]; simp)
    exact ⟨y, mem_filter.2 ⟨mem_univ y, Or.inl hy⟩⟩
  have hoff (f : ℝ → ℝ) (hf : f 0 = 0) :
      ∑ y ∈ S, f (|P y - Q y| / 2) = ∑ y, f (|P y - Q y| / 2) := by
    refine sum_filter_of_ne fun y _ hy ↦ ?_
    by_contra! h
    simp [h.1, h.2, hf] at hy
  have hε : ∑ y ∈ S, |P y - Q y| / 2 = tvDistSum P Q := by
    rw [tvDistSum_eq_sum]
    exact hoff id rfl
  have hJ := sum_negMulLog_le_card_mul hS (δ := fun y ↦ |P y - Q y| / 2)
    (fun y _ ↦ by positivity)
  rw [hoff negMulLog negMulLog_zero, hε, mul_negMulLog_div (by exact_mod_cast hS.card_pos)] at hJ
  calc _ ≤ 2 * ∑ y, negMulLog (|P y - Q y| / 2) :=
        sum_negMulLog_sub_le_two_mul_sum hP hQ hP₁ hQ₁
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hJ zero_le_two

/-- A variant of Lemma 4.6 with `N = |β|`: `H(P) - H(Q) ≤ 2 |β| h(SD(P; Q) / |β|)`. -/
lemma sum_negMulLog_sub_le_card (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hP₁ : ∑ y, P y = 1) (hQ₁ : ∑ y, Q y = 1) :
    ∑ y, negMulLog (P y) - ∑ y, negMulLog (Q y) ≤
      2 * (Fintype.card β * negMulLog (tvDistSum P Q / Fintype.card β)) := by
  have hne : (univ : Finset β).Nonempty := by
    obtain ⟨y, -, -⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := P) (by rw [hP₁]; simp)
    exact ⟨y, mem_univ y⟩
  have hJ := sum_negMulLog_le_card_mul hne (δ := fun y ↦ |P y - Q y| / 2)
    (fun y _ ↦ by positivity)
  rw [← tvDistSum_eq_sum, card_univ] at hJ
  exact (sum_negMulLog_sub_le_two_mul_sum hP hQ hP₁ hQ₁).trans
    (mul_le_mul_of_nonneg_left hJ zero_le_two)

/-- The entropy of a probability vector is at most `log |β|`. -/
lemma sum_negMulLog_le_log_card (hP : ∀ y, 0 ≤ P y) (hP₁ : ∑ y, P y = 1) :
    ∑ y, negMulLog (P y) ≤ log (Fintype.card β) := by
  have hne : (univ : Finset β).Nonempty := by
    obtain ⟨y, -, -⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := P) (by rw [hP₁]; simp)
    exact ⟨y, mem_univ y⟩
  have hJ := sum_negMulLog_le_card_mul hne (δ := P) (fun y _ ↦ hP y)
  rw [hP₁, card_univ, mul_negMulLog_div (by exact_mod_cast hne.card_pos), div_one,
    one_mul] at hJ
  exact hJ

end InformationTheory.SemanticSecurity

namespace InformationTheory.SemanticSecurity

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {W : α → β → ℝ}

/-- **Lemma 4.8 of Bellare–Tessaro–Vardy**, averaged form: the distance from a row of the channel
to the output law is at most the average distance between rows,
`SD(P_{C|M=m}; P_C) ≤ ∑_{m'} P_M(m') SD(P_{C|M=m}; P_{C|M=m'})`. -/
lemma tvDistSum_outputLaw_le (hp₀ : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1) (x : α) :
    tvDistSum (W x) (outputLaw p W) ≤ ∑ x', p x' * tvDistSum (W x) (W x') := by
  have key (y : β) : |W x y - outputLaw p W y| ≤ ∑ x', p x' * |W x y - W x' y| := by
    have : W x y - outputLaw p W y = ∑ x', p x' * (W x y - W x' y) := by
      simp_rw [outputLaw, mul_sub, sum_sub_distrib, ← sum_mul, hp₁, one_mul]
    rw [this]
    refine (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun x' _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (hp₀ x')]
  unfold tvDistSum
  calc (∑ y, |W x y - outputLaw p W y|) / 2 ≤ (∑ y, ∑ x', p x' * |W x y - W x' y|) / 2 := by
        gcongr with y
        exact key y
    _ = ∑ x', p x' * ((∑ y, |W x y - W x' y|) / 2) := by
        rw [sum_comm, sum_div]
        refine sum_congr rfl fun x' _ ↦ ?_
        rw [← mul_sum, mul_div_assoc]

/-- **Lemma 4.8 of Bellare–Tessaro–Vardy**, for the bound `ε` on all pairs of rows: if every two
rows are within `ε`, then so is every row and the output law, `SD(P_C; P_{C|M=m}) ≤ ε`. The paper
only assumes the bound for pairs in `supp P_M` (its `PSD(M; C)`); that version follows from the
averaged form `tvDistSum_outputLaw_le`, where messages outside the support have weight `0`. -/
lemma tvDistSum_outputLaw_le_of_forall (hp₀ : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1) {ε : ℝ}
    (hε : ∀ x x', tvDistSum (W x) (W x') ≤ ε) (x : α) :
    tvDistSum (W x) (outputLaw p W) ≤ ε :=
  (tvDistSum_outputLaw_le hp₀ hp₁ x).trans <| (sum_le_sum fun x' _ ↦
    mul_le_mul_of_nonneg_left (hε x x') (hp₀ x')).trans_eq (by rw [← sum_mul, hp₁, one_mul])

/-- For `0 ≤ g ≤ 1` and vectors of equal mass, `∑_y (a y - b y) g y ≤ SD(a; b)`. -/
lemma sum_sub_mul_le_tvDistSum {a b g : β → ℝ} (h : ∑ y, a y = ∑ y, b y)
    (hg₀ : ∀ y, 0 ≤ g y) (hg₁ : ∀ y, g y ≤ 1) :
    ∑ y, (a y - b y) * g y ≤ tvDistSum a b := by
  rw [← sum_max_sub_zero_eq_tvDistSum h]
  refine sum_le_sum fun y _ ↦ ?_
  rcases le_total 0 (a y - b y) with hd | hd
  · exact (mul_le_of_le_one_right hd (hg₁ y)).trans (le_max_left _ _)
  · exact (mul_nonpos_of_nonpos_of_nonneg hd (hg₀ y)).trans (le_max_right _ _)

omit [Fintype α] in
lemma sum_outputLaw_eq_one [Fintype α] (hp₁ : ∑ x, p x = 1) (hW₁ : ∀ x, ∑ y, W x y = 1) :
    ∑ y, outputLaw p W y = 1 := by
  simp_rw [outputLaw]
  rw [sum_comm]
  simp_rw [← mul_sum, hW₁, mul_one, hp₁]

end InformationTheory.SemanticSecurity

namespace InformationTheory.SemanticSecurity

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {W : α → β → ℝ}

/-- The mutual information `I(M; C) = ∑_m P_M(m) D(P_{C|M=m} ‖ P_C)` equals
`H(C) - H(C | M) = H(P_C) - ∑_m P_M(m) H(P_{C|M=m})`. -/
lemma sum_mul_sum_mul_log_eq (hp₀ : ∀ x, 0 ≤ p x) (hW₀ : ∀ x y, 0 ≤ W x y) :
    ∑ x, p x * ∑ y, W x y * log (W x y / outputLaw p W y) =
      ∑ y, negMulLog (outputLaw p W y) - ∑ x, p x * ∑ y, negMulLog (W x y) := by
  have hterm (x : α) (y : β) : p x * (W x y * log (W x y / outputLaw p W y)) =
      p x * (W x y * log (W x y)) - p x * W x y * log (outputLaw p W y) := by
    rcases (hp₀ x).eq_or_lt with h | h
    · simp [← h]
    rcases (hW₀ x y).eq_or_lt with h' | h'
    · simp [← h']
    have hν : 0 < outputLaw p W y :=
      lt_of_lt_of_le (mul_pos h h') (single_le_sum (f := fun x ↦ p x * W x y)
        (fun x _ ↦ mul_nonneg (hp₀ x) (hW₀ x y)) (mem_univ x))
    rw [log_div h'.ne' hν.ne']
    ring
  have hν : ∑ x, ∑ y, p x * W x y * log (outputLaw p W y) =
      ∑ y, outputLaw p W y * log (outputLaw p W y) := by
    rw [sum_comm]
    simp_rw [← sum_mul, outputLaw]
  calc ∑ x, p x * ∑ y, W x y * log (W x y / outputLaw p W y)
      = ∑ x, ∑ y, (p x * (W x y * log (W x y)) - p x * W x y * log (outputLaw p W y)) := by
        simp_rw [mul_sum, hterm]
    _ = ∑ x, p x * ∑ y, W x y * log (W x y) - ∑ y, outputLaw p W y * log (outputLaw p W y) := by
        rw [← hν, ← sum_sub_distrib]
        simp_rw [mul_sum, sum_sub_distrib]
    _ = _ := by
        simp only [negMulLog, neg_mul, sum_neg_distrib, mul_neg]
        ring


/-- **Theorem 4.9 of Bellare–Tessaro–Vardy**, finite-sum form, in nats: if every two rows of the
channel are within statistical distance `ε ≤ 1`, then for every prior the mutual information is
at most `2 ε log (|β| / ε)`. -/
theorem sum_mul_sum_mul_log_le (hp₀ : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1)
    (hW₀ : ∀ x y, 0 ≤ W x y) (hW₁ : ∀ x, ∑ y, W x y = 1) {ε : ℝ}
    (hε : ∀ x x', tvDistSum (W x) (W x') ≤ ε) (hε₁ : ε ≤ 1) :
    ∑ x, p x * ∑ y, W x y * log (W x y / outputLaw p W y) ≤
      2 * ε * log (Fintype.card β / ε) := by
  set ν := outputLaw p W
  have hν₀ : ∀ y, 0 ≤ ν y := fun y ↦ sum_nonneg fun x _ ↦ mul_nonneg (hp₀ x) (hW₀ x y)
  have hν₁ : ∑ y, ν y = 1 := sum_outputLaw_eq_one hp₁ hW₁
  have hW1 (x : α) (y : β) : W x y ≤ 1 :=
    hW₁ x ▸ single_le_sum (fun y _ ↦ hW₀ x y) (mem_univ y)
  obtain ⟨x₀⟩ : Nonempty α := nonempty_of_sum_eq_one hp₁
  have : Nonempty β := nonempty_of_sum_eq_one hν₁
  have hε₀ : 0 ≤ ε := tvDistSum_nonneg.trans (hε x₀ x₀)
  set N : ℝ := (Fintype.card β : ℝ) with hN_def
  have hN1 : 1 ≤ N := by
    rw [hN_def]
    exact_mod_cast Fintype.card_pos
  rw [sum_mul_sum_mul_log_eq hp₀ hW₀]
  have hHW : 0 ≤ ∑ x, p x * ∑ y, negMulLog (W x y) := sum_nonneg fun x _ ↦
    mul_nonneg (hp₀ x) (sum_nonneg fun y _ ↦ negMulLog_nonneg (hW₀ x y) (hW1 x y))
  have hrhs : 2 * ε * log (N / ε) = 2 * ε * log N + 2 * negMulLog ε := by
    rcases hε₀.eq_or_lt with h | h
    · simp [← h]
    · rw [log_div (by positivity) h.ne', negMulLog]
      ring
  have hnml : 0 ≤ negMulLog ε := negMulLog_nonneg hε₀ hε₁
  by_cases hcase : 1 / 2 ≤ ε ∨ N ≤ 1
  · -- `I(M; C) ≤ H(C) ≤ log |β| ≤ 2 ε log |β| + 2 h(ε)`.
    have hH := sum_negMulLog_le_log_card hν₀ hν₁
    have hlogN : 0 ≤ log N := log_nonneg hN1
    have : log N ≤ 2 * ε * log N := by
      rcases hcase with h | h
      · nlinarith
      · rw [le_antisymm h hN1, log_one]
        simp
    rw [hrhs]
    linarith
  · -- Otherwise `ε / |β| ≤ 1/4 ≤ e⁻¹`, where `negMulLog` is monotone.
    push Not at hcase
    obtain ⟨hε2, hN⟩ := hcase
    have hN0 : 0 < N := by linarith
    have he : ε / N ≤ exp (-1) := by
      have h4 : (1 : ℝ) / 4 ≤ exp (-1) := by
        rw [exp_neg, one_div]
        exact inv_anti₀ (exp_pos 1) (by linarith [exp_one_lt_d9])
      have hN2 : (2 : ℝ) ≤ N := by
        rw [hN_def] at hN ⊢
        exact_mod_cast (show 1 < Fintype.card β by exact_mod_cast hN)
      calc ε / N ≤ (1 / 2) / 2 := div_le_div₀ (by norm_num) hε2.le (by norm_num) hN2
        _ ≤ _ := by linarith
    have hrow (x : α) : ∑ y, negMulLog (ν y) - ∑ y, negMulLog (W x y) ≤
        2 * ε * log (N / ε) := by
      have h1 := sum_negMulLog_sub_le_card hν₀ (hW₀ x) hν₁ (hW₁ x)
      have ht : tvDistSum ν (W x) ≤ ε := by
        rw [tvDistSum_comm]
        exact tvDistSum_outputLaw_le_of_forall hp₀ hp₁ hε x
      have hmono : negMulLog (tvDistSum ν (W x) / N) ≤ negMulLog (ε / N) :=
        negMulLog_le_negMulLog (div_nonneg tvDistSum_nonneg hN0.le)
          (div_le_div_of_nonneg_right ht hN0.le) he
      rw [mul_assoc, ← mul_negMulLog_div hN0]
      rw [← hN_def] at h1
      nlinarith
    calc ∑ y, negMulLog (ν y) - ∑ x, p x * ∑ y, negMulLog (W x y)
        = ∑ x, p x * (∑ y, negMulLog (ν y) - ∑ y, negMulLog (W x y)) := by
          simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, hp₁, one_mul]
      _ ≤ ∑ x, p x * (2 * ε * log (N / ε)) :=
          sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hrow x) (hp₀ x)
      _ = 2 * ε * log (N / ε) := by rw [← sum_mul, hp₁, one_mul]

end InformationTheory.SemanticSecurity

namespace InformationTheory.SemanticSecurity

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {W : α → β → ℝ}

/-- Pinsker's inequality averaged over the prior:
`2 ∑_m P_M(m) SD(P_{C|M=m}; P_C)² ≤ I(M; C)`. -/
lemma two_mul_sum_mul_sq_le (hp₀ : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1)
    (hW₀ : ∀ x y, 0 ≤ W x y) (hW₁ : ∀ x, ∑ y, W x y = 1) :
    2 * ∑ x, p x * tvDistSum (W x) (outputLaw p W) ^ 2 ≤
      ∑ x, p x * ∑ y, W x y * log (W x y / outputLaw p W y) := by
  rw [mul_sum]
  refine sum_le_sum fun x _ ↦ ?_
  rcases (hp₀ x).eq_or_lt with h | h
  · simp [← h]
  have hpin := two_mul_sq_tvDistSum_le (q := outputLaw p W) (hW₀ x)
    (fun y ↦ sum_nonneg fun x _ ↦ mul_nonneg (hp₀ x) (hW₀ x y)) (hW₁ x)
    (sum_outputLaw_eq_one hp₁ hW₁) fun y hy ↦ by
      have : p x * W x y ≤ outputLaw p W y := single_le_sum (f := fun x ↦ p x * W x y)
        (fun x _ ↦ mul_nonneg (hp₀ x) (hW₀ x y)) (mem_univ x)
      rw [hy] at this
      exact le_antisymm (nonpos_of_mul_nonpos_right this h) (hW₀ x y)
  nlinarith

/-- Averages under the uniform prior on two messages `m₀`, `m₁`. -/
lemma sum_twoPoint [DecidableEq α] {m₀ m₁ : α}
    (hp : ∀ x, p x = (if x = m₀ then 1 / 2 else 0) + (if x = m₁ then 1 / 2 else 0))
    (f : α → ℝ) : ∑ x, p x * f x = f m₀ / 2 + f m₁ / 2 := by
  simp_rw [hp, add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  ring

/-- For `M` uniform on `{m₀, m₁}`, each of the two rows is at statistical distance
`SD(P_{C|M=m₀}; P_{C|M=m₁}) / 2` from the output law. -/
lemma tvDistSum_outputLaw_twoPoint [DecidableEq α] {m₀ m₁ : α}
    (hp : ∀ x, p x = (if x = m₀ then 1 / 2 else 0) + (if x = m₁ then 1 / 2 else 0)) :
    tvDistSum (W m₀) (outputLaw p W) = tvDistSum (W m₀) (W m₁) / 2 ∧
      tvDistSum (W m₁) (outputLaw p W) = tvDistSum (W m₀) (W m₁) / 2 := by
  have hν (y : β) : outputLaw p W y = W m₀ y / 2 + W m₁ y / 2 :=
    sum_twoPoint hp (fun x ↦ W x y)
  have e₀ (y : β) : |W m₀ y - (W m₀ y / 2 + W m₁ y / 2)| = |W m₀ y - W m₁ y| / 2 := by
    rw [show W m₀ y - (W m₀ y / 2 + W m₁ y / 2) = (W m₀ y - W m₁ y) / 2 by ring, abs_div,
      abs_two]
  have e₁ (y : β) : |W m₁ y - (W m₀ y / 2 + W m₁ y / 2)| = |W m₀ y - W m₁ y| / 2 := by
    rw [show W m₁ y - (W m₀ y / 2 + W m₁ y / 2) = (W m₁ y - W m₀ y) / 2 by ring, abs_div,
      abs_two, abs_sub_comm]
  constructor
  · simp_rw [tvDistSum, hν, e₀, ← sum_div]
  · simp_rw [tvDistSum, hν, e₁, ← sum_div]

/-- **Lemma 4.4 of Bellare–Tessaro–Vardy**, finite-sum form: for `M` uniform on `{m₀, m₁}` and
`C` the output of the channel `W`, the statistical distance between the joint law
`J(m, c) = P_M(m) W(c | m)` and the product law `I(m, c) = P_M(m) P_C(c)` is
`SD(W(· | m₀); W(· | m₁)) / 2`. -/
theorem tvDistSum_joint_twoPoint [DecidableEq α] {m₀ m₁ : α}
    (hp : ∀ x, p x = (if x = m₀ then 1 / 2 else 0) + (if x = m₁ then 1 / 2 else 0)) :
    tvDistSum (fun z : α × β ↦ p z.1 * W z.1 z.2) (fun z ↦ p z.1 * outputLaw p W z.2) =
      tvDistSum (W m₀) (W m₁) / 2 := by
  have hp₀ (x : α) : 0 ≤ p x := by rw [hp x]; split_ifs <;> norm_num
  have h : tvDistSum (fun z : α × β ↦ p z.1 * W z.1 z.2) (fun z ↦ p z.1 * outputLaw p W z.2) =
      ∑ x, p x * tvDistSum (W x) (outputLaw p W) := by
    simp_rw [tvDistSum, Fintype.sum_prod_type, ← mul_sub, abs_mul, abs_of_nonneg (hp₀ _),
      ← mul_sum, sum_div, mul_div_assoc, sum_div]
  rw [h, sum_twoPoint hp, (tvDistSum_outputLaw_twoPoint hp).1,
    (tvDistSum_outputLaw_twoPoint hp).2]
  ring

/-- The core of **Theorem 4.5 of Bellare–Tessaro–Vardy**, finite-sum form: for `M` uniform on
`{m₀, m₁}`, `SD(W(· | m₀); W(· | m₁))² / 2 ≤ I(M; C)`. -/
lemma sq_tvDistSum_div_two_le [DecidableEq α] {m₀ m₁ : α}
    (hp : ∀ x, p x = (if x = m₀ then 1 / 2 else 0) + (if x = m₁ then 1 / 2 else 0))
    (hW₀ : ∀ x y, 0 ≤ W x y) (hW₁ : ∀ x, ∑ y, W x y = 1) :
    tvDistSum (W m₀) (W m₁) ^ 2 / 2 ≤
      ∑ x, p x * ∑ y, W x y * log (W x y / outputLaw p W y) := by
  have hp₀ (x : α) : 0 ≤ p x := by rw [hp x]; split_ifs <;> norm_num
  have hp₁ : ∑ x, p x = 1 := by
    have := sum_twoPoint hp (fun _ ↦ 1)
    simp only [mul_one] at this
    rw [this]
    norm_num
  have := two_mul_sum_mul_sq_le hp₀ hp₁ hW₀ hW₁
  rw [sum_twoPoint hp (fun x ↦ tvDistSum (W x) (outputLaw p W) ^ 2),
    (tvDistSum_outputLaw_twoPoint hp).1, (tvDistSum_outputLaw_twoPoint hp).2] at this
  linarith

end InformationTheory.SemanticSecurity

namespace InformationTheory.SemanticSecurity

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {W : α → β → ℝ}

/-- The core of `Adv^ss ≤ Adv^ds` (Theorem 4.1), finite-sum form: if every two rows of the channel
are within `ε`, an adversary `G` guessing the value of a randomized function `F` of the message
succeeds with probability at most `B + ε`, where `B` bounds every `P[F(M) = u]`. -/
lemma sum_guess_le_add {γ : Type*} [Fintype γ] {F : α → γ → ℝ} {G : β → γ → ℝ}
    (hp₀ : ∀ x, 0 ≤ p x) (hp₁ : ∑ x, p x = 1) (hW₀ : ∀ x y, 0 ≤ W x y)
    (hW₁ : ∀ x, ∑ y, W x y = 1) (hF₀ : ∀ x u, 0 ≤ F x u) (hF₁ : ∀ x, ∑ u, F x u = 1)
    (hG₀ : ∀ y u, 0 ≤ G y u) (hG₁ : ∀ y, ∑ u, G y u = 1) {B : ℝ}
    (hB : ∀ u, ∑ x, F x u * p x ≤ B) {ε : ℝ} (hε : ∀ x x', tvDistSum (W x) (W x') ≤ ε) :
    ∑ x, ∑ u, ∑ y, G y u * W x y * F x u * p x ≤ B + ε := by
  set ν := outputLaw p W
  have hν₁ : ∑ y, ν y = 1 := sum_outputLaw_eq_one hp₁ hW₁
  set a : α → β → ℝ := fun x y ↦ ∑ u, G y u * F x u with ha_def
  have hF1 (x : α) (u : γ) : F x u ≤ 1 :=
    hF₁ x ▸ single_le_sum (fun u _ ↦ hF₀ x u) (mem_univ u)
  have ha₀ (x : α) (y : β) : 0 ≤ a x y := sum_nonneg fun u _ ↦ mul_nonneg (hG₀ y u) (hF₀ x u)
  have ha₁ (x : α) (y : β) : a x y ≤ 1 :=
    (sum_le_sum fun u _ ↦ mul_le_of_le_one_right (hG₀ y u) (hF1 x u)).trans_eq (hG₁ y)
  have hlhs : ∑ x, ∑ u, ∑ y, G y u * W x y * F x u * p x = ∑ x, p x * ∑ y, W x y * a x y := by
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun u _ ↦ by ring
  -- Replacing the ciphertext by an independent one leaves success probability at most `B`.
  have hind : ∑ x, p x * ∑ y, ν y * a x y ≤ B := by
    have : ∑ x, p x * ∑ y, ν y * a x y = ∑ y, ν y * ∑ u, G y u * ∑ x, F x u * p x := by
      simp only [ha_def, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun y _ ↦ ?_
      rw [sum_comm]
      exact sum_congr rfl fun u _ ↦ sum_congr rfl fun x _ ↦ by ring
    rw [this]
    calc ∑ y, ν y * ∑ u, G y u * ∑ x, F x u * p x ≤ ∑ y, ν y * ∑ u, G y u * B :=
          sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left
            (sum_le_sum fun u _ ↦ mul_le_mul_of_nonneg_left (hB u) (hG₀ y u))
            (sum_nonneg fun x _ ↦ mul_nonneg (hp₀ x) (hW₀ x y))
      _ = B := by
          simp_rw [← sum_mul, hG₁, one_mul]
          rw [← sum_mul, hν₁, one_mul]
  have hdiff : ∑ x, p x * ∑ y, W x y * a x y - ∑ x, p x * ∑ y, ν y * a x y ≤ ε := by
    rw [← sum_sub_distrib]
    calc ∑ x, (p x * ∑ y, W x y * a x y - p x * ∑ y, ν y * a x y)
        = ∑ x, p x * ∑ y, (W x y - ν y) * a x y := by
          simp_rw [← mul_sub, ← sum_sub_distrib, sub_mul]
      _ ≤ ∑ x, p x * ε := sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left
          ((sum_sub_mul_le_tvDistSum (by rw [hW₁, hν₁]) (ha₀ x)
            (ha₁ x)).trans (tvDistSum_outputLaw_le_of_forall hp₀ hp₁ hε x)) (hp₀ x)
      _ = ε := by rw [← sum_mul, hp₁, one_mul]
  rw [hlhs]
  linarith

/-- `∑_y max (a y) (b y) = 1 + SD(a; b)` for probability vectors. -/
lemma sum_max_eq_one_add_tvDistSum {a b : β → ℝ} (ha : ∑ y, a y = 1) (hb : ∑ y, b y = 1) :
    ∑ y, max (a y) (b y) = 1 + tvDistSum a b := by
  have h (y : β) : max (a y) (b y) = (a y + b y + |a y - b y|) / 2 := by
    rcases le_total (a y) (b y) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      ring
  simp_rw [h, ← sum_div, sum_add_distrib, ha, hb, tvDistSum]
  ring


/-- The core of `Adv^ds ≤ 2 Adv^ss` (Theorem 4.1), finite-sum form: for `M` uniform on two distinct
messages, `F` the indicator of `M = m₁` and `G` the maximum-likelihood guess of it, the success
probability is `(1 + SD(P_{C|M=m₀}; P_{C|M=m₁})) / 2`. -/
lemma sum_guess_twoPoint [DecidableEq α] {m₀ m₁ : α} (hm : m₀ ≠ m₁)
    (hp : ∀ x, p x = (if x = m₀ then 1 / 2 else 0) + (if x = m₁ then 1 / 2 else 0))
    (hW₁ : ∀ x, ∑ y, W x y = 1) {F : α → Fin 2 → ℝ}
    (hF : ∀ x u, F x u = if (if x = m₀ then 0 else 1) = u then 1 else 0) {G : β → Fin 2 → ℝ}
    (hG : ∀ y u, G y u = if (if W m₁ y ≤ W m₀ y then 0 else 1) = u then 1 else 0) :
    ∑ x, ∑ u, ∑ y, G y u * W x y * F x u * p x = (1 + tvDistSum (W m₀) (W m₁)) / 2 := by
  have h : ∀ x, ∑ u, ∑ y, G y u * W x y * F x u * p x = p x * ∑ u, ∑ y, G y u * W x y * F x u :=
    fun x ↦ by
      simp_rw [mul_sum]
      exact sum_congr rfl fun u _ ↦ sum_congr rfl fun y _ ↦ by ring
  rw [sum_congr rfl fun x _ ↦ h x, sum_twoPoint hp, ← add_div,
    ← sum_max_eq_one_add_tvDistSum (hW₁ m₀) (hW₁ m₁)]
  congr 1
  simp only [Fin.sum_univ_two, hF, hG, hm.symm, ite_true, ite_false, Fin.isValue, zero_ne_one,
    one_ne_zero, mul_one, mul_zero, sum_const_zero, add_zero, zero_add, ← sum_add_distrib]
  refine sum_congr rfl fun y _ ↦ ?_
  by_cases h' : W m₁ y ≤ W m₀ y
  · simp [h']
  · simp [h', max_eq_right (not_le.1 h').le]

end InformationTheory.SemanticSecurity

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

namespace SemanticSecurity

/-- The atoms of a probability measure on a finite space sum to `1`. -/
lemma sum_toReal_singleton [Fintype β] [MeasurableSingletonClass β] (ν : Measure β)
    [IsProbabilityMeasure ν] : ∑ y, (ν {y}).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _, sum_measure_singleton, coe_univ,
    measure_univ, ENNReal.toReal_one]

/-- The output law `P_U(u) = ∑_x ρ(u | x) μ(x)`, in real coordinates. -/
lemma toReal_comp_apply_singleton [Fintype α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass γ] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ : Kernel α γ) [IsMarkovKernel ρ] (u : γ) :
    ((ρ ∘ₘ μ) {u}).toReal = ∑ x, (ρ x {u}).toReal * (μ {x}).toReal := by
  rw [comp_apply_singleton, ENNReal.toReal_sum fun x _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp_rw [ENNReal.toReal_mul]

/-- `P[U = Û]` as a finite sum, in real coordinates. -/
lemma toReal_guessProb [Fintype α] [MeasurableSingletonClass α] [Fintype β]
    [MeasurableSingletonClass β] [Fintype γ] [MeasurableSingletonClass γ] {μ : Measure α}
    [IsFiniteMeasure μ] {κ : Kernel α β} [IsMarkovKernel κ] {ρ : Kernel α γ} [IsMarkovKernel ρ]
    {g : Kernel β γ} [IsMarkovKernel g] :
    (guessProb μ ρ κ g).toReal =
      ∑ x, ∑ u, ∑ y, (g y {u}).toReal * (κ x {y}).toReal * (ρ x {u}).toReal * (μ {x}).toReal := by
  have h4 (x : α) (u : γ) (y : β) : g y {u} * κ x {y} * ρ x {u} * μ {x} ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)) (measure_ne_top _ _)) (measure_ne_top _ _)
  rw [guessProb_eq_sum, ENNReal.toReal_sum fun x _ ↦ ENNReal.sum_ne_top.2 fun u _ ↦
    ENNReal.sum_ne_top.2 fun y _ ↦ h4 x u y]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [ENNReal.toReal_sum fun u _ ↦ ENNReal.sum_ne_top.2 fun y _ ↦ h4 x u y]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [ENNReal.toReal_sum fun y _ ↦ h4 x u y]
  simp_rw [ENNReal.toReal_mul]

/-- A success probability is at most `1`. -/
lemma guessProb_le_one {μ : Measure α} [IsProbabilityMeasure μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {ρ : Kernel α γ} [IsMarkovKernel ρ] {g : Kernel β γ} [IsMarkovKernel g] :
    guessProb μ ρ κ g ≤ 1 :=
  prob_le_one

/-- The blind guessing probability is at most `1`. -/
lemma blindGuessProb_le_one {μ : Measure α} [IsProbabilityMeasure μ] {ρ : Kernel α γ}
    [IsMarkovKernel ρ] : blindGuessProb μ ρ ≤ 1 :=
  iSup_le fun _ ↦ prob_le_one

end SemanticSecurity

end InformationTheory

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

open SemanticSecurity

/-- The statistical distance between probability vectors is at most `1`. -/
lemma SemanticSecurity.tvDistSum_le_one {a b : β → ℝ} [Fintype β] (ha₀ : ∀ y, 0 ≤ a y)
    (ha₁ : ∑ y, a y = 1) (hb₀ : ∀ y, 0 ≤ b y) (hb₁ : ∑ y, b y = 1) : tvDistSum a b ≤ 1 := by
  have : ∑ y, |a y - b y| ≤ ∑ y, (a y + b y) := sum_le_sum fun y _ ↦
    (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (ha₀ y), abs_of_nonneg (hb₀ y)])
  rw [sum_add_distrib, ha₁, hb₁] at this
  rw [tvDistSum]
  linarith

section DS

variable [Fintype β] {κ : Kernel α β}

/-- Every two rows of `κ` are within statistical distance `Adv^ds`. -/
lemma tvDistSum_le_dsAdvantage [Finite α] (m₀ m₁ : α) :
    tvDistSum (fun y ↦ (κ m₀ {y}).toReal) (fun y ↦ (κ m₁ {y}).toReal) ≤ dsAdvantage κ :=
  le_ciSup_of_le (Set.finite_range _).bddAbove m₀ <|
    le_ciSup (f := fun m₁ ↦ tvDistSum (fun y ↦ (κ m₀ {y}).toReal) (fun y ↦ (κ m₁ {y}).toReal))
      (Set.finite_range _).bddAbove m₁

/-- `Adv^ds` is nonnegative. -/
lemma dsAdvantage_nonneg : 0 ≤ dsAdvantage κ :=
  Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg fun _ ↦ tvDistSum_nonneg

/-- `Adv^ds ≤ 1`. -/
lemma dsAdvantage_le_one [MeasurableSingletonClass β] [IsMarkovKernel κ] : dsAdvantage κ ≤ 1 :=
  Real.iSup_le (fun m₀ ↦ Real.iSup_le (fun m₁ ↦ tvDistSum_le_one (fun _ ↦ ENNReal.toReal_nonneg)
    (sum_toReal_singleton (κ m₀)) (fun _ ↦ ENNReal.toReal_nonneg) (sum_toReal_singleton (κ m₁)))
    zero_le_one) zero_le_one

/-- **Eq. (5) = eq. (6) of Bellare–Tessaro–Vardy**: for fixed messages `m₀`, `m₁`, the largest
advantage `2 P[A wins] - 1` of an adversary in the distinguishing game is `SD(κ m₀; κ m₁)`; no
adversary does better, and the maximum-likelihood adversary attains it. -/
theorem isGreatest_dsGameAdvantage [MeasurableSingletonClass β] [IsMarkovKernel κ] (m₀ m₁ : α) :
    IsGreatest {t | ∃ A : Kernel β Bool, IsMarkovKernel A ∧ t = 2 * dsGameSuccess κ m₀ m₁ A - 1}
      (tvDistSum (fun y ↦ (κ m₀ {y}).toReal) (fun y ↦ (κ m₁ {y}).toReal)) := by
  have h₀ : ∑ y, (κ m₀ {y}).toReal = 1 := sum_toReal_singleton (κ m₀)
  have h₁ : ∑ y, (κ m₁ {y}).toReal = 1 := sum_toReal_singleton (κ m₁)
  -- The game advantage of `A` is `∑_y (κ m₁ {y} - κ m₀ {y}) P[A(y) = true]`.
  have hgame (A : Kernel β Bool) [IsMarkovKernel A] : 2 * dsGameSuccess κ m₀ m₁ A - 1 =
      ∑ y, ((κ m₁ {y}).toReal - (κ m₀ {y}).toReal) * (A y {true}).toReal := by
    have hA (y : β) : (A y {false}).toReal = 1 - (A y {true}).toReal := by
      have := sum_toReal_singleton (A y)
      rw [Fintype.sum_bool] at this
      linarith
    simp only [dsGameSuccess, hA, mul_sub, mul_one, sum_sub_distrib, sub_mul, h₀]
    ring
  have hsum : ∑ y, (κ m₁ {y}).toReal = ∑ y, (κ m₀ {y}).toReal := h₁.trans h₀.symm
  refine ⟨⟨Kernel.deterministic (fun y ↦ decide ((κ m₀ {y}).toReal < (κ m₁ {y}).toReal))
    (measurable_of_finite _), inferInstance, ?_⟩, ?_⟩
  · rw [hgame, tvDistSum_comm, ← sum_filter_lt_sub_eq_tvDistSum hsum, ← sum_sub_distrib,
      sum_filter]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [Kernel.deterministic_apply' _ _ (measurableSet_singleton true)]
    by_cases h : (κ m₀ {y}).toReal < (κ m₁ {y}).toReal <;> simp [h]
  · rintro _ ⟨A, hA, rfl⟩
    rw [hgame, tvDistSum_comm]
    refine sum_sub_mul_le_tvDistSum hsum (fun _ ↦ ENNReal.toReal_nonneg) fun y ↦ ?_
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := A y) (s := {true}))

/-- `Adv^ds` defined by the game (5) agrees with `dsAdvantage`, defined by (6). -/
theorem dsAdvantage_eq_iSup_sSup_dsGame [MeasurableSingletonClass β] [IsMarkovKernel κ] :
    dsAdvantage κ = ⨆ (m₀ : α) (m₁ : α),
      sSup {t | ∃ A : Kernel β Bool, IsMarkovKernel A ∧ t = 2 * dsGameSuccess κ m₀ m₁ A - 1} :=
  iSup_congr fun m₀ ↦ iSup_congr fun m₁ ↦ (isGreatest_dsGameAdvantage m₀ m₁).csSup_eq.symm

end DS

namespace SemanticSecurity

section TwoPoint

variable {M : Type*} [MeasurableSpace M]

/-- The uniform distribution `(δ_{m₀} + δ_{m₁}) / 2` on two messages. -/
noncomputable def twoPoint (m₀ m₁ : M) : Measure M :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac m₀ + Measure.dirac m₁)

/-- The two-point prior is a probability measure. -/
instance (m₀ m₁ : M) : IsProbabilityMeasure (twoPoint m₀ m₁) :=
  ⟨by simp [twoPoint, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- The atoms of `twoPoint m₀ m₁`. -/
lemma toReal_twoPoint_singleton [MeasurableSingletonClass M] [DecidableEq M] {m₀ m₁ : M}
    (x : M) : (twoPoint m₀ m₁ {x}).toReal =
      (if x = m₀ then 1 / 2 else 0) + (if x = m₁ then 1 / 2 else 0) := by
  simp only [twoPoint, smul_apply, add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  by_cases h₀ : x = m₀ <;> by_cases h₁ : x = m₁ <;> simp_all [eq_comm]
  norm_num

end TwoPoint

end SemanticSecurity

section SS

variable {κ : Kernel α β}

/-- A simulator, which sees nothing, guesses `f(M)` with probability at most
`max_u P[f(M) = u]`, and this is the supremum over simulators: `blindGuessProb` is the simulator
term of eq. (3). The equality holds for every finite `γ`; for empty `γ` there is no probability
measure on `γ` and both sides are empty suprema (`0`). For nonempty `γ` the supremum is attained
by a deterministic simulator: `exists_simulator_eq_blindGuessProb`. -/
theorem blindGuessProb_eq_iSup_simulator [Fintype γ] [MeasurableSingletonClass γ] (μ : Measure α)
    (ρ : Kernel α γ) :
    blindGuessProb μ ρ =
      ⨆ (s : Measure γ) (_ : IsProbabilityMeasure s), ∑ u, s {u} * (ρ ∘ₘ μ) {u} := by
  refine le_antisymm (iSup_le fun u ↦ ?_) (iSup₂_le fun s _ ↦ ?_)
  · refine le_iSup₂_of_le (Measure.dirac u) inferInstance (le_of_eq ?_)
    rw [sum_eq_single u (fun v _ hv ↦ by simp [Measure.dirac_apply', hv.symm]) (by simp)]
    simp
  · calc ∑ u, s {u} * (ρ ∘ₘ μ) {u} ≤ ∑ u, s {u} * blindGuessProb μ ρ :=
          sum_le_sum fun u _ ↦ by
            gcongr
            exact le_iSup (fun u ↦ (ρ ∘ₘ μ) {u}) u
      _ = blindGuessProb μ ρ := by
          rw [← sum_mul, sum_measure_singleton, coe_univ, measure_univ, one_mul]

/-- For a nonempty finite alphabet `γ`, the simulator term of eq. (3) is attained: the
deterministic simulator `S = u*`, for `u*` maximizing `P[f(M) = u]`, has success probability
`blindGuessProb μ ρ`. -/
theorem exists_simulator_eq_blindGuessProb [Fintype γ] [Nonempty γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (ρ : Kernel α γ) :
    ∃ (s : Measure γ), IsProbabilityMeasure s ∧
      ∑ u, s {u} * (ρ ∘ₘ μ) {u} = blindGuessProb μ ρ := by
  obtain ⟨u, hu⟩ := exists_eq_ciSup_of_finite (f := fun u ↦ (ρ ∘ₘ μ) {u})
  refine ⟨Measure.dirac u, inferInstance, ?_⟩
  rw [sum_eq_single u (fun v _ hv ↦ by simp [Measure.dirac_apply', hv.symm]) (by simp)]
  simpa [blindGuessProb] using hu

/-- The best adversarial success probability is finite. -/
lemma SemanticSecurity.iSup_guessProb_ne_top [IsMarkovKernel κ] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {ρ : Kernel α γ} [IsMarkovKernel ρ] :
    (⨆ (g : Kernel β γ) (_ : IsMarkovKernel g), guessProb μ ρ κ g) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup₂_le fun _ _ ↦ guessProb_le_one)

/-- The advantages in the definition of `Adv^ss` are bounded above (by `1`). -/
lemma SemanticSecurity.bddAbove_ssAdvantage [IsMarkovKernel κ] :
    BddAbove {a | ∃ (n : ℕ) (μ : Measure α) (ρ : Kernel α (Fin n)), IsProbabilityMeasure μ ∧
      IsMarkovKernel ρ ∧ a = (⨆ (g : Kernel β (Fin n)) (_ : IsMarkovKernel g),
        guessProb μ ρ κ g).toReal - (blindGuessProb μ ρ).toReal} := by
  refine ⟨1, fun a ⟨n, μ, ρ, hμ, hρ, ha⟩ ↦ ?_⟩
  have h1 : (⨆ (g : Kernel β (Fin n)) (_ : IsMarkovKernel g), guessProb μ ρ κ g).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]
      exact iSup₂_le fun _ _ ↦ guessProb_le_one)
  rw [ha]
  linarith [ENNReal.toReal_nonneg (a := blindGuessProb μ ρ)]

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] [IsMarkovKernel κ]

/-- An adversary can do at least as well as a simulator: it may ignore the ciphertext. -/
lemma SemanticSecurity.toReal_blindGuessProb_le [Finite β] [Finite γ] [MeasurableSingletonClass γ]
    {μ : Measure α} [IsProbabilityMeasure μ] {ρ : Kernel α γ} [IsMarkovKernel ρ] :
    (blindGuessProb μ ρ).toReal ≤
      (⨆ (g : Kernel β γ) (_ : IsMarkovKernel g), guessProb μ ρ κ g).toReal := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  rw [blindGuessProb, ENNReal.toReal_iSup fun u ↦ measure_ne_top _ _]
  refine Real.iSup_le (fun u ↦ ?_) ENNReal.toReal_nonneg
  refine le_of_eq_of_le ?_ (ENNReal.toReal_mono iSup_guessProb_ne_top
    (le_iSup₂ (f := fun g (_ : IsMarkovKernel g) ↦ guessProb μ ρ κ g)
      (Kernel.const β (Measure.dirac u)) inferInstance))
  rw [toReal_comp_apply_singleton, toReal_guessProb]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [sum_eq_single u (fun v _ hv ↦ by simp [Measure.dirac_apply', hv.symm]) (by simp)]
  simp_rw [Kernel.const_apply, Measure.dirac_apply_of_mem (Set.mem_singleton u),
    ENNReal.toReal_one, one_mul, ← sum_mul, sum_toReal_singleton (κ x), one_mul]

/-- `Adv^ss` is nonnegative. -/
lemma ssAdvantage_nonneg [Finite β] : 0 ≤ ssAdvantage κ := by
  refine Real.sSup_nonneg fun a ⟨n, μ, ρ, hμ, hρ, ha⟩ ↦ ?_
  rw [ha, sub_nonneg]
  exact toReal_blindGuessProb_le

/-- **Theorem 4.1 of Bellare–Tessaro–Vardy, first inequality**: `Adv^ss ≤ Adv^ds`, so DS-security
implies semantic security. -/
theorem ssAdvantage_le_dsAdvantage [Fintype β] : ssAdvantage κ ≤ dsAdvantage κ := by
  have := Fintype.ofFinite α
  refine Real.sSup_le ?_ dsAdvantage_nonneg
  rintro _ ⟨n, μ, ρ, hμ, hρ, rfl⟩
  set B := (blindGuessProb μ ρ).toReal
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hsup : (⨆ (g : Kernel β (Fin n)) (_ : IsMarkovKernel g), guessProb μ ρ κ g) ≤
      ENNReal.ofReal (B + dsAdvantage κ) := by
    refine iSup₂_le fun g hg ↦ ?_
    rw [ENNReal.le_ofReal_iff_toReal_le (ne_top_of_le_ne_top ENNReal.one_ne_top guessProb_le_one)
      (add_nonneg hB0 dsAdvantage_nonneg), toReal_guessProb]
    refine sum_guess_le_add (p := fun x ↦ (μ {x}).toReal) (W := fun x y ↦ (κ x {y}).toReal)
      (F := fun x u ↦ (ρ x {u}).toReal) (G := fun y u ↦ (g y {u}).toReal)
      (fun x ↦ ENNReal.toReal_nonneg) (sum_toReal_singleton μ)
      (fun x y ↦ ENNReal.toReal_nonneg) (fun x ↦ sum_toReal_singleton (κ x))
      (fun x u ↦ ENNReal.toReal_nonneg) (fun x ↦ sum_toReal_singleton (ρ x))
      (fun y u ↦ ENNReal.toReal_nonneg) (fun y ↦ sum_toReal_singleton (g y)) (fun u ↦ ?_)
      tvDistSum_le_dsAdvantage
    rw [← toReal_comp_apply_singleton]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top blindGuessProb_le_one)
      (le_iSup (fun u ↦ (ρ ∘ₘ μ) {u}) u)
  have := ENNReal.toReal_le_of_le_ofReal (add_nonneg hB0 dsAdvantage_nonneg) hsup
  linarith

/-- **Theorem 4.1 of Bellare–Tessaro–Vardy, second inequality**: `Adv^ds ≤ 2 · Adv^ss`, so semantic
security implies DS-security. The witness is the uniform prior on two messages, the function
`f(M) = [M ≠ m₀]` with values in `Fin 2`, and the maximum-likelihood adversary. -/
theorem dsAdvantage_le_two_mul_ssAdvantage [Fintype β] : dsAdvantage κ ≤ 2 * ssAdvantage κ := by
  classical
  have := Fintype.ofFinite α
  have h0 : 0 ≤ ssAdvantage κ := ssAdvantage_nonneg
  refine Real.iSup_le (fun m₀ ↦ Real.iSup_le (fun m₁ ↦ ?_) (by positivity)) (by positivity)
  rcases eq_or_ne m₀ m₁ with rfl | hm
  · simp only [tvDistSum, sub_self, abs_zero, sum_const_zero, zero_div]
    positivity
  -- `M` uniform on `{m₀, m₁}`, `f(M) = [M ≠ m₀]`, and the maximum-likelihood adversary.
  set μ : Measure α := twoPoint m₀ m₁
  set f : α → Fin 2 := fun x ↦ if x = m₀ then 0 else 1
  set ρ := Kernel.deterministic f (measurable_of_finite f)
  set d : β → Fin 2 := fun y ↦ if (κ m₁ {y}).toReal ≤ (κ m₀ {y}).toReal then 0 else 1
  set g := Kernel.deterministic d (measurable_of_finite d)
  have hp := toReal_twoPoint_singleton (m₀ := m₀) (m₁ := m₁)
  have hF (x : α) (u : Fin 2) : (ρ x {u}).toReal = if f x = u then 1 else 0 := by
    simp only [ρ, Kernel.deterministic_apply' _ x (measurableSet_singleton u),
      Set.indicator_apply, Set.mem_singleton_iff]
    split_ifs <;> simp
  have hG (y : β) (u : Fin 2) : (g y {u}).toReal = if d y = u then 1 else 0 := by
    simp only [g, Kernel.deterministic_apply' _ y (measurableSet_singleton u),
      Set.indicator_apply, Set.mem_singleton_iff]
    split_ifs <;> simp
  have hguess : (guessProb μ ρ κ g).toReal =
      (1 + tvDistSum (fun y ↦ (κ m₀ {y}).toReal) (fun y ↦ (κ m₁ {y}).toReal)) / 2 := by
    rw [toReal_guessProb]
    exact sum_guess_twoPoint (W := fun x y ↦ (κ x {y}).toReal) hm hp
      (fun x ↦ sum_toReal_singleton (κ x)) hF hG
  have hblind : (blindGuessProb μ ρ).toReal ≤ 1 / 2 := by
    rw [blindGuessProb, ENNReal.toReal_iSup fun u ↦ measure_ne_top _ _]
    refine Real.iSup_le (fun u ↦ ?_) (by norm_num)
    rw [toReal_comp_apply_singleton]
    simp_rw [mul_comm (ρ _ {u}).toReal]
    rw [sum_twoPoint hp, hF, hF]
    fin_cases u <;> simp [f, hm.symm]
  have hmem : (⨆ (g : Kernel β (Fin 2)) (_ : IsMarkovKernel g), guessProb μ ρ κ g).toReal -
      (blindGuessProb μ ρ).toReal ∈ {a | ∃ (n : ℕ) (μ : Measure α) (ρ : Kernel α (Fin n)),
        IsProbabilityMeasure μ ∧ IsMarkovKernel ρ ∧ a = (⨆ (g : Kernel β (Fin n))
          (_ : IsMarkovKernel g), guessProb μ ρ κ g).toReal - (blindGuessProb μ ρ).toReal} :=
    ⟨2, μ, ρ, inferInstance, inferInstance, rfl⟩
  have hle := le_csSup bddAbove_ssAdvantage hmem
  have hg : (guessProb μ ρ κ g).toReal ≤
      (⨆ (g : Kernel β (Fin 2)) (_ : IsMarkovKernel g), guessProb μ ρ κ g).toReal :=
    ENNReal.toReal_mono iSup_guessProb_ne_top
      (le_iSup₂ (f := fun g (_ : IsMarkovKernel g) ↦ guessProb μ ρ κ g) g inferInstance)
  rw [ssAdvantage]
  linarith

end SS

end InformationTheory

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace SemanticSecurity

/-- The Kullback–Leibler divergence of probability measures on a finite space with `P ≪ Q`, as a
finite sum. -/
lemma klDiv_eq_ofReal_sum [Fintype β] [MeasurableSingletonClass β] {P Q : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : ∀ y, Q {y} = 0 → P {y} = 0) :
    klDiv P Q =
      ENNReal.ofReal (∑ y, (P {y}).toReal * log ((P {y}).toReal / (Q {y}).toReal)) := by
  have hac : P ≪ Q := fun s hs ↦ by
    rw [measure_eq_zero_iff_ae_notMem, ae_iff_of_countable] at hs ⊢
    exact fun y hy ↦ hs y fun hQy ↦ hy (h y hQy)
  rw [klDiv_of_ac_of_integrable hac .of_finite, integral_fintype .of_finite]
  simp only [probReal_univ, add_sub_cancel_right]
  congr 1
  refine sum_congr rfl fun y _ ↦ ?_
  rw [smul_eq_mul, llr, measureReal_def]
  by_cases hPy : P {y} = 0
  · simp [hPy]
  have hQy : Q {y} ≠ 0 := fun h0 ↦ hPy (h y h0)
  have hy_eq : P {y} = P.rnDeriv Q y * Q {y} := by
    rw [← Measure.setLIntegral_rnDeriv hac, lintegral_singleton]
  have : P.rnDeriv Q y = P {y} / Q {y} := by
    rw [hy_eq, ENNReal.mul_div_cancel_right hQy (measure_ne_top _ _)]
  rw [this, ENNReal.toReal_div]

/-- **Pinsker's inequality** (Lemma 4.3 of Bellare–Tessaro–Vardy) for probability measures on a
finite space, in nats: `2 SD(P; Q)² ≤ D(P ‖ Q)`. -/
theorem ofReal_two_mul_sq_tvDistSum_le_klDiv [Fintype β] [MeasurableSingletonClass β]
    (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal (2 * tvDistSum (fun y ↦ (P {y}).toReal) (fun y ↦ (Q {y}).toReal) ^ 2) ≤
      klDiv P Q := by
  by_cases h : ∀ y, Q {y} = 0 → P {y} = 0
  · rw [klDiv_eq_ofReal_sum h]
    refine ENNReal.ofReal_le_ofReal (two_mul_sq_tvDistSum_le (fun _ ↦ ENNReal.toReal_nonneg)
      (fun _ ↦ ENNReal.toReal_nonneg) (sum_toReal_singleton P) (sum_toReal_singleton Q)
      fun y hy ↦ ?_)
    rw [ENNReal.toReal_eq_zero_iff] at hy ⊢
    exact Or.inl (h y (hy.resolve_right (measure_ne_top _ _)))
  · push Not at h
    obtain ⟨y, hQ, hP⟩ := h
    rw [klDiv_of_not_ac fun hac ↦ hP (hac hQ)]
    exact le_top

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  {κ : Kernel α β} [IsMarkovKernel κ] {μ : Measure α} [IsProbabilityMeasure μ]

omit [Fintype β] in
/-- The output law of `κ` under `μ`, in real coordinates. -/
lemma toReal_comp_eq_outputLaw (y : β) :
    ((κ ∘ₘ μ) {y}).toReal = outputLaw (fun x ↦ (μ {x}).toReal) (fun x y ↦ (κ x {y}).toReal) y := by
  rw [toReal_comp_apply_singleton, outputLaw]
  exact sum_congr rfl fun x _ ↦ mul_comm _ _

/-- The mutual information `I(M; C)` between `M ∼ μ` and the output `C` of the channel `κ`, as a
finite sum: `I(M; C) = ∑_m P_M(m) ∑_c P_{C|M=m}(c) log (P_{C|M=m}(c) / P_C(c))`. -/
lemma toReal_mutualInfo_eq :
    (mutualInfo (μ ⊗ₘ κ)).toReal = ∑ x, (μ {x}).toReal * ∑ y, (κ x {y}).toReal *
      log ((κ x {y}).toReal /
        outputLaw (fun x ↦ (μ {x}).toReal) (fun x y ↦ (κ x {y}).toReal) y) := by
  set p : α → ℝ := fun x ↦ (μ {x}).toReal
  set W : α → β → ℝ := fun x y ↦ (κ x {y}).toReal
  have hp₀ (x : α) : 0 ≤ p x := ENNReal.toReal_nonneg
  have hW₀ (x : α) (y : β) : 0 ≤ W x y := ENNReal.toReal_nonneg
  -- Each row of a message of positive probability is absolutely continuous w.r.t. the output.
  have hsupp (x : α) (hx : μ {x} ≠ 0) (y : β) : (κ ∘ₘ μ) {y} = 0 → κ x {y} = 0 := by
    intro hy
    rw [comp_apply_singleton] at hy
    have := (Finset.sum_eq_zero_iff.1 hy) x (mem_univ x)
    exact (mul_eq_zero.1 this).resolve_right hx
  have hterm (x : α) : klDiv (κ x) (κ ∘ₘ μ) * μ {x} =
      ENNReal.ofReal (p x * ∑ y, W x y * log (W x y / outputLaw p W y)) := by
    by_cases hx : μ {x} = 0
    · simp [p, hx]
    rw [klDiv_eq_ofReal_sum (hsupp x hx), ENNReal.ofReal_mul (hp₀ x), mul_comm,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp_rw [toReal_comp_eq_outputLaw]
    rfl
  have hnonneg (x : α) : 0 ≤ p x * ∑ y, W x y * log (W x y / outputLaw p W y) := by
    by_cases hx : μ {x} = 0
    · simp [p, hx]
    refine mul_nonneg (hp₀ x) ((by positivity : (0 : ℝ) ≤ 2 * tvDistSum (W x)
      (outputLaw p W) ^ 2).trans (two_mul_sq_tvDistSum_le (hW₀ x) (fun y ↦ ?_)
      (sum_toReal_singleton (κ x)) ?_ fun y hy ↦ ?_))
    · exact sum_nonneg fun x _ ↦ mul_nonneg (hp₀ x) (hW₀ x y)
    · exact sum_outputLaw_eq_one (sum_toReal_singleton μ) fun x ↦ sum_toReal_singleton (κ x)
    · rw [← toReal_comp_eq_outputLaw, ENNReal.toReal_eq_zero_iff] at hy
      simp [W, hsupp x hx y (hy.resolve_right (measure_ne_top _ _))]
  rw [mutualInfo_compProd_eq_lintegral, lintegral_fintype, sum_congr rfl fun x _ ↦ hterm x,
    ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hnonneg x,
    ENNReal.toReal_ofReal (sum_nonneg fun x _ ↦ hnonneg x)]

end SemanticSecurity

end InformationTheory

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

open SemanticSecurity

/-- `ε log (n / ε) ≥ 0` for `ε ∈ [0, 1]` and `n : ℕ`. -/
lemma SemanticSecurity.mul_log_card_div_nonneg {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (n : ℕ) :
    0 ≤ ε * log (n / ε) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases hε₀.eq_or_lt with rfl | hε
  · simp
  rw [log_div (by positivity) hε.ne']
  nlinarith [log_nonpos hε₀ hε₁, Real.log_natCast_nonneg n]

/-- `ε log (n / ε) ≤ ε log n + h(ε)` for `ε ∈ [0, 1]` and `n : ℕ` (with equality if `n ≠ 0`). -/
lemma SemanticSecurity.mul_log_card_div_le {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (n : ℕ) :
    ε * log (n / ε) ≤ ε * log n + negMulLog ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using negMulLog_nonneg hε₀ hε₁
  rcases hε₀.eq_or_lt with rfl | hε
  · simp
  rw [log_div (by positivity) hε.ne', negMulLog]
  ring_nf
  rfl

/-- `Adv^ds log 2 ≤ Adv^ds log |β|`: either `|β| ≥ 2`, or `β` has at most one point and every two
rows of `κ` coincide, so that `Adv^ds = 0`. -/
lemma SemanticSecurity.dsAdvantage_mul_log_two_le [Fintype β] [MeasurableSingletonClass β]
    {κ : Kernel α β} [IsMarkovKernel κ] :
    dsAdvantage κ * log 2 ≤ dsAdvantage κ * log (Fintype.card β) := by
  rcases le_or_gt 2 (Fintype.card β) with h | h
  · exact mul_le_mul_of_nonneg_left (log_le_log two_pos (by exact_mod_cast h)) dsAdvantage_nonneg
  have : Subsingleton β := Fintype.card_le_one_iff_subsingleton.1 (by omega)
  have hrow (m : α) (y : β) : (κ m {y}).toReal = 1 := by
    rw [← sum_toReal_singleton (κ m),
      sum_eq_single y (fun b _ hb ↦ absurd (Subsingleton.elim b y) hb) (by simp)]
  have h0 : dsAdvantage κ = 0 := le_antisymm
    (Real.iSup_le (fun m₀ ↦ Real.iSup_le (fun m₁ ↦ by simp [tvDistSum, hrow]) le_rfl) le_rfl)
    dsAdvantage_nonneg
  simp [h0]

section MIS

variable [Finite α] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {κ : Kernel α β} [IsMarkovKernel κ]

omit [MeasurableSingletonClass α] in
/-- The Shannon capacity of a channel with a finite output alphabet is finite. -/
lemma SemanticSecurity.shannonCapacity_ne_top [Finite β] : shannonCapacity κ ≠ ∞ := by
  have := Fintype.ofFinite β
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top shannonCapacity_le

omit [MeasurableSingletonClass α] in
/-- `I(M; C) ≤ Adv^mis` for every prior. -/
lemma SemanticSecurity.toReal_mutualInfo_le_toReal_shannonCapacity [Finite β] {μ : Measure α}
    [IsProbabilityMeasure μ] :
    (mutualInfo (μ ⊗ₘ κ)).toReal ≤ (shannonCapacity κ).toReal :=
  ENNReal.toReal_mono shannonCapacity_ne_top
    (le_iSup₂ (f := fun (μ : Measure α) (_ : IsProbabilityMeasure μ) ↦ mutualInfo (μ ⊗ₘ κ)) μ
      inferInstance)

/-- **Theorem 4.5 of Bellare–Tessaro–Vardy** (MIS → DS): `Adv^ds ≤ √(2 Adv^mis)`, where
`Adv^mis = max_M I(M; C)` is the Shannon capacity of `κ`, in nats (finite by
`SemanticSecurity.shannonCapacity_ne_top`, so `toReal` loses nothing). In nats this is slightly
stronger than the paper's statement in bits. -/
theorem dsAdvantage_le_sqrt_two_mul_shannonCapacity [Fintype β] :
    dsAdvantage κ ≤ √(2 * (shannonCapacity κ).toReal) := by
  classical
  have := Fintype.ofFinite α
  refine Real.iSup_le (fun m₀ ↦ Real.iSup_le (fun m₁ ↦ ?_) (sqrt_nonneg _)) (sqrt_nonneg _)
  have hI := sq_tvDistSum_div_two_le (W := fun x y ↦ (κ x {y}).toReal)
    (toReal_twoPoint_singleton (m₀ := m₀) (m₁ := m₁)) (fun _ _ ↦ ENNReal.toReal_nonneg)
    fun x ↦ sum_toReal_singleton (κ x)
  rw [← toReal_mutualInfo_eq] at hI
  have hcap := toReal_mutualInfo_le_toReal_shannonCapacity (κ := κ) (μ := twoPoint m₀ m₁)
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

/-- **Theorem 4.9 of Bellare–Tessaro–Vardy** (DS → MIS), in nats: with `ε = Adv^ds`,
`Adv^mis ≤ 2 ε log (|C| / ε)`, where `C = β` is the alphabet of adversary ciphertexts. The paper
writes `2^c` (the sender-ciphertext alphabet) in place of `|C| = 2^d`; its proof gives `|C|`, which
is what we prove (see the notes in the module docstring). For `ε = 0` both sides vanish. -/
theorem shannonCapacity_le_dsAdvantage [Fintype β] :
    shannonCapacity κ ≤ ENNReal.ofReal
      (2 * dsAdvantage κ * log (Fintype.card β / dsAdvantage κ)) := by
  have := Fintype.ofFinite α
  refine iSup₂_le fun μ hμ ↦ ?_
  rw [← ENNReal.ofReal_toReal mutualInfo_compProd_ne_top, toReal_mutualInfo_eq]
  exact ENNReal.ofReal_le_ofReal <| sum_mul_sum_mul_log_le (fun _ ↦ ENNReal.toReal_nonneg)
    (sum_toReal_singleton μ) (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun x ↦ sum_toReal_singleton (κ x)) tvDistSum_le_dsAdvantage dsAdvantage_le_one

/-- **Theorem 4.9 of Bellare–Tessaro–Vardy**, real-valued form. -/
theorem toReal_shannonCapacity_le_dsAdvantage [Fintype β] :
    (shannonCapacity κ).toReal ≤ 2 * dsAdvantage κ * log (Fintype.card β / dsAdvantage κ) := by
  refine ENNReal.toReal_le_of_le_ofReal ?_ shannonCapacity_le_dsAdvantage
  rw [mul_assoc]
  exact mul_nonneg zero_le_two
    (mul_log_card_div_nonneg dsAdvantage_nonneg dsAdvantage_le_one (Fintype.card β))

end MIS

/-! ### Asymptotic equivalences -/

section Asymptotic

open Filter Topology

variable {α β : ℕ → Type*} [∀ k, MeasurableSpace (α k)] [∀ k, MeasurableSpace (β k)]
  [∀ k, Finite (α k)] [∀ k, MeasurableSingletonClass (α k)] [∀ k, Fintype (β k)]
  [∀ k, MeasurableSingletonClass (β k)] (κ : ∀ k, Kernel (α k) (β k))
  [∀ k, IsMarkovKernel (κ k)]

/-- **Corollary of Theorem 4.1 of Bellare–Tessaro–Vardy**: a family of channels is SS-secure
(`Adv^ss → 0`) if and only if it is DS-secure (`Adv^ds → 0`). -/
theorem tendsto_ssAdvantage_iff_tendsto_dsAdvantage :
    Tendsto (fun k ↦ ssAdvantage (κ k)) atTop (𝓝 0) ↔
      Tendsto (fun k ↦ dsAdvantage (κ k)) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h2 := h.const_mul 2
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ ↦ dsAdvantage_nonneg) fun _ ↦ dsAdvantage_le_two_mul_ssAdvantage
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ ↦ ssAdvantage_nonneg) fun _ ↦ ssAdvantage_le_dsAdvantage

/-- **Corollary of Theorem 4.5 of Bellare–Tessaro–Vardy**: a family of channels that is MIS-secure
(`Adv^mis → 0`) is DS-secure. -/
theorem tendsto_dsAdvantage_of_tendsto_shannonCapacity
    (h : Tendsto (fun k ↦ (shannonCapacity (κ k)).toReal) atTop (𝓝 0)) :
    Tendsto (fun k ↦ dsAdvantage (κ k)) atTop (𝓝 0) := by
  have h' : Tendsto (fun k ↦ √(2 * (shannonCapacity (κ k)).toReal)) atTop (𝓝 0) := by
    simpa using (h.const_mul 2).sqrt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h'
    (fun _ ↦ dsAdvantage_nonneg) fun _ ↦ dsAdvantage_le_sqrt_two_mul_shannonCapacity

omit [∀ k, Fintype (β k)] in
/-- **Corollary of Theorems 4.1 and 4.5 of Bellare–Tessaro–Vardy**: a family of channels that is
MIS-secure is semantically secure. -/
theorem tendsto_ssAdvantage_of_tendsto_shannonCapacity [∀ k, Finite (β k)]
    (h : Tendsto (fun k ↦ (shannonCapacity (κ k)).toReal) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ssAdvantage (κ k)) atTop (𝓝 0) := by
  have : ∀ k, Fintype (β k) := fun k ↦ Fintype.ofFinite (β k)
  exact (tendsto_ssAdvantage_iff_tendsto_dsAdvantage κ).2
    (tendsto_dsAdvantage_of_tendsto_shannonCapacity κ h)

omit [∀ k, Finite (α k)] [∀ k, MeasurableSingletonClass (α k)] in
/-- DS-security at rate `o(1 / log |C_k|)`, i.e. `ε_k log |C_k| → 0` with `ε_k = Adv^ds_k`,
implies `ε_k → 0` (the alphabets with one symbol have `ε_k = 0`). -/
theorem tendsto_dsAdvantage_of_tendsto_mul_log
    (hlog : Tendsto (fun k ↦ dsAdvantage (κ k) * log (Fintype.card (β k))) atTop (𝓝 0)) :
    Tendsto (fun k ↦ dsAdvantage (κ k)) atTop (𝓝 0) := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have hup := hlog.div_const (log 2)
  rw [zero_div] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ ↦ dsAdvantage_nonneg) fun k ↦ ?_
  rw [le_div_iff₀ hl2]
  exact dsAdvantage_mul_log_two_le

/-- **Corollary of Theorem 4.9 of Bellare–Tessaro–Vardy**: a family of channels that is DS-secure
at rate `o(1 / log |C_k|)`, i.e. `Adv^ds_k · log |C_k| → 0` where `C_k` is the adversary alphabet,
is MIS-secure. -/
theorem tendsto_shannonCapacity_of_tendsto_mul_log
    (hlog : Tendsto (fun k ↦ dsAdvantage (κ k) * log (Fintype.card (β k))) atTop (𝓝 0)) :
    Tendsto (fun k ↦ (shannonCapacity (κ k)).toReal) atTop (𝓝 0) := by
  have h := tendsto_dsAdvantage_of_tendsto_mul_log κ hlog
  have hup : Tendsto (fun k ↦ 2 * (dsAdvantage (κ k) * log (Fintype.card (β k))) +
      2 * negMulLog (dsAdvantage (κ k))) atTop (𝓝 0) := by
    simpa using (hlog.const_mul 2).add (((continuous_negMulLog.tendsto 0).comp h).const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ ↦ ENNReal.toReal_nonneg) fun k ↦ ?_
  refine toReal_shannonCapacity_le_dsAdvantage.trans ?_
  rw [mul_assoc, ← mul_add]
  exact mul_le_mul_of_nonneg_left
    (mul_log_card_div_le dsAdvantage_nonneg dsAdvantage_le_one _) zero_le_two

/-- **The "usual" case of the DS → MIS corollary** (Bellare–Tessaro–Vardy, after Theorem 4.9):
if the adversary ciphertexts have polynomial length (`log |C_k| ≤ C k^a`) and the family is
strongly DS-secure in the sense of Section 3.2 (`Adv^ds_k ≤ exp (-d k^e)` with `d, e > 0`), then
the family is MIS-secure (`Adv^mis → 0`). The paper's "(respectively, strongly)" conclusion, strong
MIS-security, is not formalized. -/
theorem tendsto_shannonCapacity_of_le_exp {C a d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hβ : ∀ k, log (Fintype.card (β k)) ≤ C * (k : ℝ) ^ a)
    (hε : ∀ k, dsAdvantage (κ k) ≤ exp (-(d * (k : ℝ) ^ e))) :
    Tendsto (fun k ↦ (shannonCapacity (κ k)).toReal) atTop (𝓝 0) := by
  refine tendsto_shannonCapacity_of_tendsto_mul_log κ ?_
  -- `k^a exp(-d k^e) = t^(a/e) exp(-d t)` with `t = k^e → ∞`.
  have hlim : Tendsto (fun k : ℕ ↦ C * (((k : ℝ) ^ e) ^ (a / e) * exp (-d * (k : ℝ) ^ e)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / e) d hd).comp
      ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop)).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k ↦ mul_nonneg dsAdvantage_nonneg (log_natCast_nonneg _)) fun k ↦ ?_
  have hk : ((k : ℝ) ^ e) ^ (a / e) = (k : ℝ) ^ a := by
    rw [← rpow_mul (Nat.cast_nonneg k), mul_div_cancel₀ _ he.ne']
  rw [hk, neg_mul]
  calc dsAdvantage (κ k) * log (Fintype.card (β k))
      ≤ exp (-(d * (k : ℝ) ^ e)) * log (Fintype.card (β k)) :=
        mul_le_mul_of_nonneg_right (hε k) (log_natCast_nonneg _)
    _ ≤ exp (-(d * (k : ℝ) ^ e)) * (C * (k : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_left (hβ k) (exp_pos _).le
    _ = C * ((k : ℝ) ^ a * exp (-(d * (k : ℝ) ^ e))) := by ring

end Asymptotic

end InformationTheory
