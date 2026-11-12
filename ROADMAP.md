# InfoLeakage roadmap

Goal: a Lean 4 library of **operational information-leakage measures**, built on
[Statlib](https://github.com/stat-lib/statlib) and Mathlib and written to their standards so
that pieces can be upstreamed.

## Why this lane (landscape as of 2026-11-09)

- Mathlib's `InformationTheory/` has KL divergence (with chain rule and data processing),
  Kraft–McMillan and Hamming distance. Shannon entropy of random variables and mutual
  information are not in Mathlib.
- Textbook Shannon theory is already covered outside Mathlib: Statlib (f-divergences, Rényi,
  mutual information, testing), PFR (entropy), and three single-author, AI-written
  Cover & Thomas libraries (FujiHaruka/information-theory, LeanInfoTheory, infotheorylib).
  Differential privacy is covered by SampCert, cslib-frontier and DPlean4.
- **No proof assistant formalizes** maximal leakage, Sibson/Arimoto α-mutual information,
  α-leakage or maximal α-leakage. g-leakage exists only in HOL4.

Re-check `cslib-community/cslib-frontier` and Statlib before starting each milestone. Both
move fast.

## Current plan: a 4-week pilot (from 2026-11-09)

Set a weekly hours cap and stick to it.
1. Week 1:
   - Read M0 until you could defend every line, then reprove one lemma yourself.
   - Make the repo public, labelled preliminary.
   - Write your own short `#Statlib` post asking about the right generality and what would be
     useful.
2. Aim the first reviewed contribution at **Statlib**. Do a Mathlib PR only if a maintainer
   points to a gap upstream.
3. Week-4 exit criteria:
   - you can explain the contribution and extend it without AI;
   - one narrowly scoped public contribution that builds, has no `sorry`, states its scope
     accurately and discloses AI use;
   - substantive review from a knowledgeable contributor, with the review addressed.

   A merge is a bonus. Continue only if all this fits the hours budget.

Deferred until after the pilot: M3, and any paper commitment.

## Milestones

**M0 — done.** Finite-output maximal leakage as the Issa–Wagner–Kamath closed form
`log ∑_y max_{x ∈ supp} W(y|x)`. Proved: it is nonnegative, at most `log |Y|` and at most
`log |supp X|`, and post-processing the output cannot increase it.
(`InfoLeakage/MaximalLeakage/Basic.lean`)

**M1 — maximal leakage, finite alphabets.**
- `L(X → Y) = 0` iff `X` and `Y` are independent.
- Pre-processing data processing: `L(X → Z) ≤ L(Y → Z)` for `X - Y - Z`.
- `I(X; Y) ≤ L(X → Y)`, against Statlib's `mutualInfo`.
- Composition bounds for several releases.

**M2 — the operational theorem.** Issa–Wagner–Kamath Thm 1: the supremum over guessing
problems `U - X - Y - Û` equals the closed form. This is the headline result.

**M3 — Sibson/Arimoto α-MI and α-leakage**, on Statlib's `renyiDiv`.
- Sibson's `I_α` as `inf_Q D_α(P_XY ‖ P_X ⊗ Q)` and its closed form.
- Monotone in α, with `I_α → L(X → Y)` as `α → ∞`.
- α-leakage and maximal α-leakage (Liao–Kosut–Sankar–Calmon, arXiv:1806.03332):
  maximal α-leakage equals Sibson/Arimoto capacity over inputs with the same support.

**M4 — bridges.**
- g-leakage and the "miracle" bound (Alvim et al.).
- ε-local DP ⇒ leakage bounds.
- Maximal (α, β)-leakage (Kosut).

**M5 — upstream.**
- Generalize the definitions beyond finite alphabets.
- Propose the finished files to Statlib, then the stable core to Mathlib.

## Working rules (from Mathlib's contribution policy)

- Mathlib summarily closes low-quality LLM-produced PRs. Every line must be understood, and
  every design choice defensible, by a human without AI help. Disclose any AI use in the PR
  description.
- Comments on GitHub and Zulip must be in your own words: no LLM-written posts.
- Discuss design in the Lean Zulip `#Statlib` channel before large choices or PRs. Rémy
  Degenne coordinates information theory there.
- Follow Mathlib conventions: `module` files, kernels as channels, values in `ℝ≥0∞` where
  natural, nats, Mathlib linters on.
