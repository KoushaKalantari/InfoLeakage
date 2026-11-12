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

## Current plan

1. Make the repo public, labelled early work.
2. Follow Statlib's process (https://stat-lib.github.io/contribute.html):
   - open a GitHub issue on `stat-lib/statlib` with a short design doc covering the
     mathematics and the planned code;
   - then share it on Zulip.
3. The first contribution goes to **Statlib**. Do a Mathlib PR only if a maintainer points to
   a gap upstream.

Deferred: M3, and any paper commitment.

## Milestones

**M0–M2 — done (2026-11-11).** Maximal leakage on finite alphabets:
- the operational definition and Theorem 1 of Issa–Wagner–Kamath, with the supremum attained;
- data processing in both directions;
- support bounds;
- zero leakage iff independence;
- composition and additivity;
- `I(X;Y) ≤ L(X → Y)`.

See the README table. Files: `InfoLeakage/MaximalLeakage/{Basic,Operational,Properties,MutualInfo}.lean`.

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

## Working rules (from the Statlib and Mathlib contribution guides)

- Statlib welcomes AI-assisted ("agentic") code as long as its use is disclosed. Every PR
  carries the author's declaration:
  - they have read and understood every line;
  - they take responsibility for it;
  - they can answer reviewer questions without re-running the AI tool.
- A PR description needs a rationale paragraph written by a human.
- Mathlib summarily closes low-quality LLM-produced PRs and requires disclosing AI use in
  the PR description.
- Comments on GitHub and Zulip must be in your own words: no LLM-written posts.
- Discuss design in the Lean Zulip `#Statlib` channel before large choices or PRs. Rémy
  Degenne coordinates information theory there.
- Follow Mathlib conventions: `module` files, kernels as channels, values in `ℝ≥0∞` where
  natural, nats, Mathlib linters on.
