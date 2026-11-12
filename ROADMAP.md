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

1. ~~Make the repo public, labelled early work.~~ Done.
2. Statlib's process (https://stat-lib.github.io/contribute.html): design issue
   [stat-lib/statlib#78](https://github.com/stat-lib/statlib/issues/78), PR
   [stat-lib/statlib#79](https://github.com/stat-lib/statlib/pull/79) (maximal leakage) and a
   Zulip post in #Statlib, all 2026-11-12. Next: respond to maintainer review.
3. The first contribution goes to **Statlib**. Do a Mathlib PR only if a maintainer points to
   a gap upstream.

Deferred: M3, and any paper commitment.

## Milestones

**Done (2026-11-11).** The six leakage papers in the README are formalized and verified: maximal
leakage, α-leakage, the ∞-Rényi variational formula, gain-function leakage, maximal
(α,β)-leakage, and DP under Hamming distortion.

**Done (2026-11-12).** Landmark papers machine-proofread: Shannon (1949), Smith (2009),
Braun–Chatzikokolakis–Palamidessi (2009), Alvim et al. (CSF 2012, CSF 2014),
Duchi–Jordan–Wainwright, and Dong–Roth–Su. Findings are listed in the README. Codex fidelity
review of these is still to run.

**Next.** Fill gaps in the six papers:
- α-leakage: monotonicity in α, quasi-convexity, Thms. 5–6.
- MαbeL: the conditional and vector versions.
- Gain functions: the α-loss section.
- DP–Hamming: the LP case of Thm. 2(b), and Thm. 3.

Also connect the closed forms to Statlib's `renyiDiv`, and extend beyond finite alphabets.

**M4 — bridges.** g-leakage and the miracle bound, local DP, and maximal (α, β)-leakage are
done. Remaining: Pinsker's inequality (to close Duchi–Jordan–Wainwright Cor. 3), Gaussian DP,
and f-DP composition.

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
