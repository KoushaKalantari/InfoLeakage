# InfoLeakage

Machine-checked mathematics of privacy and information leakage in Lean 4: perfect secrecy,
min-entropy and g-leakage, maximal leakage, Sibson/Arimoto α-mutual information, α-leakage,
f-differential privacy and local differential privacy. Built on
[Statlib](https://github.com/stat-lib/statlib) and [Mathlib](https://github.com/leanprover-community/mathlib4).
See [ROADMAP.md](ROADMAP.md).

> **Early-stage work.** Definitions and generality may change after discussion with the
> Statlib community. The code was written with AI assistance (Claude Code), and the author is
> reviewing it line by line.

## Build

```sh
lake exe cache get   # prebuilt Mathlib
lake build
```

Toolchain: `leanprover/lean4:v4.36.0-rc2` (pinned to match Statlib).

## Status

Main results of thirteen papers are formalized for finite alphabets. About 11,000 lines; no
`sorry`. All 919 declarations use only Lean's standard axioms. The library passes the Mathlib
linters and `lake lint`. Each paper's statements were adversarially reviewed against the paper
by a second AI reviewer, and every fix raised was applied: OpenAI Codex for the six leakage
papers, and an independent Claude referee for the landmark papers (Codex review of those is
pending). Module docstrings map each paper result to its Lean name and say exactly what is and
isn't formalized.

### Landmark papers

| Paper | Directory | Formalized |
|---|---|---|
| Shannon, *Communication theory of secrecy systems*, Bell Syst. Tech. J. 1949 | `PerfectSecrecy/` | Perfect secrecy, Thm. 6, key-count bound, Latin-square characterization, Vernam; perfect secrecy ⇔ zero maximal leakage ⇔ zero MI |
| Smith, *On the foundations of quantitative information flow*, FoSSaCS 2009 | `QIF/MinEntropy.lean` | Defs. 1–4, Thms. 1–2, election example |
| Braun, Chatzikokolakis, Palamidessi, *Quantitative notions of leakage for one-try attacks*, MFPS 2009 | `QIF/MinEntropy.lean` | Defs. 4.1–4.4, Prop. 5.1 (min-capacity = maximal leakage), Prop. 6.4, Cor. 6.5, Prop. 7.1 |
| Alvim, Chatzikokolakis, Palamidessi, Smith, *Measuring information leakage using generalized gain functions*, CSF 2012 | `QIF/GainFunctions.lean` | Prop. 3.1, Thms. 4.1–4.2, Miracle theorem, Cor. 5.2, Thms. 5.3, 6.2 |
| Alvim, Chatzikokolakis, McIver, Morgan, Palamidessi, Smith, *Additive and multiplicative notions of leakage, and their capacities*, CSF 2014 | `QIF/GainFunctions.lean` | Thm. 10, §VI-C, Thm. 17 (closed form), Lemmas 19–20, Thm. 21, Cors. 22–23 |
| Duchi, Jordan, Wainwright, *Local privacy, data processing inequalities, and minimax rates* ([arXiv:1302.3203](https://arxiv.org/abs/1302.3203)) | `LocalPrivacy/` | Thm. 1, Lemmas 3–4, Cor. 1, eq. (14), Thm. 2, MI step of Cor. 3 |
| Dong, Roth, Su, *Gaussian differential privacy* ([arXiv:1905.02383](https://arxiv.org/abs/1905.02383)) | `FDP/` | Trade-off functions, f-DP, Prop. 2.2 (necessity), post-processing, Prop. 2.5 ((ε,δ)-DP ⇔ f-DP), Props. 2.4, 2.11, 2.12 (⇒), group privacy (Thm. 2.14, f-part) |

### Leakage measures

| Paper | Directory | Formalized |
|---|---|---|
| Issa, Wagner, Kamath, *An operational approach to information leakage* ([arXiv:1807.07878](https://arxiv.org/abs/1807.07878)) | `MaximalLeakage/` | Def. 1 + Thm. 1 (supremum attained), Lemma 1, Cor. 1, Lemma 2, Lemma 6 |
| Liao, Kosut, Sankar, Calmon, *Tunable measures for information leakage and applications to privacy-utility tradeoffs* ([arXiv:1809.09231](https://arxiv.org/abs/1809.09231)) | `AlphaLeakage/` | Thm. 1 (α-leakage = Arimoto MI), Thm. 2 (maximal α-leakage = Sibson/Arimoto capacity), Thm. 3, eq. (44), Thm. 4 (lower bound), α → ∞ limit |
| Kurri, Kosut, Sankar, *A variational formula for infinity-Rényi divergence with applications to information leakage* ([arXiv:2202.06040](https://arxiv.org/abs/2202.06040)) | `RenyiInfinity/` | Thm. 1, Cor. 1, Prop. 1 (10), Thms. 2–3 |
| Kurri, Sankar, Kosut, *An operational approach to information leakage via generalized gain functions* ([arXiv:2209.13862](https://arxiv.org/abs/2209.13862)) | `GainLeakage/` | Prop. 1, Thm. 1, Thm. 6, Cors. 4–5 (extended to `k` guesses) |
| Gilani, Kurri, Kosut, Sankar, *Unifying privacy measures via maximal (α,β)-leakage* ([arXiv:2304.07456](https://arxiv.org/abs/2304.07456)) | `AlphaBetaLeakage/` | Thm. 2 (1)–(4), Prop. 1 (1)–(3), limits to maximal leakage and local DP |
| Kalantari, Sankar, Sarwate, *Robust privacy-utility tradeoffs under differential privacy and Hamming distortion* ([arXiv:1601.06426](https://arxiv.org/abs/1601.06426)) | `DPHamming/` | Thm. 1, Thm. 2 (cases), Lemmas 1–4, 7, 8, 10; DP ⇒ maximal-leakage and MI bounds |

### What the formalization found

No formalized main statement turned out to be false. Formalizing did surface these issues in the
papers' text, each confirmed in Lean and by an independent reviewer; details are in the module
docstrings.

- **Duchi–Jordan–Wainwright**, Cor. 1 (arXiv v4, §7.2): the proof bounds only one direction of
  the KL divergence, so adding both gives 2·min{4, e^{2α}} rather than 4. The stated bound (13)
  is still true; Lean proves it with constant 2. Separately, the constants in Thm. 1 and Lemma 3
  can be replaced by 1, and Thm. 2's divided by 4; both follow in one line from the paper's own
  steps.
- **Dong–Roth–Su**, proof of Prop. 2.2 (App. A): two typos in the convexity step.
- **Shannon**, p. 681: the example prints P_E(M) = 1/n where P_M(E) = 1/n is meant; the
  key-count argument uses an implicit hypothesis (the fixed key has positive probability).
- **Braun–Chatzikokolakis–Palamidessi**, Fig. 6 caption: 1/(2^k−2) = 1/2^(k−1) holds only
  for k = 2; the computation uses the correct value.
- **Alvim et al., CSF 2014**: the proof of Thm. 17 prints the gain with "+" where "−" is
  needed (App. C is correct), and Cor. 23 writes S where T is meant.

## License

Apache 2.0.
