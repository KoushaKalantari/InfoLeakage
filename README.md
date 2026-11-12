# InfoLeakage

Machine-checked information-leakage measures in Lean 4: maximal leakage, Sibson/Arimoto
α-mutual information, α-leakage and their guessing interpretations. Built on
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

Main results of six papers on information-theoretic privacy are formalized for finite alphabets.
About 6,300 lines; no `sorry`. All 469 declarations use only Lean's standard axioms. The library
passes the Mathlib linters and `lake lint`. Each statement was adversarially reviewed against its
paper by a second model (OpenAI Codex), and every fix it raised was applied. Module docstrings map
each paper result to its Lean name and say exactly what is and isn't formalized.

| Paper | Directory | Formalized |
|---|---|---|
| Issa, Wagner, Kamath, *An operational approach to information leakage* ([arXiv:1807.07878](https://arxiv.org/abs/1807.07878)) | `MaximalLeakage/` | Def. 1 + Thm. 1 (supremum attained), Lemma 1, Cor. 1, Lemma 2, Lemma 6 |
| Liao, Kosut, Sankar, Calmon, *Tunable measures for information leakage and applications to privacy-utility tradeoffs* ([arXiv:1809.09231](https://arxiv.org/abs/1809.09231)) | `AlphaLeakage/` | Thm. 1 (α-leakage = Arimoto MI), Thm. 2 (maximal α-leakage = Sibson/Arimoto capacity), Thm. 3, eq. (44), Thm. 4 (lower bound), α → ∞ limit |
| Kurri, Kosut, Sankar, *A variational formula for infinity-Rényi divergence with applications to information leakage* ([arXiv:2202.06040](https://arxiv.org/abs/2202.06040)) | `RenyiInfinity/` | Thm. 1, Cor. 1, Prop. 1 (10), Thms. 2–3 |
| Kurri, Sankar, Kosut, *An operational approach to information leakage via generalized gain functions* ([arXiv:2209.13862](https://arxiv.org/abs/2209.13862)) | `GainLeakage/` | Prop. 1, Thm. 1, Thm. 6, Cors. 4–5 (extended to `k` guesses) |
| Gilani, Kurri, Kosut, Sankar, *Unifying privacy measures via maximal (α,β)-leakage* ([arXiv:2304.07456](https://arxiv.org/abs/2304.07456)) | `AlphaBetaLeakage/` | Thm. 2 (1)–(4), Prop. 1 (1)–(3), limits to maximal leakage and local DP |
| Kalantari, Sankar, Sarwate, *Robust privacy-utility tradeoffs under differential privacy and Hamming distortion* ([arXiv:1601.06426](https://arxiv.org/abs/1601.06426)) | `DPHamming/` | Thm. 1, Thm. 2 (cases), Lemmas 1–4, 7, 8, 10; DP ⇒ maximal-leakage and MI bounds |

## License

Apache 2.0.
