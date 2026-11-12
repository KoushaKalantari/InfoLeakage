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

The core results of Issa, Wagner and Kamath, *An operational approach to information leakage*
(IEEE Trans. Inf. Theory 66(3), 2020, [arXiv:1807.07878](https://arxiv.org/abs/1807.07878)) are formalized
for finite alphabets:

| Paper | Lean |
|---|---|
| Def. 1 + Thm. 1 (operational meaning, closed form, attained) | `isGreatest_log_guessRatio`, `opMaxLeakageSum_eq_maxLeakageSum` |
| Lemma 1: data processing, both directions | `maxLeakage_comp_le`, `maxLeakage_comp_le_comp` |
| Lemma 1: bounds by `log \|supp X\|`, `log \|supp Y\|`, nonnegativity | `maxLeakageSum_le_card_support`, `maxLeakage_le_log_card_support_comp`, `maxLeakage_nonneg` |
| Cor. 1(1): zero leakage iff independence | `maxLeakage_eq_zero_iff_compProd_eq_prod` |
| Cor. 1(2): additivity for independent pairs | `maxLeakage_parallelComp` |
| Lemma 6: composition | `maxLeakage_prod_le` |
| Lemma 2: `I(X;Y) ≤ L(X → Y)`, against Statlib's `mutualInfo` | `toReal_mutualInfo_compProd_le_maxLeakage` |

The code has no `sorry`, uses only Lean's standard axioms, and passes the Mathlib linters and
`lake lint`.

## License

Apache 2.0.
