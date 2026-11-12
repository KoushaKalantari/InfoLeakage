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

| File | Contents |
|---|---|
| `InfoLeakage/MaximalLeakage/Basic.lean` | Maximal leakage on finite output alphabets: bounds, post-processing data processing |

No `sorry`; only Lean's standard axioms.

## License

Apache 2.0.
