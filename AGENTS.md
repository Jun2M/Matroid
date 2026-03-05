# AGENTS.md

## Project overview

Lean 4 formalization of matroid theory, targeting eventual inclusion in Mathlib4. See `README.md` for the full topic list.

## Cursor Cloud specific instructions

- **Toolchain**: Lean 4 version is pinned in `lean-toolchain`; `elan` (installed at `~/.elan/bin`) reads it automatically.
- **Build**: `lake build` compiles all ~2246 modules. Linters (`linter.style.longLine`, `linter.unusedSimpArgs`) run as part of the build via options in `lakefile.toml`.
- **Mathlib cache**: Always run `lake exe cache get` before building to download pre-compiled Mathlib oleans. Without the cache, building Mathlib from source takes hours.
- **Do NOT run `lake update`** unless intentionally bumping dependency versions — it rewrites `lean-toolchain` and `lake-manifest.json`.
- **No separate lint command**: `lake lint` is not configured. All linting happens during `lake build`.
- **No automated test suite**: Correctness is verified by successful compilation (Lean's type checker is the test). A successful `lake build` with 0 errors means all proofs are valid.
- **Helper scripts** in `scripts/` (Python): `update_matroid_imports.py` regenerates `Matroid.lean` import list; `detect_inefficient_imports.py` finds unnecessary imports.
- **Mathlib lemma search**: Grep `.lake/packages/mathlib/Mathlib` to find relevant Mathlib lemmas.
- **WIP files** in `WIP/` are not imported by the main build and may contain incomplete proofs.
