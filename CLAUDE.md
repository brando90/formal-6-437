# Claude Code: read `~/agents-config/INDEX_RULES.md` for all agent documentation and routing.
# If `~/agents-config/` is not present, clone it: `git clone https://github.com/brando90/agents-config.git ~/agents-config`

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean 4 formalization of MIT's 6.437 "Inference and Information" course. Proves theorems from statistical inference and information theory using Lean 4 + Mathlib 4 (v4.27.0-rc1). The Lean project lives in `Formal6437/`.

## Build Commands

All `lake` commands must be run from the `Formal6437/` directory:

```bash
cd Formal6437

# Download Mathlib precompiled cache (required before first build)
lake exe cache get

# Build entire project
lake build

# Build a specific module
lake build Formal6437.Lecture01.PointwiseRisk

# Update dependencies
lake update

# Clean build artifacts
lake clean
```

There are no separate test or lint commands. **The project "passes" if `lake build` succeeds with no errors** — verification is done by the Lean kernel itself.

## Architecture

- `Formal6437/lakefile.toml` — Lake project config (Lean 4 build system)
- `Formal6437/lean-toolchain` — Lean version pin (v4.27.0-rc1)
- `Formal6437/Formal6437.lean` — Root import file; must list all top-level module imports
- `Formal6437/Formal6437/` — Source modules organized by lecture
  - `Lecture01/` — Hypothesis testing (contains `PointwiseRisk.lean`, the first completed proof)
  - `InformationTheory/` — Placeholder for Shannon information formalizations
- `6_437_S2015/` — Read-only reference PDFs (lectures, problem sets) from the MIT course
- `experiments/` — AI agent prompts and planning notes (not part of the Lean build)

## Lean Conventions

- **`relaxedAutoImplicit = false`**: All implicit arguments must be explicitly declared
- **`weak.linter.mathlibStandardSet = true`**: Mathlib linting rules are enforced
- **No `sorry`**: Shipped theorems must have complete proofs
- **`deriving DecidableEq`** is required on inductive types used in `if/else` branches
- **`noncomputable`** keyword for definitions relying on classical logic
- Import specific Mathlib modules (e.g., `import Mathlib.Data.Real.Basic`) rather than blanket `import Mathlib` when possible
- Each lecture/topic gets its own namespace (e.g., `namespace HypothesisTesting`)
- Files begin with `/-` doc comments describing the lecture/topic, referencing the source PDF

## Adding a New Module

1. Create `.lean` file under the appropriate `Formal6437/Formal6437/LectureXX/` directory
2. Add the import to `Formal6437/Formal6437.lean` (root import file)
3. Run `lake build` from `Formal6437/` to verify

## CI

GitHub Actions workflows in `Formal6437/.github/workflows/`:
- `lean_action_ci.yml` — Builds project and generates docs on push/PR
- `update.yml` — Manual trigger to check for Mathlib version updates
- `create-release.yml` — Auto-creates release tags when `lean-toolchain` changes
