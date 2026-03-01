# Formal6437

Lean 4 project formalizing MIT's 6.437 "Inference and Information" course using Mathlib 4.

## Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version pinned in `lean-toolchain`)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (bundled with Lean 4)

## Mathlib Setup

This project depends on [Mathlib 4](https://github.com/leanprover-community/mathlib4) (version pinned in `lakefile.toml`). Mathlib is managed automatically by Lake as a dependency — you do **not** need to clone or install it separately.

### First-time setup

```bash
cd Formal6437

# Fetch Mathlib precompiled cache (avoids rebuilding Mathlib from source, which takes hours)
lake exe cache get

# Build the project
lake build
```

### Updating Mathlib

```bash
cd Formal6437
lake update          # Updates dependencies to latest compatible versions
lake exe cache get   # Fetch new precompiled cache
lake build           # Rebuild
```

### Sharing Mathlib across projects

Lake stores dependencies in `.lake/packages/` within each project. Lean projects on the same machine do **not** share Mathlib installations — each project gets its own copy. The `lake exe cache get` command downloads precompiled `.olean` files so you don't have to rebuild Mathlib from source each time. This is the recommended workflow.

## Build Commands

All `lake` commands must be run from this directory (`Formal6437/`):

```bash
lake build                                       # Build entire project
lake build Formal6437.Lecture01.PointwiseRisk     # Build a specific module
lake clean                                        # Clean build artifacts
```

There are no separate test or lint commands. The project "passes" if `lake build` succeeds — verification is done by the Lean 4 kernel itself.

## GitHub Actions configuration

To set up CI, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".
