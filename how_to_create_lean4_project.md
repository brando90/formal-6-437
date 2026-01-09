# How to Create a Lean 4 Project with Mathlib

Quick guide for setting up a Lean 4 project with Mathlib as a dependency.

---

## Prerequisites

Ensure `elan` (Lean version manager) is installed and up-to-date:

```bash
elan --version
# If older than 2.0.0:
elan self update
```

---

## 1. Create Project

```bash
# Create new Lean 4 project with Mathlib
lake +leanprover-community/mathlib4:lean-toolchain new MyProject math
```

This command:
- Uses the Mathlib-compatible Lean toolchain
- Initializes project structure
- Downloads Mathlib cached builds (~7700 files)

---

## 2. Project Structure

```
MyProject/
├── MyProject/
│   └── Basic.lean       # Your Lean files go here
├── MyProject.lean       # Root import file
├── lakefile.toml        # Dependencies & config
├── lean-toolchain       # Lean version
├── lake-manifest.json   # Locked dependency versions
└── .lake/               # Build artifacts (gitignored)
```

---

## 3. Verify Setup

Create a test file `MyProject/Test.lean`:

```lean
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.ProbabilityMassFunction.Basic

#check MeasureTheory.MeasureSpace
#check PMF

example : α → α := by aesop
```

Build:

```bash
cd MyProject
lake build MyProject.Test
```

---

## 4. Adding to Existing Git Repo

If adding to an existing repository:

```bash
cd /path/to/your/repo
lake +leanprover-community/mathlib4:lean-toolchain new LeanSubproject math

# Remove nested git repo (parent repo tracks it)
rm -rf LeanSubproject/.git
```

---

## 5. Recommended `.gitignore`

```gitignore
# Lean 4 / Lake
.lake/
lake-packages/
build/
*.olean
*.ilean
*.trace
*.hash
```

---

## 6. Updating Mathlib

```bash
cd MyProject
lake update
lake exe cache get
```

---

## Common Commands

| Command | Description |
|---------|-------------|
| `lake build` | Build entire project |
| `lake build MyProject.FileName` | Build specific file |
| `lake exe cache get` | Download Mathlib cache |
| `lake update` | Update dependencies |
| `lake clean` | Clean build artifacts |

---

## References

- [Mathlib4 GitHub](https://github.com/leanprover-community/mathlib4)
- [Using Mathlib as a Dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
- [Lean Community Project Guide](https://leanprover-community.github.io/install/project.html)

