# Contributing Shannon Information Theory to Mathlib or CSLib

## TL;DR

**Mathlib is the right target** for Shannon entropy formalizations. CSLib focuses on algorithms/computation and doesn't cover information theory. Before submitting, coordinate on Zulip with the PFR project team, who have extensive entropy code being ported to Mathlib.

## Where our code would go in Mathlib

Our `ShannonEntropy.lean` would become `Mathlib.InformationTheory.Entropy` (or `.Shannon`), alongside:
- `Mathlib.InformationTheory.Hamming` (Hamming distance — already in Mathlib)
- `Mathlib.InformationTheory.KullbackLeibler` (KL divergence — already in Mathlib)
- `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` (building block we already use)
- `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` (binary entropy — already in Mathlib)

## Critical: The PFR Project

The **Polynomial Freiman-Ruzsa (PFR) conjecture formalization** (led by Terence Tao, Yael Dillies, Bhavik Mehta) developed thousands of lines of Shannon entropy lemmas. Their README states they are porting this to Mathlib.

- Repo: https://github.com/teorth/pfr
- Zulip: https://leanprover.zulipchat.com/#narrow/stream/412902-Polynomial-Freiman-Ruzsa-conjecture

**Before submitting a PR, you must:**
1. Check what the PFR team is currently porting
2. Post in the Zulip stream asking about overlap
3. Identify what gaps remain (their entropy is measure-theoretic; our discrete finite version may complement it)

## Step-by-step contribution process

### 1. Join Zulip
- Create account at https://leanprover.zulipchat.com/
- Set real name as display name, add GitHub username to profile
- Post in `#Is there code for X?` stream to check for existing Shannon entropy work

### 2. Discuss before coding
- Post in `#mathlib4` or `#new members` describing what you want to contribute
- For our case: "We want to add general Shannon entropy for finite discrete distributions, building on `negMulLog`. Is this being covered by the PFR port?"

### 3. Adapt code to Mathlib style
Key differences from our current code:

| Our code | Mathlib convention |
|---|---|
| `namespace ShannonEntropy` | `namespace InformationTheory` |
| `import Mathlib.Analysis...` | Will be local imports within Mathlib |
| Our file path | `Mathlib/InformationTheory/Entropy.lean` |

Additional Mathlib requirements:
- 100-char line limit
- `by` at end of preceding line
- Every declaration needs a `/-- -/` docstring (we already have this)
- File header: copyright, Apache 2.0, `Authors:` line (we already have this)
- Run `lake exe mk_all` to update import lists
- PR title format: `feat(InformationTheory): add Shannon entropy for finite distributions`

### 4. Submit small PRs
Mathlib strongly prefers small PRs. Strategy:
1. **PR 1**: `infoContent` definition + basic lemmas (one, zero, nonneg, mul, anti)
2. **PR 2**: `entropy` definition + nonneg, deterministic = 0
3. **PR 3**: Joint entropy, chain rule
4. **PR 4**: Gibbs' inequality

### 5. Review process
- Post in `#PR reviews` on Zulip after submitting
- Typical timeline: days to weeks
- Reviewers check style, docs, location, proof quality, API design
- Only maintainers can merge (via `ready-to-merge` label + bors bot)

## Mathlib naming conventions

Quick reference (full guide: https://leanprover-community.github.io/contribute/naming.html):
- `snake_case` for theorems/lemmas
- `UpperCamelCase` for types/structures
- Pattern: `conclusion_of_hypothesis1_of_hypothesis2`
- Standard: `pos`, `neg`, `nonpos`, `nonneg`, `le`, `lt`

## What about CSLib?

**CSLib** (https://github.com/leanprover/cslib, https://www.cslib.io/) is for computer science foundations: lambda calculus, Turing machines, algorithms, complexity theory. Its 2026 roadmap does not include information theory.

Shannon entropy would only fit CSLib if framed as algorithmic information theory or coding theory (e.g., Huffman coding with complexity analysis). For pure information theory, **use Mathlib**.

## Related Lean 4 projects

| Project | Focus | URL |
|---|---|---|
| PFR | Shannon entropy inequalities (being ported to Mathlib) | https://github.com/teorth/pfr |
| Lean-QuantumInfo | Quantum information theory | https://github.com/Timeroot/Lean-QuantumInfo |
| lean-stat-learning-theory | Statistical learning theory | https://github.com/YuanheZ/lean-stat-learning-theory |

## Key URLs

- Mathlib contribution guide: https://leanprover-community.github.io/contribute/index.html
- Style guide: https://leanprover-community.github.io/contribute/style.html
- Naming conventions: https://leanprover-community.github.io/contribute/naming.html
- PR conventions: https://leanprover-community.github.io/contribute/commit.html
- CSLib contribution guide: https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Zulip chat: https://leanprover.zulipchat.com/
