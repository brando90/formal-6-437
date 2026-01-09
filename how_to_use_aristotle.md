# How to Use Aristotle (Harmonic)

Aristotle is an AI-powered theorem prover for Lean 4 by [Harmonic](https://harmonic.fun).

---

## Installation

### 1. Install UV (recommended)

```bash
# macOS/Linux
curl -LsSf https://astral.sh/uv/install.sh | sh

# or with Homebrew
brew install uv
```

### 2. Set Your API Key

Get your free API key at: https://aristotle.harmonic.fun

**Mac** — add to `~/.zshrc`:
```bash
export ARISTOTLE_API_KEY='arstl_{YOUR_API_KEY}'
```

**Linux** — add to `~/.bashrc`:
```bash
export ARISTOTLE_API_KEY='arstl_{YOUR_API_KEY}'
```

Then reload:
```bash
source ~/.zshrc  # or ~/.bashrc
```

### 3. Start Aristotle

> ⚠️ **Note**: The official docs say `uvx aristotlelib@latest aristotle` but this is incorrect.

**Use this command instead:**
```bash
uvx --from aristotlelib@latest aristotle
```

---

## Available Modes

```
╭─ Available Modes ─────────────────────────────────────╮
│                                                       │
│  [1] Fill sorries in a lean file (.lean)              │
│  [2] Prove and formalize from an existing file (.txt) │
│  [3] Direct Aristotle in English (.lean optional)     │
│  [4] View history                                     │
│                                                       │
╰───────────────────────────────────────────────────────╯
```

### Mode 1: Fill Sorries
Automatically proves `sorry` placeholders in your Lean files.

### Mode 2: Prove and Formalize
Converts informal math (from `.txt` files) into formal Lean proofs.

### Mode 3: Direct Aristotle
Chat with Aristotle in natural language to generate Lean code.

### Mode 4: View History
Browse your previous Aristotle sessions.

---

## Version Compatibility

Aristotle runs on fixed versions:

| Component | Version |
|-----------|---------|
| Lean | `leanprover/lean4:v4.24.0` |
| Mathlib | `v4.24.0` (Oct 14, 2025) |

If your project uses different versions, you may experience degraded performance.

---

## Quick Commands

```bash
# Check if API key is set
echo $ARISTOTLE_API_KEY

# Start Aristotle
uvx --from aristotlelib@latest aristotle

# Alternative: install with pip
pip install aristotlelib
aristotle
```

---

## References

- [Aristotle Installation Docs](https://aristotle.harmonic.fun/dashboard/docs/installation)
- [Harmonic Website](https://harmonic.fun)

