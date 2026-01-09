# How to Use Aristotle (Harmonic)

AI theorem prover for Lean 4 by [Harmonic](https://harmonic.fun).

---

## Setup

### 1. Set API Key

Get your key at: https://aristotle.harmonic.fun

Add to `~/.zshrc` (Mac) or `~/.bashrc` (Linux):
```bash
export ARISTOTLE_API_KEY='arstl_{YOUR_API_KEY}'
```

### 2. Run Aristotle

```bash
uvx --from aristotlelib@latest aristotle
```

> ⚠️ The docs say `uvx aristotlelib@latest aristotle` — this is wrong. Use `--from`.

---

## Modes

| Mode | Description |
|------|-------------|
| [1] Fill sorries | Auto-prove `sorry` in `.lean` files |
| [2] Formalize | Convert `.txt` math to Lean |
| [3] Direct | Chat in English |
| [4] History | View past sessions |

---

## Version Info

Aristotle uses **Lean 4.24.0** / **Mathlib v4.24.0**.

---

## References

- [Official Docs](https://aristotle.harmonic.fun/dashboard/docs/installation)
