# Experiment 01: Shannon Information Content and Entropy

## What was done

Formalized Shannon self-information (surprisal) and Shannon entropy in Lean 4, building on Mathlib's `Real.negMulLog` and `Real.log`.

**File**: `Formal6437/Formal6437/InformationTheory/ShannonEntropy.lean`

### Definitions

| Lean name | Math | Description |
|---|---|---|
| `infoContent p` | h(p) = -log p | Surprisal in nats |
| `entropy p` | H(p) = sum negMulLog(p(a)) | Shannon entropy in nats |
| `entropyBits p` | H(p) / log 2 | Shannon entropy in bits |

### Theorems (all kernel-verified, zero `sorry`)

| Lean name | Statement | Notes from handwritten notes |
|---|---|---|
| `infoContent_one` | h(1) = 0 | "if p(x)=1 => zero info" |
| `infoContent_zero` | h(0) = 0 | Junk value in R; harmless for entropy (0*h(0)=0) |
| `infoContent_nonneg` | 0 < p, p <= 1 => h(p) >= 0 | "info is always positive or zero" |
| `infoContent_mul` | h(p*q) = h(p) + h(q) | "if X perp Y => h(x,y) = h(x) + h(y)" |
| `infoContent_anti` | 0 < p <= q => h(q) <= h(p) | "h(x) is monotonic" (anti-monotone in p) |
| `infoContent_eq_log_inv` | h(p) = log(1/p) | Equivalent form from notes |
| `mul_infoContent_eq_negMulLog` | p * h(p) = negMulLog(p) | Bridge to Mathlib's negMulLog |
| `entropy_nonneg` | H(p) >= 0 for valid dists | Follows from negMulLog_nonneg |
| `entropy_eq_zero_of_deterministic` | p deterministic => H(p) = 0 | Certain RVs have zero entropy |

### Design decisions

- **One Mathlib import** (`NegMulLog`): defines entropy via `negMulLog` to reuse Mathlib's existing lemmas (nonneg, concavity, continuity).
- **Namespace**: `ShannonEntropy` under `InformationTheory/` for future expansion.
- **Units**: nats (natural log), with `entropyBits` for base-2 conversion.
- **No PMF type**: uses `p : alpha -> R` with explicit hypotheses. Simpler and avoids ENNReal conversion complexity.

## Build verification

```
$ cd Formal6437 && lake build
Build completed successfully (2169 jobs).
```

Zero errors, zero warnings, zero `sorry`.

## Not duplicating Mathlib

Checked Mathlib v4.27.0-rc1 thoroughly. Existing information theory content:
- `Real.binEntropy` -- binary entropy only (Bernoulli-specific)
- `Real.qaryEntropy` -- restricted q-ary structure
- `InformationTheory.klDiv` -- measure-theoretic KL divergence
- `Real.negMulLog` -- building block we reuse

**No general Shannon entropy for finite distributions exists in Mathlib.** Our formalization is new.

## Prompt evolution

### Initial prompt (claude_code_prompt.md)
- Included GPT5/GPT5.2 draft Lean code with many issues: wrong API names (`PMF.prod`, `PMF.expect` don't exist), case-split proofs that wouldn't compile, speculative `import Mathlib` blanket imports.
- Key ask: formalize notes from `shannon_info_ver1.jpg` in Lean 4, use Mathlib, make it compile.

### What Claude Code actually did differently
1. **Searched Mathlib** for existing definitions first (GPT drafts didn't).
2. **Used `negMulLog`** from Mathlib instead of reinventing `p * (-log p)`.
3. **Avoided PMF**: GPT drafts used `PMF alpha` with `ENNReal.toReal` conversions that don't compile. We used `p : alpha -> R` which is simpler and correct.
4. **Every proof compiles**: GPT drafts had speculative `simp` calls and `sorry`-level proofs. All 9 theorems here are kernel-verified.
5. **Removed unused import** (`InfiniteSum.Basic`) after review.
6. **Clarified `infoContent_zero` docstring**: GPT drafts conflated the `0 log 0 = 0` entropy convention with the junk value `h(0) = 0`.

## Suggested next steps

### Verification
- [ ] Peer review the Lean file for mathematical accuracy and Mathlib style
- [ ] Check that theorem statements match standard textbook formulations (Shannon 1948, Cover & Thomas ch. 2)
- [ ] Consider adding `#check` / `#eval` examples to the file for quick sanity checks

### Extensions (in priority order)
1. **Joint entropy**: `H(X,Y) = sum negMulLog(p(a,b))` and chain rule `H(X,Y) = H(X) + H(Y|X)`
2. **Conditional entropy**: `H(Y|X) = sum_x p(x) H(Y|X=x)`
3. **Mutual information**: `I(X;Y) = H(X) + H(Y) - H(X,Y)`
4. **KL divergence (discrete)**: complement Mathlib's measure-theoretic `klDiv` with a finite-sum version
5. **Gibbs' inequality / max entropy**: uniform distribution maximizes entropy
6. **Data processing inequality**
7. **Connect to Mathlib's PMF type** for tighter integration

### Mathlib contribution path
- Style is already close to Mathlib (docstrings, simp lemmas, namespacing)
- Would need to follow `Mathlib.InformationTheory` namespace convention
- Could complement `binEntropy` and `klDiv` as a general discrete entropy
