/-
Copyright (c) 2026 Formal6437 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal6437 Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Shannon Information Content and Entropy

This file defines Shannon information content (surprisal / self-information) and
Shannon entropy for finite discrete probability distributions, following
Shannon's 1948 paper "A Mathematical Theory of Communication" and the MIT 6.437
course "Inference and Information."

## Main definitions

* `ShannonEntropy.infoContent` — information content (surprisal): `h(p) = -log(p)` (nats)
* `ShannonEntropy.entropy` — Shannon entropy: `H(p) = ∑ₐ p(a) · (-log(p(a)))` (nats)

## Main results

* `ShannonEntropy.infoContent_one` — certain events carry zero information
* `ShannonEntropy.infoContent_nonneg` — information content is nonnegative for p ∈ (0, 1]
* `ShannonEntropy.infoContent_mul` — additivity for independent events: h(pq) = h(p) + h(q)
* `ShannonEntropy.infoContent_anti` — higher probability implies lower information content
* `ShannonEntropy.entropy_nonneg` — Shannon entropy is nonnegative

## Conventions

* The natural logarithm (`Real.log`) is used throughout; units are **nats**.
  To convert to **bits**, divide by `Real.log 2`.
* We follow the standard convention `0 · log 0 = 0`, which is consistent with
  `lim_{p→0⁺} p log p = 0` and with Mathlib's `Real.log 0 = 0`.
* Entropy is expressed as `∑ p(a) · negMulLog(p(a))` using Mathlib's `Real.negMulLog`,
  where `negMulLog x = -x * log x`.

## References

* [C. E. Shannon, *A Mathematical Theory of Communication*, 1948]
* [D. J. C. MacKay, *Information Theory, Inference, and Learning Algorithms*, 2003]
* MIT 6.437 "Inference and Information," Spring 2015
-/

open scoped BigOperators
open Real

namespace ShannonEntropy

/-! ### Information Content (Surprisal / Self-Information)

The information content of an outcome with probability `p` measures the "surprise"
upon observing that outcome. Unlikely events carry more information than likely ones.
-/

/-- Information content (surprisal) of an outcome with probability `p`, in nats.
`infoContent p = -log(p)`. Also written `h(x) = -log p(x)` or `log(1/p(x))`. -/
noncomputable def infoContent (p : ℝ) : ℝ := -Real.log p

/-! ### Basic properties of information content -/

/-- A certain event (`p = 1`) carries zero information: `h(1) = 0`. -/
@[simp]
theorem infoContent_one : infoContent 1 = 0 := by
  simp [infoContent]

/-- An impossible event (`p = 0`) has information content zero by convention
(since `Real.log 0 = 0` in Mathlib). This is consistent with the `0 log 0 = 0`
convention used throughout information theory. -/
@[simp]
theorem infoContent_zero : infoContent 0 = 0 := by
  simp [infoContent]

/-- Information content is nonnegative for probabilities `p ∈ (0, 1]`:
since `log p ≤ 0` for `p ∈ (0, 1]`, we have `-log p ≥ 0`. -/
theorem infoContent_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ infoContent p := by
  unfold infoContent
  linarith [Real.log_nonpos hp.le hp1]

/-- Additivity of information content for independent events:
`h(p · q) = h(p) + h(q)`.
This corresponds to the independence property: if `X ⊥ Y`, then
`h(x, y) = h(x) + h(y)` since `p(x, y) = p(x) · p(y)`. -/
theorem infoContent_mul {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    infoContent (p * q) = infoContent p + infoContent q := by
  unfold infoContent
  rw [Real.log_mul hp hq]
  ring

/-- Monotonicity (anti-tonicity): higher probability implies lower information content.
If `0 < p ≤ q`, then `h(q) ≤ h(p)`, i.e., more likely events are less surprising. -/
theorem infoContent_anti {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    infoContent q ≤ infoContent p := by
  unfold infoContent
  linarith [Real.log_le_log hp hpq]

/-- Information content equals `log(1/p)`:
`h(p) = -log(p) = log(p⁻¹)`. -/
theorem infoContent_eq_log_inv (p : ℝ) :
    infoContent p = Real.log p⁻¹ := by
  unfold infoContent
  rw [Real.log_inv]

/-- The relationship between information content and `negMulLog`:
`p * h(p) = negMulLog p`. This is the key identity connecting surprisal to entropy. -/
theorem mul_infoContent_eq_negMulLog (p : ℝ) :
    p * infoContent p = negMulLog p := by
  unfold infoContent negMulLog
  ring

/-! ### Shannon Entropy

The Shannon entropy `H(X)` is the expected information content — the average
amount of information (in nats) needed to encode/transmit the state of a random
variable. If there is nonuniformity in the distribution, we can encode more
efficiently (using fewer bits on average).
-/

variable {α : Type*}

/-- Shannon entropy of a finite probability distribution `p : α → ℝ`, in nats.
`H(p) = ∑ₐ p(a) · h(p(a)) = ∑ₐ negMulLog(p(a))`.
This is the average amount of information (surprise) when observing outcomes
distributed according to `p`. -/
noncomputable def entropy [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a : α, negMulLog (p a)

/-- Shannon entropy in bits (base-2 logarithm). -/
noncomputable def entropyBits [Fintype α] (p : α → ℝ) : ℝ :=
  entropy p / Real.log 2

/-- Entropy equals the sum of `p(a) * infoContent(p(a))` over all outcomes. -/
theorem entropy_eq_sum_mul_infoContent [Fintype α] (p : α → ℝ) :
    entropy p = ∑ a : α, p a * infoContent (p a) := by
  simp only [entropy, ← mul_infoContent_eq_negMulLog]

/-- Shannon entropy is nonnegative for valid probability distributions
(where each probability is in `[0, 1]`). -/
theorem entropy_nonneg [Fintype α] {p : α → ℝ}
    (hp : ∀ (a : α), 0 ≤ p a) (hp1 : ∀ (a : α), p a ≤ 1) :
    0 ≤ entropy p := by
  unfold entropy
  apply Finset.sum_nonneg
  intro a _
  exact negMulLog_nonneg (hp a) (hp1 a)

/-- Entropy of a deterministic distribution (one outcome has probability 1,
rest have probability 0) is zero. This is expressed as: if some outcome `a₀`
has `p(a₀) = 1` and all others have `p(a) = 0`, then `H(p) = 0`. -/
theorem entropy_eq_zero_of_deterministic [Fintype α] {p : α → ℝ}
    {a₀ : α} (ha₀ : p a₀ = 1) (hrest : ∀ (a : α), a ≠ a₀ → p a = 0) :
    entropy p = 0 := by
  unfold entropy
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a = a₀
  · rw [ha, ha₀, negMulLog_one]
  · rw [hrest a ha, negMulLog_zero]

end ShannonEntropy
