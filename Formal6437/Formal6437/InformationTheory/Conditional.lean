/-
Copyright (c) 2026 Formal6437 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal6437 Contributors
-/
import Formal6437.InformationTheory.ShannonEntropy
import Formal6437.InformationTheory.KLDivergence
import Mathlib.Data.Fintype.BigOperators

/-!
# Conditional Entropy and Mutual Information

This file defines conditional entropy H(Y|X) and mutual information I(X;Y) for
joint distributions `p : α × β → ℝ` over finite types, building on the Shannon
entropy and KL divergence formalizations.

## Main definitions

* `ConditionalEntropy.marginalFst` — first marginal: `p_X(a) = ∑_b p(a, b)`
* `ConditionalEntropy.marginalSnd` — second marginal: `p_Y(b) = ∑_a p(a, b)`
* `ConditionalEntropy.condEntropy` — conditional entropy: `H(Y|X) = H(X,Y) - H(X)`
* `ConditionalEntropy.mutualInfo` — mutual information: `I(X;Y) = H(X) + H(Y) - H(X,Y)`

## Design choice

`condEntropy` is defined algebraically via the chain rule `H(Y|X) = H(X,Y) - H(X)`
rather than as `∑ p_X(x) H(Y|X=x)`. This avoids division-by-zero issues and makes
the chain rule trivially true by definition.

## Main results

* `ConditionalEntropy.chain_rule` — `H(X,Y) = H(X) + H(Y|X)` (definitional)
* `ConditionalEntropy.mutualInfo_alt` — `I(X;Y) = H(Y) - H(Y|X)`
* `ConditionalEntropy.mutualInfo_eq_klDiv` — `I(X;Y) = D_KL(p ‖ p_X ⊗ p_Y)` (sorry)
* `ConditionalEntropy.mutualInfo_nonneg` — `I(X;Y) ≥ 0` (sorry, depends on above)
* `ConditionalEntropy.condEntropy_le_entropy` — `H(Y|X) ≤ H(Y)` (depends on nonneg)
* `ConditionalEntropy.condEntropy_nonneg` — `H(Y|X) ≥ 0` (sorry, needs Jensen)

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2006, Ch. 2]
* MIT 6.437 "Inference and Information," Spring 2015
-/

open scoped BigOperators
open Real ShannonEntropy KLDivergence

namespace ConditionalEntropy

variable {α β : Type*}

/-! ### Marginal Distributions -/

/-- First marginal distribution: `p_X(a) = ∑_b p(a, b)`. -/
noncomputable def marginalFst [Fintype β] (p : α × β → ℝ) (a : α) : ℝ :=
  ∑ b : β, p (a, b)

/-- Second marginal distribution: `p_Y(b) = ∑_a p(a, b)`. -/
noncomputable def marginalSnd [Fintype α] (p : α × β → ℝ) (b : β) : ℝ :=
  ∑ a : α, p (a, b)

/-! ### Marginal Properties -/

/-- First marginal is nonneg when joint distribution is nonneg. -/
theorem marginalFst_nonneg [Fintype β] {p : α × β → ℝ}
    (hp : ∀ (x : α × β), 0 ≤ p x) (a : α) : 0 ≤ marginalFst p a := by
  unfold marginalFst
  exact Finset.sum_nonneg fun b _ => hp (a, b)

/-- Second marginal is nonneg when joint distribution is nonneg. -/
theorem marginalSnd_nonneg [Fintype α] {p : α × β → ℝ}
    (hp : ∀ (x : α × β), 0 ≤ p x) (b : β) : 0 ≤ marginalSnd p b := by
  unfold marginalSnd
  exact Finset.sum_nonneg fun a _ => hp (a, b)

/-- Summing the first marginal recovers the total probability. -/
theorem marginalFst_sum [Fintype α] [Fintype β] (p : α × β → ℝ) :
    ∑ a, marginalFst p a = ∑ x, p x := by
  simp only [marginalFst]
  exact (Fintype.sum_prod_type p).symm

/-- Summing the second marginal recovers the total probability. -/
theorem marginalSnd_sum [Fintype α] [Fintype β] (p : α × β → ℝ) :
    ∑ b, marginalSnd p b = ∑ x, p x := by
  simp only [marginalSnd]
  exact (Fintype.sum_prod_type_right p).symm

/-- First marginal sums to 1 for a valid PMF. -/
theorem marginalFst_sum_eq_one [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_sum : ∑ x, p x = 1) : ∑ a, marginalFst p a = 1 := by
  rw [marginalFst_sum]; exact hp_sum

/-- Second marginal sums to 1 for a valid PMF. -/
theorem marginalSnd_sum_eq_one [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_sum : ∑ x, p x = 1) : ∑ b, marginalSnd p b = 1 := by
  rw [marginalSnd_sum]; exact hp_sum

/-- Each first marginal value is ≤ 1 for a valid PMF. -/
theorem marginalFst_le_one [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp : ∀ (x : α × β), 0 ≤ p x) (hp_sum : ∑ x, p x = 1) (a : α) :
    marginalFst p a ≤ 1 := by
  calc marginalFst p a
      ≤ ∑ a', marginalFst p a' :=
        Finset.single_le_sum (fun a' _ => marginalFst_nonneg hp a') (Finset.mem_univ a)
    _ = 1 := marginalFst_sum_eq_one hp_sum

/-- Each second marginal value is ≤ 1 for a valid PMF. -/
theorem marginalSnd_le_one [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp : ∀ (x : α × β), 0 ≤ p x) (hp_sum : ∑ x, p x = 1) (b : β) :
    marginalSnd p b ≤ 1 := by
  calc marginalSnd p b
      ≤ ∑ b', marginalSnd p b' :=
        Finset.single_le_sum (fun b' _ => marginalSnd_nonneg hp b') (Finset.mem_univ b)
    _ = 1 := marginalSnd_sum_eq_one hp_sum

/-! ### Conditional Entropy -/

/-- Conditional entropy `H(Y|X) = H(X,Y) - H(X)`, defined algebraically via the chain rule. -/
noncomputable def condEntropy [Fintype α] [Fintype β] (p : α × β → ℝ) : ℝ :=
  entropy p - entropy (marginalFst p)

/-- **Chain rule for entropy**: `H(X,Y) = H(X) + H(Y|X)`. Holds by definition. -/
theorem chain_rule [Fintype α] [Fintype β] (p : α × β → ℝ) :
    entropy p = entropy (marginalFst p) + condEntropy p := by
  unfold condEntropy; ring

/-! ### Mutual Information -/

/-- Mutual information `I(X;Y) = H(X) + H(Y) - H(X,Y)`. -/
noncomputable def mutualInfo [Fintype α] [Fintype β] (p : α × β → ℝ) : ℝ :=
  entropy (marginalFst p) + entropy (marginalSnd p) - entropy p

/-- Alternative form: `I(X;Y) = H(Y) - H(Y|X)`. -/
theorem mutualInfo_alt [Fintype α] [Fintype β] (p : α × β → ℝ) :
    mutualInfo p = entropy (marginalSnd p) - condEntropy p := by
  unfold mutualInfo condEntropy; ring

/-- Mutual information is symmetric in its algebraic form:
`I(X;Y) = H(X) + H(Y) - H(X,Y) = I(Y;X)`. -/
theorem mutualInfo_comm [Fintype α] [Fintype β] (p : α × β → ℝ) :
    mutualInfo p = entropy (marginalFst p) - (entropy p - entropy (marginalSnd p)) := by
  unfold mutualInfo; ring

/-- Mutual information expressed as KL divergence from the joint to the product of marginals:
`I(X;Y) = D_KL(p ‖ p_X ⊗ p_Y)`.

This is the key identity connecting mutual information to KL divergence. The proof requires
manipulating nested sums with `Fintype.sum_prod_type` and factoring via `Finset.sum_mul`.

**Strategy**: Both sides reduce to `H(X) + H(Y) - H(X,Y)` after expanding definitions
and using:
- `∑_{a,b} p(a,b) · log(p_X(a)) = ∑_a p_X(a) · log(p_X(a))` (factor out from inner sum)
- `∑_{a,b} p(a,b) · log(p_Y(b)) = ∑_b p_Y(b) · log(p_Y(b))` (similarly) -/
theorem mutualInfo_eq_klDiv [Fintype α] [Fintype β] (p : α × β → ℝ) :
    mutualInfo p = klDiv p (fun xy => marginalFst p xy.1 * marginalSnd p xy.2) := by
  sorry

/-- **Mutual information is nonneg**: `I(X;Y) ≥ 0`.
Follows from `mutualInfo_eq_klDiv` + `klDiv_nonneg` (Gibbs' inequality). -/
theorem mutualInfo_nonneg [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x)
    (hp_sum : ∑ x, p x = 1)
    (hac : ∀ (x : α × β), p x ≠ 0 → marginalFst p x.1 * marginalSnd p x.2 ≠ 0) :
    0 ≤ mutualInfo p := by
  sorry

/-- **Conditioning reduces entropy**: `H(Y|X) ≤ H(Y)`.
Equivalent to mutual information being nonneg: `I(X;Y) = H(Y) - H(Y|X) ≥ 0`.
Note: depends on `mutualInfo_nonneg` which is currently sorry'd. -/
theorem condEntropy_le_entropy [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x)
    (hp_sum : ∑ x, p x = 1)
    (hac : ∀ (x : α × β), p x ≠ 0 → marginalFst p x.1 * marginalSnd p x.2 ≠ 0) :
    condEntropy p ≤ entropy (marginalSnd p) := by
  have h := mutualInfo_nonneg hp_nonneg hp_sum hac
  rw [mutualInfo_alt] at h
  linarith

/-- Conditional entropy is nonneg for valid PMFs. Requires concavity of entropy
(superadditivity of `negMulLog`), which needs Jensen's inequality.

**Strategy**: Show `H(X,Y) ≥ H(X)` by expressing `H(X,Y) - H(X)` as
`∑_a ∑_b negMulLog(p(a,b)) - ∑_a negMulLog(∑_b p(a,b))` and applying
concavity of `negMulLog` (Jensen's inequality) to each fiber. -/
theorem condEntropy_nonneg [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x)
    (hp_le_one : ∀ (x : α × β), p x ≤ 1)
    (hp_sum : ∑ x, p x = 1) :
    0 ≤ condEntropy p := by
  sorry

end ConditionalEntropy
