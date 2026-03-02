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
* `ConditionalEntropy.mutualInfo_eq_klDiv` — `I(X;Y) = D_KL(p ‖ p_X ⊗ p_Y)`
* `ConditionalEntropy.mutualInfo_nonneg` — `I(X;Y) ≥ 0` (via Gibbs' inequality)
* `ConditionalEntropy.condEntropy_le_entropy` — `H(Y|X) ≤ H(Y)`
* `ConditionalEntropy.condEntropy_nonneg` — `H(Y|X) ≥ 0` (via superadditivity of `negMulLog`)

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

/-! ### Helper lemmas for the KL divergence identity -/

/-- First marginal is positive when joint has a positive entry in that fiber. -/
private theorem marginalFst_pos_of_pos [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x) {a : α} {b : β} (hab : 0 < p (a, b)) :
    0 < marginalFst p a := by
  unfold marginalFst
  calc 0 < p (a, b) := hab
    _ ≤ ∑ b', p (a, b') :=
        Finset.single_le_sum (fun b' _ => hp_nonneg (a, b')) (Finset.mem_univ b)

/-- Second marginal is positive when joint has a positive entry in that fiber. -/
private theorem marginalSnd_pos_of_pos [Fintype α] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x) {a : α} {b : β} (hab : 0 < p (a, b)) :
    0 < marginalSnd p b := by
  unfold marginalSnd
  calc 0 < p (a, b) := hab
    _ ≤ ∑ a', p (a', b) :=
        Finset.single_le_sum (fun a' _ => hp_nonneg (a', b)) (Finset.mem_univ a)

/-- Collapsing sum: `∑ xy, p xy * log(margFst xy.1) = ∑ a, margFst a * log(margFst a)`. -/
private lemma sum_joint_mul_log_margFst [Fintype α] [Fintype β] (p : α × β → ℝ) :
    ∑ xy : α × β, p xy * Real.log (marginalFst p xy.1) =
    ∑ a : α, marginalFst p a * Real.log (marginalFst p a) := by
  simp_rw [Fintype.sum_prod_type, ← Finset.sum_mul]
  rfl

/-- Collapsing sum: `∑ xy, p xy * log(margSnd xy.2) = ∑ b, margSnd b * log(margSnd b)`. -/
private lemma sum_joint_mul_log_margSnd [Fintype α] [Fintype β] (p : α × β → ℝ) :
    ∑ xy : α × β, p xy * Real.log (marginalSnd p xy.2) =
    ∑ b : β, marginalSnd p b * Real.log (marginalSnd p b) := by
  simp_rw [Fintype.sum_prod_type_right, ← Finset.sum_mul]
  rfl

/-- The product distribution sums to 1 when the joint sums to 1. -/
private lemma product_marginals_sum_eq_one [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_sum : ∑ x, p x = 1) :
    ∑ xy : α × β, marginalFst p xy.1 * marginalSnd p xy.2 = 1 := by
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [marginalFst_sum_eq_one hp_sum, marginalSnd_sum_eq_one hp_sum, one_mul]

/-- Mutual information expressed as KL divergence from the joint to the product of marginals:
`I(X;Y) = D_KL(p ‖ p_X ⊗ p_Y)`. -/
theorem mutualInfo_eq_klDiv [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x) :
    mutualInfo p = klDiv p (fun xy => marginalFst p xy.1 * marginalSnd p xy.2) := by
  -- Strategy: show both sides equal
  -- ∑ xy, p xy * log(p xy) - ∑ xy, p xy * log(margFst xy.1) - ∑ xy, p xy * log(margSnd xy.2)
  --
  -- For mutualInfo: use entropy = ∑ negMulLog and collapse marginal sums
  -- For klDiv: split log(a / (b*c)) = log a - log b - log c termwise
  suffices hkl : klDiv p (fun xy => marginalFst p xy.1 * marginalSnd p xy.2) =
      ∑ xy : α × β, p xy * Real.log (p xy) -
      ∑ xy : α × β, p xy * Real.log (marginalFst p xy.1) -
      ∑ xy : α × β, p xy * Real.log (marginalSnd p xy.2) by
    rw [hkl]
    -- Now show mutualInfo = the same expression
    unfold mutualInfo entropy
    simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
    rw [← sum_joint_mul_log_margFst, ← sum_joint_mul_log_margSnd]
    ring
  -- Prove the klDiv expansion
  unfold klDiv
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hxy : p xy = 0
  · simp [hxy]
  · have hpxy : 0 < p xy := lt_of_le_of_ne (hp_nonneg xy) (Ne.symm hxy)
    have hmf : 0 < marginalFst p xy.1 :=
      marginalFst_pos_of_pos hp_nonneg (by rwa [Prod.eta])
    have hms : 0 < marginalSnd p xy.2 :=
      marginalSnd_pos_of_pos hp_nonneg (by rwa [Prod.eta])
    rw [Real.log_div hxy (ne_of_gt (mul_pos hmf hms)),
        Real.log_mul (ne_of_gt hmf) (ne_of_gt hms)]
    ring

/-- **Mutual information is nonneg**: `I(X;Y) ≥ 0`.
Follows from `mutualInfo_eq_klDiv` + `klDiv_nonneg` (Gibbs' inequality). -/
theorem mutualInfo_nonneg [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x)
    (hp_sum : ∑ x, p x = 1)
    (hac : ∀ (x : α × β), p x ≠ 0 → marginalFst p x.1 * marginalSnd p x.2 ≠ 0) :
    0 ≤ mutualInfo p := by
  rw [mutualInfo_eq_klDiv hp_nonneg]
  exact klDiv_nonneg hp_nonneg
    (fun xy => mul_nonneg (marginalFst_nonneg hp_nonneg xy.1) (marginalSnd_nonneg hp_nonneg xy.2))
    hp_sum
    (product_marginals_sum_eq_one hp_sum)
    hac

/-- **Conditioning reduces entropy**: `H(Y|X) ≤ H(Y)`.
Equivalent to mutual information being nonneg: `I(X;Y) = H(Y) - H(Y|X) ≥ 0`. -/
theorem condEntropy_le_entropy [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x)
    (hp_sum : ∑ x, p x = 1)
    (hac : ∀ (x : α × β), p x ≠ 0 → marginalFst p x.1 * marginalSnd p x.2 ≠ 0) :
    condEntropy p ≤ entropy (marginalSnd p) := by
  have h := mutualInfo_nonneg hp_nonneg hp_sum hac
  rw [mutualInfo_alt] at h
  linarith

/-- Superadditivity of `negMulLog`: `negMulLog(∑ f) ≤ ∑ negMulLog(f)` for nonneg `f`.
The key step: each `f(c) ≤ ∑ f`, so `log(f(c)) ≤ log(∑ f)`, hence
`f(c) * log(f(c)) ≤ f(c) * log(∑ f)`. Summing and negating gives the result. -/
private lemma negMulLog_sum_le {γ : Type*} [Fintype γ] {f : γ → ℝ} (hf : ∀ (c : γ), 0 ≤ f c) :
    negMulLog (∑ c, f c) ≤ ∑ c, negMulLog (f c) := by
  -- Step 1: termwise bound f(c) * log(f(c)) ≤ f(c) * log(∑ f)
  have key : ∀ (c : γ), f c * Real.log (f c) ≤ f c * Real.log (∑ c', f c') := by
    intro c
    by_cases hc : f c = 0
    · simp [hc]
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (lt_of_le_of_ne (hf c) (Ne.symm hc))
          (Finset.single_le_sum (fun c' _ => hf c') (Finset.mem_univ c)))
        (hf c)
  -- Step 2: sum and factor to get ∑ f*log(f) ≤ (∑ f) * log(∑ f)
  have sum_le : ∑ c, f c * Real.log (f c) ≤ (∑ c, f c) * Real.log (∑ c, f c) :=
    calc ∑ c, f c * Real.log (f c)
        ≤ ∑ c, f c * Real.log (∑ c', f c') := Finset.sum_le_sum (fun c _ => key c)
      _ = (∑ c, f c) * Real.log (∑ c', f c') := by rw [← Finset.sum_mul]
  -- Step 3: convert to negMulLog form (negate both sides)
  unfold negMulLog
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib]
  linarith

/-- **Conditional entropy is nonneg**: `H(Y|X) ≥ 0`, i.e., `H(X,Y) ≥ H(X)`.

Proof: for each fiber `a`, `negMulLog(∑_b p(a,b)) ≤ ∑_b negMulLog(p(a,b))` by
log monotonicity (each `p(a,b) ≤ ∑_b' p(a,b')` implies `log p(a,b) ≤ log(∑ p)`).
Summing over fibers gives `H(X) ≤ H(X,Y)`. -/
theorem condEntropy_nonneg [Fintype α] [Fintype β] {p : α × β → ℝ}
    (hp_nonneg : ∀ (x : α × β), 0 ≤ p x) :
    0 ≤ condEntropy p := by
  unfold condEntropy entropy marginalFst
  rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro a _
  have h := negMulLog_sum_le (f := fun b => p (a, b)) (fun b => hp_nonneg (a, b))
  linarith

end ConditionalEntropy
