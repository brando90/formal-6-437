/-
Copyright (c) 2026 Formal6437 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal6437 Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# KL Divergence and Gibbs' Inequality

This file defines the Kullback-Leibler divergence for finite discrete
probability distributions and proves Gibbs' inequality (the nonnegativity
of KL divergence).

Mathlib already has a measure-theoretic `klDiv` in
`Mathlib.InformationTheory.KullbackLeibler.Basic`. This file provides
the complementary finite-sum version for `p q : α → ℝ` with `[Fintype α]`.

## Main definitions

* `KLDivergence.klDiv` — KL divergence: `D_KL(p ‖ q) = ∑ₐ p(a) · log(p(a) / q(a))` (nats)

## Main results

* `KLDivergence.klDiv_nonneg` — **Gibbs' inequality**: `0 ≤ D_KL(p ‖ q)` for valid PMFs

## Conventions

* The natural logarithm (`Real.log`) is used; units are **nats**.
* Convention: `0 · log(0 / q) = 0`, consistent with `Real.log 0 = 0`.
* The proof uses the fundamental inequality `log(x) ≤ x - 1`
  (`Real.log_le_sub_one_of_pos`), applied termwise to `x = q(a)/p(a)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2006, Theorem 2.6.3]
* [C. E. Shannon, *A Mathematical Theory of Communication*, 1948]
* MIT 6.437 "Inference and Information," Spring 2015
-/

open scoped BigOperators
open Real

namespace KLDivergence

variable {α : Type*}

/-! ### Definition -/

/-- KL divergence (relative entropy) between finite discrete distributions, in nats.
`D_KL(p ‖ q) = ∑ₐ p(a) · log(p(a) / q(a))`.
Uses the convention `0 · log(0/q) = 0` (since `Real.log 0 = 0`). -/
noncomputable def klDiv [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, p a * Real.log (p a / q a)

/-! ### Helper lemmas -/

/-- Pointwise lower bound: `p · log(p/q) ≥ p - q` when `p > 0` and `q > 0`.
This follows from applying `log(x) ≤ x - 1` to `x = q/p`, negating, and
multiplying by `p`. -/
private lemma klDiv_term_ge_sub {p_a q_a : ℝ} (hp : 0 < p_a) (hq : 0 < q_a) :
    p_a - q_a ≤ p_a * Real.log (p_a / q_a) := by
  -- log(q/p) ≤ q/p - 1
  have h1 : Real.log (q_a / p_a) ≤ q_a / p_a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hq hp)
  -- Negate: 1 - q/p ≤ -log(q/p)
  -- Multiply by p > 0: p - q ≤ p * (-log(q/p))
  have h2 : p_a * (1 - q_a / p_a) ≤ p_a * (-Real.log (q_a / p_a)) :=
    mul_le_mul_of_nonneg_left (by linarith) hp.le
  -- Simplify LHS: p * (1 - q/p) = p - q
  have h3 : p_a * (1 - q_a / p_a) = p_a - q_a := by
    field_simp
  -- Simplify RHS: p * (-log(q/p)) = p * log(p/q)
  have h4 : p_a * (-Real.log (q_a / p_a)) = p_a * Real.log (p_a / q_a) := by
    rw [Real.log_div hq.ne' hp.ne', Real.log_div hp.ne' hq.ne']
    ring
  linarith

/-! ### Gibbs' Inequality -/

/-- **Gibbs' inequality**: KL divergence is nonnegative for valid PMFs.

For finite discrete probability distributions `p` and `q` with `q` absolutely
continuous with respect to `p` (i.e., `p(a) > 0 → q(a) > 0`), we have
`D_KL(p ‖ q) ≥ 0`.

The proof uses `log(x) ≤ x - 1` (applied to `x = q(a)/p(a)`) termwise, then
sums to get `∑(p(a) - q(a)) ≤ D_KL(p ‖ q)`, and the LHS equals `1 - 1 = 0`. -/
theorem klDiv_nonneg [Fintype α] {p q : α → ℝ}
    (hp_nonneg : ∀ (a : α), 0 ≤ p a)
    (hq_nonneg : ∀ (a : α), 0 ≤ q a)
    (hp_sum : ∑ a : α, p a = 1)
    (hq_sum : ∑ a : α, q a = 1)
    (hac : ∀ (a : α), p a ≠ 0 → q a ≠ 0) :
    0 ≤ klDiv p q := by
  unfold klDiv
  -- It suffices to show ∑(p - q) ≤ ∑ p * log(p/q), since ∑(p - q) = 0.
  suffices h : ∑ a : α, (p a - q a) ≤ ∑ a : α, p a * Real.log (p a / q a) by
    have hsub : ∑ a : α, (p a - q a) = 0 := by
      simp only [Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self]
    linarith
  apply Finset.sum_le_sum
  intro a _
  by_cases hpa : p a = 0
  · -- When p(a) = 0: need 0 - q(a) ≤ 0 * log(...), i.e. -q(a) ≤ 0
    simp [hpa, hq_nonneg a]
  · -- When p(a) > 0: use the pointwise lemma
    exact klDiv_term_ge_sub
      (lt_of_le_of_ne (hp_nonneg a) (Ne.symm hpa))
      (lt_of_le_of_ne (hq_nonneg a) (Ne.symm (hac a hpa)))

end KLDivergence
