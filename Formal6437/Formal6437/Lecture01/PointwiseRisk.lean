import Mathlib.Data.Real.Basic

/-!
Thm: Show that for a binary hypothesis testing H(y) = argmin ...
1. The global objective is to minimize the expected cost:
H_opt = argmin E_{H,Y} [ C(H(Y), H) ]
2. We rewrite the expectation as an integral over marginal P(y):
H_opt = argmin ∫ P(y) * E[ C(H(y), H) | Y=y ] dy
3. POINTWISE MINIMIZATION PRINCIPLE:
Since the integrand terms are independent for each y, we can minimize
point-wise. For a fixed y, the optimal decision H(y) is:
H(y) = argmin_{h ∈ {H0, H1}} E[ C(h, H) | Y=y ]
4. BINARY CASE (The Theorem):
With only two hypotheses H0 and H1, the optimal choice is simply the
argmin of the two conditional risks:
H(y) = argmin( Risk(H0|y), Risk(H1|y) )
-/

namespace HypothesisTesting

inductive Hypothesis | H0 | H1 deriving DecidableEq

variable {Y : Type}
variable (P0 P1 : ℝ)
variable (p0 p1 : Y → ℝ)
variable (C00 C01 C10 C11 : ℝ)

def pointwise_risk (y : Y) (d : Hypothesis) : ℝ :=
  match d with
  | Hypothesis.H0 => P0 * C00 * p0 y + P1 * C01 * p1 y
  | Hypothesis.H1 => P0 * C10 * p0 y + P1 * C11 * p1 y

noncomputable def optimal_decision_rule (y : Y) : Hypothesis :=
  if
      pointwise_risk (P0:=P0) (P1:=P1) (p0:=p0) (p1:=p1) (C00:=C00) (C01:=C01)
          (C10:=C10) (C11:=C11) y Hypothesis.H1
        <
        pointwise_risk (P0:=P0) (P1:=P1) (p0:=p0) (p1:=p1) (C00:=C00) (C01:=C01)
          (C10:=C10) (C11:=C11) y Hypothesis.H0 then
    Hypothesis.H1
  else
    Hypothesis.H0

theorem pointwise_min_bayes_risk_optimality :
    ∀ (y : Y) (h : Hypothesis),
      pointwise_risk (P0:=P0) (P1:=P1) (p0:=p0) (p1:=p1) (C00:=C00) (C01:=C01)
          (C10:=C10) (C11:=C11) y
          (optimal_decision_rule (P0:=P0) (P1:=P1) (p0:=p0) (p1:=p1) (C00:=C00)
            (C01:=C01) (C10:=C10) (C11:=C11) y)
        ≤
        pointwise_risk (P0:=P0) (P1:=P1) (p0:=p0) (p1:=p1) (C00:=C00) (C01:=C01)
          (C10:=C10) (C11:=C11) y h := by
  intro y h
  dsimp [optimal_decision_rule]
  split_ifs with hlt
  · cases h with
    | H0 =>
        exact le_of_lt hlt
    | H1 =>
        exact le_refl _
  · cases h with
    | H0 =>
        exact le_refl _
    | H1 =>
        exact not_lt.mp hlt

end HypothesisTesting
