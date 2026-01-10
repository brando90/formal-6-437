### **The Prompt for Codex / Cursor Agent**

**System Role:**
You are an expert Formal Verification Engineer specializing in **Lean 4** and **Mathlib4**. You are working in a specific existing project with the following structure:

* **Project Root:** `/Users/brandomiranda/formal-6-437/Formal6437/` (contains `lakefile.toml`)
* **Source Directory:** `/Users/brandomiranda/formal-6-437/Formal6437/Formal6437/`
* **Target Directory:** `/Users/brandomiranda/formal-6-437/Formal6437/Formal6437/Lecture01/`

**Task:**
Create a new Lean 4 file named **`PointwiseRisk.lean`** inside the **Target Directory** (`Lecture01`). This file must formally prove the **Pointwise Minimum Bayes Risk** theorem.

**Constraint 1: The Documentation (Strict)**
You MUST include the following specific derivation as the module docstring at the very top of the file. Use this exact text, which transcribes the user's handwritten notes:

> **Docstring Content:**
> /--
> Thm: Show that for a binary hypothesis testing H(y) = argmin ...
> 1. The global objective is to minimize the expected cost:
> H_opt = argmin E_{H,Y} [ C(H(Y), H) ]
> 2. We rewrite the expectation as an integral over marginal P(y):
> H_opt = argmin ∫ P(y) * E[ C(H(y), H) | Y=y ] dy
> 3. POINTWISE MINIMIZATION PRINCIPLE:
> Since the integrand terms are independent for each y, we can minimize
> point-wise. For a fixed y, the optimal decision H(y) is:
> H(y) = argmin_{h ∈ {H0, H1}} E[ C(h, H) | Y=y ]
> 4. BINARY CASE (The Theorem):
> With only two hypotheses H0 and H1, the optimal choice is simply the
> argmin of the two conditional risks:
> H(y) = argmin( Risk(H0|y), Risk(H1|y) )
> -/
> 
> 

**Constraint 2: The Code Structure**

1. **Imports:** Use `import Mathlib.Data.Real.Basic`.
2. **Namespace:** Wrap the code in `namespace HypothesisTesting`.
3. **Types:** Define `inductive Hypothesis | H0 | H1`.
4. **Variables:** Define priors `P0, P1`, likelihoods `p0, p1`, and costs `C00, C01, C10, C11` as Reals.
5. **Risk Definition:** Define `pointwise_risk (y : Y) (d : Hypothesis) : ℝ`.
6. **Decision Rule:** Define `optimal_decision_rule` using standard `if/else` logic that implements the `argmin` described in step 4 of the docstring.
7. **Theorem:** Name the theorem **`pointwise_min_bayes_risk_optimality`**.
* *Statement:* For all `y` and all hypotheses `h`, `pointwise_risk(optimal_rule(y)) ≤ pointwise_risk(h)`.



**Constraint 3: Verification**

* **No Sorries:** The proof must be complete.
* **Tactic Strategy:** Use `dsimp` to unfold definitions, `split_ifs` to handle the decision logic, and basic inequality lemmas.
* **Kernel Check:** Before finishing, ensure the code compiles with the Lean 4 kernel available in the project context.

**Output:**
Provide **only** the content of the `PointwiseRisk.lean` file.