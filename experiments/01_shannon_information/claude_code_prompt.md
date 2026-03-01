# Formalizing Shannon Information

Your task is to formalize in Lean4 shannon information according to the notes I gave.
In particular, you must use the Lean4 kernel/compiler and make sure the files compile. 
When you choose to do the proofs; they must be accepted by the Lean4 kernel/compiler --
otherwise, they must be left as soryy.

Ideally we should follow the Mathlib or CSLiB standards. 

Think very carefully and always do correct hings please.
You can put the notes here: `/Users/brandomiranda/formal-6-437/Formal6437/Formal6437/InformationTheory/` 
idk if to make a new folder or file for this so make that decision yourself; in particular note we will formalize all of information theory.

Note; use mathlib or cslib as much as you want. If there are already formalizations of probability from mathlib feel free to import them. 
Ideally I'd like to push this to math or cslib eventually. 

PS: if mathlib wasn't "installed" then install it fully. And there should be other lean projects in this computer, so I wonder if there is a way to re-use them or what the deal with that would be? Maybe let's add that to the readme.md of this folder so it's clear how to use/install mathlib. 

Feel free to git add commit push for this repo, since my team will help me review this as a PR later. 

------

## GPT5 thinking heavy

Prompt:
```txt
Note: seems bishop uses h(x) for info of RV taking value x and macay h(xi=a) and I like h(X=x) or h_X(x) for info content to encode/send -- probably because capital H is used for entropy (avg info to specify encode vals from RV X). 
Note; bit = binary digit
--- Transcribe these notes in detail and accurately and factually and then write a lean implementation especially that would be consistent with mathlib or cslib from lean 4.
```
Path `/Users/brandomiranda/formal-6-437/experiments/01_shannon_information/shannon_info_ver1.jpg`
Response:
```txt
**TL;DR:** Your page is building the “surprisal” / information content (h_X(x) = -\log p_X(x)) (aka self-information) and then entropy (H(X)=\mathbb E[h_X(X)]) as the average code length / average surprise; below is a faithful transcription plus a Lean 4 (mathlib-style) implementation for finite discrete distributions.

---

## 1) Transcription (verbatim-ish, keeping your notation + intent)

**Goal / idea.**

* “(X=x): how much info we receive when RV takes value (x).”
* Amount of info ( \approx ) the degree of **surprise** on learning the value (X=x).
* If we were **certain** of the event: (p(x)=1) (\Rightarrow) that event shows us **zero info** (bits).

**Intuition.**

* An **unlikely** event tells us **a lot** of info because it surprises us, so we learn a lot.

**Thus (definition).**

* (;;;;)def (h(x) := -\log p(x)).

  * (noted equivalently) (h(x) = \log!\left(\frac{1}{p(x)}\right)).
  * (side note near top right) log base choice: (\log_2) gives **bits**, (\ln) gives **nats** (MacKay).

**Independence property.**

* If (X \perp Y) then (h(x,y) = h(x) + h(y)).

  * (you also scribbled: (h_{p_{X,Y}}(x,y)) or “(h_X(x)), (h_Y(y))” and “we can also define (h_Z(z))” style comment)

**Monotonicity.**

* “(h(x)) is monotonic: if (x \le y \Rightarrow h(x)\le h(y)) := by property of logs.”

  * (Interpretation note: this monotonicity is really about probability: if (p(x)\ge p(y)) then (-\log p(x)\le -\log p(y)).)

**Nonnegativity.**

* “Info is always positive or zero: (h(x)\ge 0).”

**Convention.**

* “(0\log 0 = 0 \equiv \lim_{p\to 0} p\log p = 0 :=) by l’Hospital.”

**More intuition: coding / efficiency.**

* “Intuition: to transmit less info (more efficiently): if there is nonuniformity in the dist (p_X(\cdot)) then we can encode and therefore send less info / be more efficient.”
* Example idea: if some events/RV values are more probable than others, we can encode them with **smaller/less bits**, and less likely ones with **more bits**. So overall we send/encode **less** info **on average** for (p_X(\cdot)).

**Entropy definition.**

* “Def: (H(X)): avg amount of info to encode/transmit the state of a RV e.g. (X=x).”

  * (You also wrote variants like (H(p_X)), (H(X)), (H_{p_X}(X)) / “in (h_{p_X}(\cdot)) (aka distribution) matters” and “degree of surprise / long-ness”.)

**Question (written).**

* “Q: why does it mean/measure the amount of disorder in physics?”

**TODOs (written).**

* “TODO: Really in depth understanding of (h(x)); why is it info content, surprise, etc.?”
* “multiplicity Bishop” (note to check Bishop’s discussion / physics-style counting).
* “why (2^{-3}, 2^{-2}), etc map to bits exactly.”

---

## 2) Answering your inline question: “why ‘disorder’ in physics?”

Physics uses (roughly) the same math but a different story:

* In statistical mechanics, “disorder” is basically “how many microstates are compatible with the macrostate.” If there are (W) equally likely microstates, then one natural measure is (\log W) (because independent systems multiply microstate counts, and logs turn products into sums—same additivity vibe as your independence property).
* If microstates are **not** equally likely, the right generalization is the **expected surprise**: (H(X)=\mathbb E[-\log p(X)]). This matches “how many bits you’d need on average to specify the exact microstate,” which is why entropy behaves like “uncertainty / multiplicity / disorder.” (The Shannon form also drops out of log-loss optimality in decision-theoretic derivations. )

---

## 3) Lean 4 (mathlib-style) implementation

Below is a practical Lean 4 file that:

* defines **information content** (your (h_X(x))) for a `PMF α`,
* defines **entropy** (H(X)) as an expectation,
* includes a clean “independence ⇒ additivity” lemma in a form that matches how mathlib typically expresses independence (product pmf).

This is written to be *consistent with mathlib conventions*, i.e., using `ProbabilityTheory.PMF`.

```lean
import Mathlib.Probability.ProbabilityMassFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib

open scoped BigOperators
open Classical

namespace InfoTheory

open ProbabilityTheory

/--
Information content / surprisal in **nats**:
    h_p(a) = - log p(a)

We use `ENNReal.toReal` to coerce probabilities into `ℝ`.
We also explicitly guard the `p a = 0` case, because in info theory
`-log 0` should be `+∞`. In ℝ we can’t represent `+∞`, so we choose
a conventional “finite” surrogate value `0` for `p a = 0`.
That convention is harmless for entropy computations because the entropy
uses the `p a * h(a)` pattern and `0 * (anything)` should be `0`.
(If you want literal `∞`, use `ℝ≥0∞`-valued info content instead.)
-/
def infoContent (p : PMF α) (a : α) : ℝ :=
  if h0 : p a = 0 then
    0
  else
    -Real.log (ENNReal.toReal (p a))

/--
Entropy in nats:
    H(p) = E_{a~p}[ infoContent p a ].

For finite alphabets this is the familiar `∑ p(a) * (-log p(a))`.
-/
def entropy (p : PMF α) : ℝ :=
  p.expect (fun a => infoContent p a)

/--
A more explicit finite-sum form when `α` is finite.
This is often the form you want when doing algebra.
-/
lemma entropy_eq_sum [Fintype α] (p : PMF α) :
    entropy p = ∑ a, (ENNReal.toReal (p a)) * infoContent p a := by
  -- `PMF.expect` over a finite type is a sum.
  simp [entropy, PMF.expect, Finset.sum_attach]

/--
If a joint pmf factors as a product, the information content adds:
    h_{p×q}(a,b) = h_p(a) + h_q(b)

This is the Lean version of your independence property.
-/
lemma infoContent_prod (p : PMF α) (q : PMF β) (a : α) (b : β) :
    infoContent (p.prod q) (a, b) = infoContent p a + infoContent q b := by
  -- Expand definitions and use log(product) = log + log (on positive reals).
  -- We keep it simple and do case splits on whether probabilities are 0.
  by_cases ha : p a = 0
  · -- then (p.prod q) (a,b) = 0, so both sides reduce appropriately
    simp [infoContent, ha, PMF.prod, ha]
  · by_cases hb : q b = 0
    · simp [infoContent, hb, PMF.prod, hb, ha]
    ·
      -- In the nonzero case, `toReal` is positive, so log rules apply.
      -- `PMF.prod` value is (p a) * (q b) in `ℝ≥0∞`.
      -- `ENNReal.toReal_mul` helps after ensuring finiteness.
      have hpa : (ENNReal.toReal (p a)) ≠ 0 := by
        -- `toReal = 0` iff original is 0
        simpa [ENNReal.toReal_eq_zero] using ha
      have hqb : (ENNReal.toReal (q b)) ≠ 0 := by
        simpa [ENNReal.toReal_eq_zero] using hb
      -- Now compute
      simp [infoContent, ha, hb, PMF.prod, Real.log_mul, hpa, hqb]
        -- `Real.log_mul` needs nonzero; the simp line above supplies it.

end InfoTheory
```

### Notes about this Lean choice (pragmatic + mathlib-aligned)

* If you want *literal* “(+\infty) surprisal” for zero-probability events, the clean route is to define `infoContent : α → ℝ≥0∞` using `ENNReal.log`-style tooling (or extended real logs) and keep everything in `ℝ≥0∞`. For entropy proofs, though, the `0 * log 0 = 0` convention is exactly why the real-valued entropy formula behaves nicely. 

---

## 4) Matching your notation preferences

If you want your preferred explicit style, you can treat these as:

* (h_{p_X}(x)) ↔ `infoContent p x`
* (H(p_X)) or (H(X)) ↔ `entropy p`

That’s faithful to your point: (h) is event-level surprise; (H) is the distribution-level average.

---
```

------

## GPT5.2 pro extended response:

Path `/Users/brandomiranda/formal-6-437/experiments/01_shannon_information/shannon_info_ver1.jpg`
Prompt:
```txt
Transcribe these notes in detail and accurately and factually and then write a lean implementation especially that would be consistent with mathlib or cslib from lean 4. 
```
Response:
```txt
1) Detailed transcription (as written)

(I’m transcribing what’s on the page, keeping the original phrasing/notation. Where the handwriting is ambiguous, I mark it with [?].)

⸻

“X = x” (the “X” is written in a stylized way, a bit like Σ)
→ “how much info we receive when RV takes value x.”

Amount of info (there’s a small side note above: “in Q: disorder.” [?])
Amount of info := the degree of surprise on learning the value of X = x.
(nearby note) surprise ≡ “entropy”.

i.e. if we were certain of the event p(x) = 1 ⇒ that event gives us zero info (margin points to) h(x) = 0.

Thus: an unlikely event tells us a lot of info because it surprises us, so we learn a lot.

Thm: def h(x) := − log p(x)
(written to the right) h(x) = −log p(x) = log 1/p(x)
(the word “unrelated” is written under the long arrow between these lines)

Independence property: (there’s a scribbled-out chunk here)
if X ⟂ Y ⇒ h(x) + h(y)
(It looks like the intended statement is “joint info adds,” but the joint term (like h(x,y)) isn’t explicitly written.)

Lmm: h(x) is monotonic; if x ≤ y ⇒ h(x) ≤ h(y) := by property of logs.

Thm: info is always positive or zero; h(x) ≥ 0

Thm: 0 log 0 = 0 ≡ lim p log p = 0 := by l’Hôpital.
(“p→0” is indicated under the “lim”.)

⸻

✱ Intuition: to transmit less info (more efficiently): if there is some nonuniformity in the dist pₓ(·) then we can encode & therefore send less info / be more efficient.
For example: if some events/RVs are more probable than others, we can encode those with smaller/less info (“bits = bny digits” is written here — i.e. binary digits), and the less likely we use more bits, so that in the hope overall we send/encode less info on avg for pₓ(·).

(small comment above this section): comment on [beyond scale?] how uniform distribution is considered “most diverse” but it contains no meaningful information (it’s just totally random).  [?]

(arrow note near the “avg” idea): in bits (bny digits), nats (natural digits) / degree of surprise / len.

⸻

def: H(X) := avg amount of info to encode/transmit the state of a RV e.g. X = x
(written under it) avg surprise

Q: why does it mean/matter the amount is discrete in physics?

TODO: Really in depth understanding of h(x); y is it info content, surprise, etc.?

⸻

Margin note (top-right):
Looks like: h(X = x) matches … → Shannon h(x) & Boltz[mann] → MacKay’s notation.
(The spiral binding blocks part of this, but “Shannon”, “Boltz…”, and “MacKay’s notation” are pretty clear.)

⸻

2) Lean 4 (mathlib-style) implementation

Below is a “lean” (minimal) implementation that matches the math on the page:
	•	surprisal p = -log p (your h(x) but as a function of probability p)
	•	Shannon entropy on a finite type: H(p) = ∑ p(a) * surprisal (p(a))
	•	bits vs nats: bits = divide by log 2
	•	basic lemmas: h(1)=0, additivity under multiplication (-log(pq)= -log p -log q), nonnegativity on (0,1].

I’m writing it in a way that’s idiomatic for mathlib: namespaces, docstrings, simp lemmas, open scoped BigOperators, etc.

import Mathlib

open scoped BigOperators

namespace InfoTheory

/-- Information content / surprisal of an outcome with probability `p`.

We use the natural logarithm `Real.log`, so the unit is **nats**.
(If you want **bits**, divide by `Real.log 2`.) -/
def surprisal (p : ℝ) : ℝ :=
  - Real.log p

/-- Surprisal measured in bits: `-log₂ p = -(log p) / (log 2)`. -/
def surprisalBits (p : ℝ) : ℝ :=
  surprisal p / Real.log 2

@[simp] lemma surprisal_one : surprisal 1 = 0 := by
  simp [surprisal]

/-- Additivity of surprisal for independent probabilities: `-log(pq) = -log p + -log q`
(assuming `p,q > 0` so the log-multiplication lemma applies). -/
lemma surprisal_mul {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    surprisal (p * q) = surprisal p + surprisal q := by
  -- mathlib: `Real.log_mul` needs positivity hypotheses
  simp [surprisal, Real.log_mul, hp, hq, add_comm, add_left_comm, add_assoc, mul_assoc]

/-- Nonnegativity of surprisal on probabilities `p ∈ (0,1]`: since `log p ≤ 0`, we have `-log p ≥ 0`. -/
lemma surprisal_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ surprisal p := by
  have hlog : Real.log p ≤ 0 := Real.log_le_zero hp hp1
  -- `0 ≤ -log p`
  simpa [surprisal] using (neg_nonneg.mpr hlog)

@[simp] lemma zero_mul_log_zero : (0 : ℝ) * Real.log 0 = 0 := by
  simp

/-
Your notes mention the removable-singularity fact `lim_{p→0} p log p = 0`.
In mathlib this exists as a `Tendsto` lemma (name depends slightly on imports;
often something like `Real.tendsto_mul_log_zero` or `tendsto_mul_log_zero`).

If you want it formally, you can uncomment/adapt the following once you know the exact lemma name
in your local mathlib version.

-- theorem tendsto_mul_log_zero :
--     Filter.Tendsto (fun p : ℝ => p * Real.log p)
--       (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
--   simpa using Real.tendsto_mul_log_zero
-/

section FiniteEntropy

variable {α : Type*} [Fintype α]

/-- Shannon entropy (in nats) of a function `p : α → ℝ` on a finite type.

This is the raw formula `∑ a, p a * (-log (p a))`.

To interpret `p` as a probability distribution you typically assume:
`(∀ a, 0 ≤ p a)` and `(∑ a, p a = 1)`. -/
def entropy (p : α → ℝ) : ℝ :=
  ∑ a, p a * surprisal (p a)

lemma entropy_eq_sum_neg_mul_log (p : α → ℝ) :
    entropy p = ∑ a, - p a * Real.log (p a) := by
  -- unfold and rearrange
  simp [entropy, surprisal, mul_assoc, mul_left_comm, mul_comm]

/-- Entropy measured in bits (base-2). -/
def entropyBits (p : α → ℝ) : ℝ :=
  entropy p / Real.log 2

end FiniteEntropy

end InfoTheory

How this lines up with your page
	•	Your h(x) := -log p(x) ↔ InfoTheory.surprisal (p : ℝ).
	•	Your “bits vs nats” note ↔ surprisalBits and entropyBits.
	•	Your “independence property” ↔ surprisal_mul (because independence gives p(x,y)=p(x)p(y)).
	•	Your H(X) = avg amount … ↔ entropy p = ∑ p(a) * surprisal (p(a)) (finite version).

If you later want the measure-theoretic version (random variable X : Ω → α, probability measure μ, and p(x)=μ {ω | X ω = x}), the next step is to define surprisal using μ and Set.preimage of singletons, and then define entropy as an expectation. That’s very doable in mathlib, but it’s a second layer of abstraction on top of the “finite distribution” layer above.
```