/-
Test file to verify Mathlib is working correctly.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.ProbabilityMassFunction.Basic

#check MeasureTheory.MeasureSpace
#check PMF

-- Simple example: identity function
example : α → α := fun x => x

-- Using Aesop (included in Mathlib)
example : α → α := by aesop

