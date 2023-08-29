/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Homework 1 -/


/- 5 points -/
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  have hq : q = 3 := by addarith[h2]
  rw[hq] at h1; addarith[h1]

/- 5 points -/
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := calc
  a = ((a + 2 * b) + 2 * (a - b)) / 3 := by ring; 
  _ = 2 := by rw[h1, h2]; ring

/- 5 points -/
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  have h1 : x-8 ≥ 1 := by addarith[hx]
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x ≥ x ^ 3 - 8 * x ^ 2 := by extra
    _ = x * x * (x-8) := by ring
    _ ≥ x * 9 * 1 := by rel[h1, hx]
    _ ≥ 9 * 9 * 1 := by rel[hx]
    _ ≥ 3 := by numbers

/- 5 points -/
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := calc
  x^2 - 2*x = (x-1)^2 + -1 := by ring
  _ ≥ -1 := by extra

/- 5 points -/
theorem problem5 (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have this : b-a ≥ 0 := by addarith[h]
  have hdif : b^3 - a^3 ≥ 0 := calc
    b^3 - a^3 = (b-a) * (a^2 + b^2 + (a+b)^2)/2 := by ring
    _ ≥ 0 * (a^2 + b^2 + (a+b)^2)/2 := by rel[this]
    _ = 0 := by ring
  addarith[hdif]

