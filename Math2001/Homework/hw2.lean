/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Numbers
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/-! # Homework 2 -/


/- 5 points -/
theorem problem1 {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h := calc
   (x+3)*(x-1) = x ^ 2 + 2 * x - 3 := by ring
   _ = 0:= by rw[hx]
  obtain h | h := eq_zero_or_eq_zero_of_mul_eq_zero h
  · left
    addarith[h]
  · right
    addarith[h]

/- 5 points -/
theorem problem2 {a : ℝ} (ha : a ^ 3 = 0) : a = 0 := by
  obtain h | h := lt_or_ge a 0
  have h : 0 < -a := Iff.mpr neg_pos h
  · have := calc
      0 = -0 := by ring
      _ = -a^3 := by rw[ha]
      _ = -a*-a*-a := by ring
      _ > 0*0*0 := by rel[h]
      _ = 0 := by ring
    simp at this
  obtain h | h := gt_or_eq_of_le h
  · have := calc
      0 = a^3 := by rw[ha]
      _ = a*a*a := by ring
      _ > 0*0*0 := by rel[h]
      _ = 0 := by ring
    simp at this
  · exact h

/- 5 points -/
theorem problem3 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  rcases h with ⟨h1, h2⟩ 
  constructor
  · calc
    x = 2*(x + y) - (x+2*y) := by ring
    _ = 3 := by rw[h1,h2]; numbers
  · calc
    y = (x + 2*y) - (x+y) := by ring
    _ = 2 := by rw[h1,h2]; numbers

  
/- 3 points -/
theorem problem4 : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6,7
  numbers

/- 3 points -/
theorem problem5 : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use (-0.5 : ℝ) 
  numbers
  exact ⟨by triv, by triv⟩ 

/- 4 points -/
theorem problem6 {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc 
    p = (p+p)/2 := by ring
    _ < (p+q)/2 := by rel[h]
  · calc 
    (p+q)/2 < (q+q)/2 := by rel[h]
    _ = q := by ring