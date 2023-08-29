/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have := calc 
      0 < -x * t := by addarith[hxt]
      _ = x*(-t) := by ring
    cancel x at this
    have : 0 > t := by exact Iff.mp neg_pos this
    exact ne_of_lt this


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc 
    p = (p+p)/2 := by ring
    _ < (p+q)/2 := by rel[h]
  · calc 
    (p+q)/2 < (q+q)/2 := by rel[h]
    _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 7, 6 
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use (-0.5 : ℝ) 
  numbers
  exact ⟨by triv, by triv⟩ 

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0,0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h := le_or_gt 0 x
  obtain h | h := h
  · use x+1
    calc 
      (x+1)^2 = x^2 + 1 + 2*x := by ring
      _ > 2*x := by extra
      _ = x + x := by ring
      _ ≥ 0+x := by rel[h]
      _ = x := by ring
  · use x-1
    have : 0 < -x := Iff.mpr neg_pos h
    calc 
      (x-1)^2 = x^2 + 1 + -2*x := by ring
      _ > -2*x := by extra
      _ = -x + -x := by ring
      _ > 0 + 0 := by rel[this, this]
      _ = 0 := by ring
      _ > x := by rel[h]

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  intro ht
  rcases h with ⟨a, h⟩ 
  rw[ht] at h
  apply Iff.mp (lt_self_iff_false (a+1))
  simp at h 

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h⟩ := h
  intro hm
  rw[hm] at h
  simp at h
  obtain h1 | h1 :=  le_or_gt a 2 
  · have := calc
      5 = 2*a := by rw[h]
      _ ≤ 2 * 2 := by rel[h1] 
    simp at this
  · have h1 : a ≥ 3 := by exact h1
    have := calc
      5 = 2 * a := by rw[h]
      _ ≥ 2 * 3 := by rel[h1]
      _ = 6 := by numbers
    simp at this


example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b)
    (ha' : 0 ≤ a) (hb' : 0 ≤ b) (hc' : 0 ≤ c) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b+c-a)/2, (a+c-b)/2, (a+b-c)/2
  constructor
  calc
     (b+c-a)/2 = (b+c)/2 - a/2 := by ring
     _ ≥ (b+c)/2 - (b+c)/2 := by rel[ha]
     _ = 0 := by ring
  constructor
  calc
     (a+c-b)/2 = (a+c)/2 - b/2 := by ring
     _ ≥ (a+c)/2 - (a+c)/2 := by rel[hb]
     _ = 0 := by ring
  constructor
  calc
     (a+b-c)/2 = (a+b)/2 - c/2 := by ring
     _ ≥ (a+b)/2 - (a+b)/2 := by rel[hc]
     _ = 0 := by ring
  ring
