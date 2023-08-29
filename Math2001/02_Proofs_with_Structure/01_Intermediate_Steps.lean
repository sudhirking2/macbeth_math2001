/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith[h1]
  have h4 : r ≤ 3 - s := by addarith[h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h4, h3]
    _ = 3 := by ring

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h1 : x ≤ -1 := by addarith[hx]
  calc
    y ≥ 3 - 2*x := by addarith[hy]
    _ ≥ 3 - 2*-1 := by rel[h1]
    _ > 3 := by numbers

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have hadd : 0 ≤ b+a := by addarith[h1]
  have : 0≤ b-a := by addarith[h2]
  have := calc
    (b+a)*(b-a) ≥ 0 * (b-a) := by rel[hadd]
    _ = 0 := by ring
  calc
    a^2 ≤ a^2 + (b+a)*(b-a) := by extra
    _ = b^2 := by ring

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have : 0≤b-a := by addarith[h]
  calc
    a^3 ≤ a^3 + (b-a)*((b-a)^2 + 3*(b+a)^2)/4 := by extra
    _ = b^3 := by ring

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have hx :=  calc
    x*(x+2) =  x^2 + 2*x := by ring;
    _ = 2*(x+2) := by rw[h1]; ring
  cancel x+2 at hx

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 := calc
    (n-2)^2 = n^2+4 -4*n := by ring
    _ = 0 := by rw[hn]; ring
  have h2 : n-2 = 0 := Iff.mp sq_eq_zero_iff h1
  -- "by exact?" to figure out
  addarith[h2]

example (x y : ℚ) (h1 : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have : 0 < x*y := by rw[h1]; numbers
  have : 0 < y := by cancel x at this
  calc
    y = 1 * y := by ring
    _ ≤ x * y := by rel[h2]
    _ = 1 := by rw[h1]
 