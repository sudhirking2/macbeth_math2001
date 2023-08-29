/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring    
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    2 < 2^2 := by numbers
    _ ≤ n^2 := by rel[hn]

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h2 | h2
  left; addarith[h2] 
  right; addarith[h2] 

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  rcases h with h | h
  repeat{rw[h]; numbers}

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rcases h with h | h
  repeat{rw[h]; numbers}

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  rcases h with h | h
  repeat{rw[h]; numbers}

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  rcases h with h | h
  repeat{rw[h]; ring}

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left; addarith[h]

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc
    b = (a + 2 * b) /2 - a / 2 := by ring
    _ < 0/2 - a/2 := by rel[h] 
    _ = -a/2 := by ring

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    x = (2 * x + 1)/2 - 1/2 := by ring
    _ < y/2 - 1/2 + 1/2 := by rw[h]; extra
    _ = y/2 := by ring


example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h := calc
    (x+3)*(x-1) = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := by rw[hx]
  obtain h1 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h
  · left; addarith[h1]
  · right; addarith[h1]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h := calc
    (a-b)*(a-2*b) = a ^ 2 + 2 * b ^ 2 - 3*a*b := by ring
    _ = 0 := by rw[hab]; ring
  obtain h1 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h
  · left; addarith[h1]
  · right; addarith[h1]
  

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h := calc
    (t-1)*(t*t) = t ^ 3 - t ^ 2 := by ring
    _ = 0 := by rw[ht]; ring
  obtain h1 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h
  · left; addarith[h1]
  · right; obtain h1 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    repeat exact h1

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h := calc
    (a-b)*(a-2*b) = a ^ 2 + 2 * b ^ 2 - 3*a*b := by ring
    _ = 0 := by rw[hab]; ring
  obtain h1 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h
  · left; addarith[h1]
  · right; addarith[h1]

example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hlt := le_or_succ_le n 2
  obtain hlt | hlt := hlt
  apply ne_of_lt
  calc
    n ^ 2 ≤ 2 ^ 2 := by rel [hlt]
    _ < 7 := by numbers
  apply ne_of_gt
  calc
    7 < 3^2 := by numbers
    _ ≤ n^2 := by rel[hlt]  

example {x : ℤ} : 2 * x ≠ 3 := by
  have hlt := le_or_succ_le x 1
  obtain hlt | hlt := hlt
  apply ne_of_lt
  calc
    2*x  ≤ 2 *1 := by rel [hlt]
    _ < 3 := by numbers
  apply ne_of_gt
  calc
    3 < 2*2 := by numbers
    _ ≤ 2*x := by rel[hlt]  

example {t : ℤ} : 5 * t ≠ 18 := by
  have hlt := le_or_succ_le t 3
  obtain hlt | hlt := hlt
  apply ne_of_lt
  calc
    5*t  ≤ 5 *3 := by rel [hlt]
    _ < 18 := by numbers
  apply ne_of_gt
  calc
    18 < 5*4 := by numbers
    _ ≤ 5*t := by rel[hlt]   

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hlt := le_or_succ_le m 5
  obtain hlt | hlt := hlt
  apply ne_of_lt
  have hm : m^2 ≤ 5^2 := by rel[hlt]
  calc
    m ^ 2 + 4 * m  ≤ 5 ^ 2 + 4*m := by addarith[hm]
    _ ≤ 5^2 + 4*5 := by rel[hlt]
    _ < 46 := by numbers
  apply ne_of_gt
  have hm : 6^2 ≤ m^2 := by rel[hlt]
  calc
    46 < 6*6 + 4*6 := by numbers
    _ ≤ m^2 + 4*6 := by addarith[hm]
    _ ≤ m^2 + 4*m := by rel[hlt]   
