/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · rintro ⟨x, hx⟩
    use x
    addarith[hx]


theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · rintro ⟨x, hx⟩
    use x
    addarith[hx]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro hx
    have := calc
      (x+3)*(x-2) =  x ^ 2 + x - 6 := by ring
      _ = 0 := by rw[hx]
    rw [mul_eq_zero] at this
    obtain hx|hx := this
    left; addarith[hx]
    right; addarith[hx]
  · rintro (hx|hx)
    repeat {rw[hx]; numbers}

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have := calc
      (2*a-5)^2 = 4*(a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 *-1 + 5 := by rel[h]
      _ = 1^2 := by ring
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' this (by numbers)
    have h1 : 2*2 ≤ 2*a := by addarith[h1]
    cancel 2 at h1
    have h2 : 2*a ≤ 2*3 := by addarith[h2]
    cancel 2 at h2
    interval_cases a
    · left; rfl
    · right; rfl
  
  · rintro (h|h) 
    repeat {rw[h]; numbers}


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain h|h := hn2
  · have h : n=4 := by addarith[h]
    rw[h]
    use 2
    numbers
  · have h : n=6 := by addarith[h]
    rw[h]
    use 3
    numbers


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h|h := hn1
  · have h : n=4 := by addarith[h]
    rw[h]
    use 2
    numbers
  · have h : n=6 := by addarith[h]
    rw[h]
    use 3
    numbers

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra  


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw[Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have h : 2*x = 2*6 := by addarith[h]
    cancel 2 at h

  · intro h
    rw[h]
    numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · rintro ⟨x, h⟩
    constructor
    rw[h]
    use 9*x
    ring
    rw[h]
    use 7*x
    ring
  
  · rintro ⟨⟨x, hx⟩, ⟨y,hy⟩⟩
    use 4*y - 3*x
    calc
      n = 28*n - 27*n := by ring
      _ = 28*(9*y) - 27*(7*x) := by nth_rw 1 [hy]; rw[hx]
      _ = 63*(4*y - 3*x) := by ring
    

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · rintro ⟨x, h⟩
    simp at h
    rw[h]
    use x
    ring
  · rintro ⟨x, h⟩
    simp at h
    rw[h]
    use x
    ring
    

example {a b : ℤ} (hab : a ∣ b) : a ∣ 3 * b ^ 3 - b ^ 2 + 5 * b := by
  rw [dvd_iff_modEq] at *
  calc
    3 * b ^ 3 - b ^ 2 + 5 * b ≡ 3 * 0 ^ 3 - 0 ^ 2 + 5 * 0 [ZMOD a] := by rel[hab]
    _ = 0 := by numbers
  

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h1
    have h2:= calc 
      k*k = k^2 := by ring 
      _ ≤ 6 := h1
      _ ≤ 3*3:= by numbers
    rw [← Nat.mul_self_le_mul_self_iff] at h2
    obtain h|h := eq_or_lt_of_le h2
    rw[h] at h1
    simp at h1
    interval_cases k
    left; rfl
    right; left; rfl
    right; right; rfl
  · rintro (h|h|h)
    repeat{rw[h]; numbers}
    
