/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

/-! # Homework 3 -/

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Int


/- 4 points -/
theorem problem1 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨a, hx⟩ := hx
  rw[hx]
  use 4*a^3 + 6*a^2 + 3*a
  ring

/- 5 points -/
theorem problem2 (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
  obtain (⟨x, h⟩ | ⟨x, h⟩) := Int.even_or_odd n
  · rw[h]
    use 10*x^2 +3*x +3
    ring
  · rw[h]
    use 10*x^2 +13*x +7
    ring

/- 4 points -/
theorem problem3 : ¬(3 : ℤ) ∣ -10 := by
  rintro ⟨k, hk⟩
  obtain (h | h) := lt_or_ge k (-3)
  · have h : k ≤ -4 := by exact Iff.mp Int.lt_add_one_iff h
    have := calc
      -10 = 3 * k := hk
      _ ≤ 3* (-4) := by linarith -- for some reason "by rel[h]" doesn't work here...
      _ = -12 := by numbers
    contradiction

  · have := calc
      -10 = 3 * k := hk
      _ ≥ 3 * (-3) := by linarith -- neither does it work here!
      _ = -9 := by numbers
    contradiction

  

/- 4 points -/
theorem problem4 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  obtain ⟨x, h1⟩ := hab
  obtain ⟨y, h2⟩ := hbc
  rw[h2,h1]
  use x^3 * y
  ring 

/- 4 points -/
theorem problem5 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  apply Int.ModEq.trans h1 h2

/- 4 points -/
theorem problem6 {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hab⟩ := hab
  obtain h|h := le_or_gt 0 a
  rw [le_iff_eq_or_lt] at h
  obtain h | h := h
  · rw[← h] at hab
    rw[hab] at hb
    calc
      0 < 0 * k := hb
      _ = a := by ring; rw[← h]
  · exact h
  · simp at h
  

