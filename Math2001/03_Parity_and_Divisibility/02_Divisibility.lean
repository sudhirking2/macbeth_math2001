/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel
import Library.Theory.Division
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  use -3
  numbers

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use x^2 * y
  rw[hy,hx]
  ring


example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨t, h⟩ := h
  rw[h]
  use y*t
  ring

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk⟩ := hab
  rw[hk] at hb
  cancel k at hb
  
/-! # Exercises -/


example (t : ℤ) : t ∣ 0 := by
  use 0
  ring

example : ¬(3 : ℤ) ∣ -10 := by
  rintro ⟨k, hk⟩
  obtain (h | h) := lt_or_ge k (-3)
  · have h : k ≤ -4 := by exact Iff.mp Int.lt_add_one_iff h
    have := calc
      -10 = 3 * k := hk
      _ ≤ 3* (-4) := by rel[h]
      _ = -12 := by numbers
    contradiction

  · have := calc
      -10 = 3 * k := hk
      _ ≥ 3 * (-3) := by rel[h]
      _ = -9 := by numbers
    contradiction



example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, h⟩ := h
  rw[h]
  use 3*k-4*x*k^2 
  ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, h⟩ := h
  rw[h]
  use 2*m^2*k^3 + k
  ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, h⟩ := hab
  rw[h]
  use 2*a^2*k^3 - a*k^2 + 3*k
  ring

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨a, h1⟩ := h1
  obtain ⟨b, h2⟩ := h2
  rw[h2,h1]
  use a^3*b
  ring

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨a, h1⟩ := hpq
  obtain ⟨b, h2⟩ := hqr
  rw[h2,h1]
  use a^2 * b
  ring 

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  · extra
  · use 7; numbers

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1
  exact ⟨by numbers, by numbers, by use 3; numbers⟩ 

