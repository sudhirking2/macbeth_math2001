/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.Ring
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5*a-3*n
  calc
    n = 5 * (5*n) - 24*n := by ring
    _ =  8 * (5 * a - 3 * n) := by rw[ha]; ring 

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨x, h1⟩ := h1
  use 2*x-n
  calc
    n = 2 * (3*n) - 5*n := by ring
    _ =  5 * (2 * x - n) := by rw[h1]; ring 

example {m : ℤ} (h2 : 5 ∣ m) (h1 : 8 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5*a-9*n
  calc
    n = 5 * (11*n) - 54*n := by ring
    _ = 6 * (5*a-9*n) := by rw[ha]; ring 

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨x, h1⟩ := h1
  use 2*x-n
  calc
    n = 2 * (3*n) - 5*n := by ring
    _ =  5 * (2 * x - n) := by rw[h1]; ring 

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨x, ha⟩ := ha
  use 3*x - 2*a
  calc
    a = 3 * (5*a) - 14*a := by ring
    _ = 7 * (3*x - 2*a) := by rw[ha]; ring

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use 4*b - 3*a
  calc
    n = 28 * n - 27 * n := by ring
    _ = 28 * (9*b) - 27 * (7*a) := by nth_rw 1 [hb]; rw [ha]
    _ = 63 * (4*b - 3*a) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use (2*a - 5*b)
  calc
    n = 26 * n - 25 * n := by ring
    _ = 26 * (5*a) - 25 * (13*b) := by nth_rw 1 [ha]; rw [hb]
    _ = 65 * (2*a - 5*b) := by ring
