/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] := by
  rel [ha]


example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
  calc
    a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] := by rel [ha]
    _ ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel [hb]
    _ = 2 + 5 * 8 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra


example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] := by
  use 8
  calc
    (6:ℤ) * 8 = 4 + 4 * 11 := by numbers
    _ ≡ 4 [ZMOD 11] := by extra


example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]    
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

/-! # Exercises -/


example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := calc
  n ^ 3 + 7 * n ≡ 1^3 + 7*1 [ZMOD 3] := by rel [hn]
  _ = 2 + 2*3 := by numbers
  _ ≡ 2 [ZMOD 3] := by extra


example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] := calc
 (a + b) ^ 3 = a ^ 3 + b ^ 3 +  3*(a^2*b + b^2*a) := by ring
  _ ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by extra

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2
  numbers
  use 1
  numbers

example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  · calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 ^2 + 3 * 0 + 7 [ZMOD 2] := by rel[h]
      _ = 1 + 2*3 :=  by numbers
      _ ≡ 1 [ZMOD 2] := by extra
  · calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^2 + 3 * 1 + 7 [ZMOD 2] := by rel[h]
      _ = 1 + 2*7 :=  by numbers
      _ ≡ 1 [ZMOD 2] := by extra

example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases h : x % 5
  · calc
      x^5 ≡ 0^5 [ZMOD 5] := by rel[h]
      _ = 0  :=  by numbers
      _ ≡ x [ZMOD 5] := by rel[h]

  · calc
    x^5 ≡ 1^5 [ZMOD 5] := by rel[h]
    _ = 1  :=  by numbers
    _ ≡ x [ZMOD 5] := by rel[h] 

  · calc
    x^5 ≡ 2^5 [ZMOD 5] := by rel[h]
    _ = 2 + 5*6  :=  by numbers
    _ ≡ 2 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel[h] 

  · calc
    x^5 ≡ 3^5 [ZMOD 5] := by rel[h]
    _ = 3 + 48*5  :=  by numbers
    _ ≡ 3 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel[h]

  · calc
    x^5 ≡ 4^5 [ZMOD 5] := by rel[h]
    _ = 4 + 204*5 :=  by numbers
    _ ≡ 4 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel[h] 


