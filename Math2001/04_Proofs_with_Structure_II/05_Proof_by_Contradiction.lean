/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥  3 * 5 := by rel [h5]
    numbers at h 

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  rintro ⟨n, hn⟩
  obtain h|h := le_or_succ_le n 1 <;> 
  { have h := Nat.pow_le_pow_of_le_left h 2 
    rw [hn] at h; numbers at h }


example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction   


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h2
    rw [Int.odd_iff_modEq] at h1
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h2]
      _ ≡ 1 [ZMOD 2] := by rel [h1]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2 

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h :=
    calc 1 ≡ 1 + 3*1 [ZMOD 3]:= by extra
      _ = 2^2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction  


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have := calc b*q < a := by assumption
    _ = b*k := by rw[hk]
  cancel b at this
  have := calc q+1 ≤ k := by exact this
    _ < q+1 := by assumption
  have : 1<1 := by addarith[this]
  numbers at this

  


example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2) 
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m; rw[hl]; ring
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have := calc T*l ≤ m*l := by rel[hmT]
      _ = p := by rw[← hl]
      _ < T^2 := hTp
      _ = T*T := by ring
    cancel T at this
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  have hcon: (1:ℝ)≠0 := by exact one_ne_zero
  rintro ⟨a,h1, h2⟩ 
  have h3 := calc
    a^2 ≤ 8 := h1
    _ ≤ 3^2 := by numbers
  obtain ⟨_, h4⟩  := abs_le_of_sq_le_sq' h3 (by numbers)
  obtain (hyp|hyp) := le_or_gt a 0
  rw [le_iff_eq_or_lt] at hyp
  obtain (hyp|hyp) := hyp
  · rw[hyp] at h2
    simp at h2
    have that : 30=0 := le_antisymm h2 (by numbers)
    apply hcon
    calc
      (1:ℝ) = 30 / 30 := by ring
      _ = 0  := by rw[that]; ring

  · have : a^3 < 0 := Iff.mpr (Odd.pow_neg_iff (by use 1; numbers)) hyp
    have := calc
     1 < 30 := by numbers
     _ ≤  a^3 := h2
     _ < 0 := this
    apply hcon
    apply le_antisymm
    rw[le_iff_eq_or_lt]
    right
    exact this
    numbers
  · have := calc
      a^3 = a^2*a := by ring
      _ ≤ 8*3 := by rel[h1, h4]
      _ < 30 := by numbers
      _ ≤ a^3 := by addarith[h2]
    have : (1:ℝ) < 0 := by addarith[this]
    apply hcon
    apply le_antisymm
    rw[le_iff_eq_or_lt]
    right
    exact this
    numbers
  

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  rintro ⟨h1, h2⟩
  rw[Int.even_iff_modEq] at h1
  obtain ⟨k, hk⟩ := h1
  simp at hk
  rw[hk] at hn
  have : 2*k = 2*2 := by addarith [hn]
  cancel 2 at this
  rw [hk, this] at h2
  numbers at h2

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  rintro (h|h)
  have hx:= calc x^2 < 9 := hx
    _ = 3^2 := by numbers
  obtain ⟨h1, h2⟩ := abs_lt_of_sq_lt_sq' hx (by numbers)
  have := calc -3 < x := by assumption
    _ ≤ -3 := by assumption
  numbers at this
  have : x^2 ≥ 3^2 :=  pow_le_pow_of_le_left (by numbers) h 2
  have := calc 3^2 ≤ x^2 := this
    _ < 9 := hx
  numbers at this

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  rintro ⟨n, hn⟩
  have : ¬ Nat.Even (2*n+1) := by
    rw[← Nat.odd_iff_not_even]
    use n; ring
  apply this
  have := calc 2*n+1 = n + (n+1) := by ring
    _ > n := by extra 
  exact hn _ this

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro hn
  mod_cases n % 4
  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 0*0 [ZMOD 4] := by rel [H]
      _ = 0 := by numbers
    numbers at this

  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 1*1 [ZMOD 4] := by rel [H]
      _ = 1 := by numbers
    numbers at this
  
  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 2*2 [ZMOD 4] := by rel [H]
      _ = 0+4*1 := by numbers
      _ ≡ 0 [ZMOD4] := by extra
    numbers at this

  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 3*3 [ZMOD 4] := by rel [H]
      _ = 1+4*2 := by numbers
      _ ≡ 1 [ZMOD4] := by extra
    numbers at this

example : ¬ Prime 1 := by
  rintro ⟨h, _⟩
  numbers at h
  

example : Prime 97 := by
  apply prime_test; numbers
  intro n h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases n
  repeat {use 48; constructor <;> numbers}
  repeat {use 47; constructor <;> numbers}
  repeat {use 46; constructor <;> numbers}
  repeat {use 45; constructor <;> numbers}
  repeat {use 44; constructor <;> numbers}
  repeat {use 43; constructor <;> numbers}
  repeat {use 42; constructor <;> numbers}
  repeat {use 43; constructor <;> numbers}
  repeat {use 42; constructor <;> numbers}
  repeat {use 41; constructor <;> numbers}
  repeat {use 40; constructor <;> numbers}
  repeat {use 39; constructor <;> numbers}
  repeat {use 38; constructor <;> numbers}
  repeat {use 37; constructor <;> numbers}
  repeat {use 36; constructor <;> numbers}
  repeat {use 35; constructor <;> numbers}
  repeat {use 34; constructor <;> numbers}
  repeat {use 33; constructor <;> numbers}
  repeat {use 32; constructor <;> numbers}
  repeat {use 31; constructor <;> numbers}
  repeat {use 30; constructor <;> numbers}
  repeat {use 29; constructor <;> numbers}
  repeat {use 28; constructor <;> numbers}
  repeat {use 27; constructor <;> numbers}
  repeat {use 26; constructor <;> numbers}
  repeat {use 25; constructor <;> numbers}
  repeat {use 24; constructor <;> numbers}
  repeat {use 23; constructor <;> numbers}
  repeat {use 22; constructor <;> numbers}
  repeat {use 21; constructor <;> numbers}
  repeat {use 20; constructor <;> numbers}
  repeat {use 19; constructor <;> numbers}
  repeat {use 18; constructor <;> numbers}
  repeat {use 17; constructor <;> numbers}
  repeat {use 16; constructor <;> numbers}
  repeat {use 15; constructor <;> numbers}
  repeat {use 14; constructor <;> numbers}
  repeat {use 13; constructor <;> numbers}
  repeat {use 12; constructor <;> numbers}
  repeat {use 11; constructor <;> numbers}
  repeat {use 10; constructor <;> numbers}
  repeat {use 9; constructor <;> numbers}
  repeat {use 8; constructor <;> numbers}
  repeat {use 7; constructor <;> numbers}
  repeat {use 6; constructor <;> numbers}
  repeat {use 5; constructor <;> numbers}
  repeat {use 4; constructor <;> numbers}
  repeat {use 3; constructor <;> numbers}
  repeat {use 2; constructor <;> numbers}
  repeat {use 1; constructor <;> numbers}