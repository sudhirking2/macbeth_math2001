/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/-! # Homework 4 -/


/- 2 points -/
theorem problem1 : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intro m
  exact Nat.zero_le m
  

/- 4 points -/
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 10
  intro x hx
  calc 
    x ^ 3  = x * x^2 := by ring
    _ ≥ 10*x^2  := by rel[hx]
    _ = 7*x^2 + 3*x*x := by ring
    _ ≥ 7*x^2 + 3*10*10:= by rel[hx]
    _ = 7*x^2 + 12 + 288 := by ring
    _ ≥ 7*x^2 + 12 := by extra

/- 3 points -/
theorem problem3 {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor <;> intro hx
  · calc
      x = (2*x-1 +1)/2 := by ring
      _ = 6 := by rw[hx]; ring
  · rw[hx]
    numbers
  
/- 3 points -/
theorem problem4 {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  rw [Int.odd_iff_modEq] at *
  calc
    x^3 ≡ 1^3 [ZMOD 2] := by rel[hx]
    _ = 1 := by numbers

/- 4 points -/
theorem problem5 : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
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
  

/- 5 points -/
theorem problem6 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro hn
  mod_cases n % 4
  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 0*0 [ZMOD 4] := by rel [H]
      _ = 0 := by numbers
    have h1:= @Int.existsUnique_modEq_lt 2 4 (by numbers) 
    obtain ⟨r, ⟨_,h1⟩⟩ :=  h1
    dsimp at h1
    have uhoh := h1 0 ⟨by numbers, by numbers, this⟩ 
    have uhoh2 := h1 2 ⟨by numbers, by numbers, by apply Int.ModEq.refl⟩ 
    rw[← uhoh] at uhoh2
    exact two_ne_zero uhoh2

  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 1*1 [ZMOD 4] := by rel [H]
      _ = 1 := by numbers
    have h1:= @Int.existsUnique_modEq_lt 2 4 (by numbers) 
    obtain ⟨r, ⟨_,h1⟩⟩ :=  h1
    dsimp at h1
    have uhoh := h1 1 ⟨by numbers, by numbers, this⟩ 
    have uhoh2 := h1 2 ⟨by numbers, by numbers, by apply Int.ModEq.refl⟩ 
    rw[← uhoh] at uhoh2
    have uhoh2 : 2 = 0 := by addarith[uhoh2]
    exact two_ne_zero uhoh2
  
  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 2*2 [ZMOD 4] := by rel [H]
      _ = 0+4*1 := by numbers
      _ ≡ 0 [ZMOD4] := by extra
    have h1:= @Int.existsUnique_modEq_lt 2 4 (by numbers) 
    obtain ⟨r, ⟨_,h1⟩⟩ :=  h1
    dsimp at h1
    have uhoh := h1 0 ⟨by numbers, by numbers, this⟩ 
    have uhoh2 := h1 2 ⟨by numbers, by numbers, by apply Int.ModEq.refl⟩ 
    rw[← uhoh] at uhoh2
    have uhoh2 : 2 = 0 := by addarith[uhoh2]
    exact two_ne_zero uhoh2

  · have := calc
      2 ≡ n^2 [ZMOD 4] := (Int.ModEq.symm hn)
      _ = n*n := by ring
      _ ≡ 3*3 [ZMOD 4] := by rel [H]
      _ = 1+4*2 := by numbers
      _ ≡ 1 [ZMOD4] := by extra
    have h1:= @Int.existsUnique_modEq_lt 2 4 (by numbers) 
    obtain ⟨r, ⟨_,h1⟩⟩ :=  h1
    dsimp at h1
    have uhoh := h1 1 ⟨by numbers, by numbers, this⟩ 
    have uhoh2 := h1 2 ⟨by numbers, by numbers, by apply Int.ModEq.refl⟩ 
    rw[← uhoh] at uhoh2
    have uhoh2 : 2 = 0 := by addarith[uhoh2]
    exact two_ne_zero uhoh2    


/- 4 points -/
theorem problem7 : Prime 97 := by
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
