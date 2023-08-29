/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
attribute [-simp] Nat.not_two_dvd_bit1 two_dvd_bit0


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    have hmlep : m ≤ p := Nat.le_of_dvd hp' hmp
    obtain hm| hm_right : m=p ∨ m < p := eq_or_lt_of_le hmlep
    · -- the case `m=p`
      right
      exact hm
    · -- the case `m<p`
      specialize H m hm_left hm_right
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
    obtain ha_left | ha_right : a ≤ 2 ∨ a ≥ 3 := by apply le_or_gt
    obtain hb_left | hb_right : b ≤ 1 ∨ b ≥ 2 := by apply le_or_gt
    · have := calc --Case 1
        c^2 = a^2+b^2 := by rw [h_pyth]
        _   ≤ 2^2 + 1^2 := by rel [ha_left, hb_left]
        _   < 3^2 := by numbers
      have :=  lt_of_pow_lt_pow' 2 this
      interval_cases a <;> interval_cases b <;> interval_cases c
      all_goals numbers at h_pyth
    · have := calc --Case 2
        b^2 < a^2 + b^2 := by extra
        _   = c^2 := h_pyth
      
      have :=  lt_of_pow_lt_pow' 2 this
      have that := calc
        c^2 = a^2 + b^2 := by rw[h_pyth]
        _   ≤ 2^2 + b^2 := by rel[ha_left]
        _   = b^2 + 2*2 := by ring
        _   ≤ b^2 + 2*b := by rel[hb_right]
        _   < b^2+2*b+1 := by extra
        _   = (b+1)^2   := by ring
      have := calc
        b+1 ≤ c   := this
        _   < b+1 := lt_of_pow_lt_pow' 2 that
      have : 1<1 := by addarith[this]
      numbers at this
    · apply ha_right


/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
    apply le_of_pow_le_pow n <;> assumption


example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases n % 5
  · have := calc
      0 = 0^2 := by numbers 
      _ ≡ n^2 [ZMOD 5] := by rel[H]
      _ ≡ 4 [ZMOD 5] := by rel[hn]
    numbers at this
  · have := calc
      1 = 1^2 := by numbers 
      _ ≡ n^2 [ZMOD 5] := by rel[H]
      _ ≡ 4 [ZMOD 5] := by rel[hn]
    numbers at this
  · left; assumption
  · right; assumption
  · have := calc
      1 ≡ 1 + 3*5 [ZMOD 5] := by extra
      _ = 4^2 := by numbers 
      _ ≡ n^2 [ZMOD 5] := by rel[H]
      _ ≡ 4 [ZMOD 5] := by rel[hn]
    numbers at this


example : Prime 7 := by
  apply prime_test; numbers
  intro n h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases n
  repeat {use 3; constructor <;> numbers}
  repeat {use 2; constructor <;> numbers}
  repeat {use 1; constructor <;> numbers}

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h3|h3 := h3
  · have h3 : x=-2 := by addarith[h3]
    rw[h3] at h2
    numbers at h2
  · addarith[h3]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, hdiv⟩ := h
  rw [le_iff_lt_or_eq] at hp
  rcases hp  with hp | hp
  · right
    rw [odd_iff_not_even]
    rintro ⟨k, hk⟩
    obtain this|this := hdiv 2 (by use k; rw[hk]) 
    numbers at this
    rw[← this] at hp
    numbers at hp
  · left
    rw[hp]
