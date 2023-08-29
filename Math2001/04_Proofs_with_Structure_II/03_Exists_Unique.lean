/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h1 h2 
    have h1 : -1 ≤ a-2 := by addarith[h1]
    have h2 : 1 ≥ a-2 := by addarith[h2]
    have : (1:ℚ) = 1^2 := by exact Eq.symm (one_pow 2)
    rw[this]
    apply sq_le_sq' h1 h2
  · intro y h
    have h1 := h 1 (by numbers) (by numbers)
    have h3 := h 3 (by numbers) (by numbers)
    rw [← sub_eq_zero]
    rw [← sq_eq_zero_iff]
    apply le_antisymm
    · calc
      (y-2)^2 = ((1-y)^2 + (3-y)^2 -2)/2 := by ring
      _ ≤ ((1:ℚ) + 1 -2)/2 := by rel[h1, h3]
      _ = 0 := by numbers
    · extra
      

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  numbers
  intro y h 
  have h : 4*y = 4 *3 := by addarith[h]
  cancel 4 at h

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  exact fun a ↦ Nat.zero_le a
  intro y h 
  cases y -- ℕ is an inductive type constructed by either 0 or as the successor of some nat
  · rfl
  · specialize h 0
    simp at h
    
example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  have := calc
    11 = 2 + 3*3 := by numbers
    _ ≡ 2 [ZMOD 3] := modEq_add_fac_self
  use 2
  constructor
  constructor 
  numbers
  constructor 
  numbers
  exact this
  rintro a ⟨h1, h2, h3⟩
  interval_cases a
  · obtain ⟨x, hx⟩ := h3
    obtain h|h := le_or_gt x 3
    have := calc
      (11:ℤ) = 11 - 0 := by numbers
      _ = 3*x := hx
      _ ≤ 3*3 := by rel[h]
      _ = 9 := by numbers
    simp at this
    have h : x≥4 := h
    have :=  calc
      (11:ℤ) = 11-0 := by numbers
      _ = 3*x := hx
      _ ≥ 3*4 := by rel[h]
      _ = 12 := by numbers
    simp at this
  · obtain ⟨x, hx⟩ := h3
    have hx : 10 = 3*x := by addarith[hx]
    obtain h|h := le_or_gt x 3
    have := calc
      10 = 3*x := hx
      _ ≤ 3*3 := by rel[h]
      _ = 9 := by numbers
    simp at this
    have h : x≥4 := h
    have :=  calc
      10 = 3*x := hx
      _ ≥ 3*4 := by rel[h]
      _ = 12 := by numbers
    simp at this
  · rfl

     

  
  



