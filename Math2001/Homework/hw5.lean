/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true
set_option linter.unusedVariables false

/-! # Homework 5 -/


/- 4 points -/
theorem problem1 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor <;> rintro ⟨h1, h2⟩
  · obtain ⟨x, h1⟩ := h1
    use x
    constructor <;> assumption
  · constructor
    · use h1
      exact And.left h2
    · exact And.right h2 


/- 5 points -/
theorem problem2 (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor <;> intro h
  · push_neg at h
    assumption
  · intro h1
    obtain ⟨x, _⟩ := h
    specialize h1 x
    contradiction

/- 4 points -/
theorem problem3 {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  obtain (hp | hp) := le_or_gt p 2
  obtain(hp|hp) : p<2 ∨ p=2 := by exact Nat.lt_or_eq_of_le hp
  · left
    assumption
  · right
    rw[hp] at hkp
    rw[hp] at hk
    rw[hp]
    have := Nat.le_of_dvd  (by numbers) hk
    interval_cases k
    · obtain ⟨hk, hk1⟩ := hk
      rw[zero_mul] at hk1
      numbers at hk1
    · numbers at hk1
    · numbers at hkp
  
  · right
    use k
    exact ⟨by assumption, by assumption, by assumption⟩ 

/- 4 points -/
theorem problem4 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  induction' n with n ih
  · left
    exact calc (5:ℤ)^0 = 1 := by numbers
      _ ≡ 1 [ZMOD 8] := Int.ModEq.refl 1
  · obtain (ih | ih) := ih
    · right
      calc (5:ℤ) ^ Nat.succ n = 5 ^ n * 5 := by rfl
        _ ≡ 1*5 [ZMOD 8] := by rel[ih]
        _ = 5 := by numbers
    · left
      calc (5:ℤ) ^ Nat.succ n = 5 ^ n * 5 := by rfl
        _ ≡ 5*5 [ZMOD 8] := by rel[ih]
        _ = 1 + 8*3 := by numbers
        _ ≡ 1 [ZMOD8] := by extra


/- 4 points -/
theorem problem5 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n
  simple_induction n with n ih
  intro a0
  numbers at a0
  intro hn
  have hn : 4≤n := by addarith[hn]
  rw[le_iff_eq_or_lt] at hn
  rcases hn with hn|hn
  · rw[← hn]
    numbers
  · have hn : n≥5 := by addarith [hn]
    exact calc
      (3:ℤ) ^ (n + 1) = 3 ^ n * 2 + 3^n  := by ring
      _ ≥ 3^n*2 := by extra
      _ ≥ (2 ^ n + 100)*2 := by rel[ih hn]
      _ = 2^(n+1) + 100 + 100 := by ring
      _ ≥ 2^(n+1) + 100 := by extra


def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2 

/- 4 points -/
theorem problem6 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with n ih; numbers; rfl
  exact calc 
    y (n+1) = (y n)^2 := rfl
    _ = (2^(2^n))^2 := by rw[ih]
    _ = 2 ^ (2 ^ (n+1)) := by ring
  
