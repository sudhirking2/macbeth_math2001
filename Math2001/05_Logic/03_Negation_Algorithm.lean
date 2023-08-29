/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.Numbers
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · rintro (h|h) ⟨hp, hq⟩
    exact h hp 
    exact h hq

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := calc
    ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
      ↔ ∃ n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel[not_forall]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ (n ^ 2 < m ∧ m < (n + 1) ^ 2) := by rel[not_exists]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬ (n ^ 2 < m) ∨ ¬ (m < (n + 1) ^ 2) := by rel[not_and_or]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ,  (n ^ 2 ≥ m) ∨  (m ≥ (n + 1) ^ 2) := by rel[not_lt]


#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n, ∀ (m : ℤ), n ^ 2 < m → (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n^2 ≥ 2^2 := by rel[hn]
      _ > 2 := by numbers 

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor <;> intro h
  · push_neg at h
    assumption
  · intro hnp
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor <;> intro h
  · constructor
    · push_neg at h
      exact And.left h
    · intro hq
      exact h (fun _ ↦ hq)
  · rcases h with ⟨hp, hq⟩ 
    intro h 
    apply hq
    apply h hp 

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  push_neg
  rfl


example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by
    push_neg
    rfl 

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by
  push_neg 
  rfl


example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by
  push_neg
  rfl

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example {n m : ℕ} (h1 : n ∣  m) (h2 : m>0) : n>0 := by exact Nat.pos_of_dvd_of_pos h1 h2
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
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

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    dsimp[Prime] at hp
    push_neg at hp
    rcases hp with hp|hp
    · have := calc 2≤p:= by assumption
        _ < 2 := by rel[hp]
      numbers at this
    · obtain ⟨m, h1, h2, h3⟩ := hp
      obtain hp|hp := le_or_gt p 2
      interval_cases p
      · have := Nat.le_of_dvd (by numbers) h1
        interval_cases m
        · obtain ⟨k, h1⟩ := h1
          rw[zero_mul] at h1
          numbers at h1
        · numbers at h2
        · numbers at h3
      · obtain (hm | hm) := le_or_gt m 2
        interval_cases m
        · obtain ⟨k, hk⟩ := h1
          have := calc 0 = 0*k := by ring
            _ > 2 := by rw[← hk]; rel[hp]
          numbers at this
        · numbers at h2
        · exact H 2 (by numbers) hp h1
        · have this := H m (by exact Nat.le_of_lt hm) 
          have a0 := calc p>2 := by assumption
            _ > 0 := by numbers
          have a1 := Nat.le_of_dvd a0 h1
          have a2 : m<p := by exact Nat.lt_of_le_of_ne a1 h3
          specialize this a2
          contradiction
  · push_neg at H
    exact H



