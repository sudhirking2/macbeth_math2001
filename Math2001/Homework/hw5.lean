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
  have thm1 (m:ℕ) := calc
      (3:ℤ) ^m  - 2 ^ m ≥ 2^m - 2^m := by rel[@pow_le_pow_of_le_left ℤ _ 2 3 (by numbers) (by numbers) m]
      _ = 0 := by ring
  
  have thm2 (m:ℕ) := calc
      (3:ℤ) ^ (m+1) - 2 ^ (m+1) = 3 ^ m * 3 - 2 ^ m * 2 := by rfl
      _ = (3:ℤ)^m * 3 - 2 ^ m*2 - 2^m + 2^m := by ring
      _ ≥ (3:ℤ)^m * 3 - 2 ^ m*2 - 2^m := by extra
      _ = 3*(3 ^m  - 2 ^ m):= by ring
  dsimp at thm2

  have thm3 (m:ℕ) :  m≥2 →  (3:ℤ)^(m)-2^(m) ≥ 5*3^(m-1) := by
    induction' m with m ih
    · simp
    · intro hm
      have hm : 1 ≤ m := by addarith [hm] 
      rw[le_iff_eq_or_lt] at hm
      rcases hm with hm|hm
      · obtain (hm|hm) := hm
        rw[hm]
        simp 
        numbers
        obtain (hm|hm) := hm
        

      · have hm : m ≥ 2 := by exact hm
        specialize ih hm 
        have : m-1-1+1 = m-1 := by
          apply Nat.sub_add_cancel
          exact Nat.le_pred_of_lt hm
        calc
          (3:ℤ) ^ (Nat.succ m + 1) - 2 ^ (Nat.succ m + 1)  ≥ 3 * (3 ^ Nat.succ m - 2 ^ Nat.succ m) := thm2 (Nat.succ m)
          _ ≥ 3 * (5 * 3 ^ (m - 2)) := by rel[ih]
          _ = 5* (3^(m-2)*3) := by ring
          _ = 5* 3^(Nat.succ (m-2)) := by rfl
          _ =  5* 3^(m-1-1+1) := by rfl
          _ = 5* 3^(m-1) := by rw[this]
  
  have thm4 (m:ℕ) (hm: m≥5) :  (5:ℤ) * 3 ^ (m - 2) ≥ 100 := by
    induction' m with m ih 
    · simp at hm
    · have hm : 5 ≤ m+1 := by exact hm
      rw[le_iff_eq_or_lt] at hm
      obtain (hm|hm) := hm
      · have hm : m=4 := by addarith[hm]
        rw[hm]
        numbers
      · have hm : m≥ 5 := by exact Iff.mp Nat.lt_succ hm
        have : Nat.succ m - 2 = Nat.succ (m-2) := by
          apply Nat.succ_sub
          exact calc 2 ≤ 5 := by numbers
            _ ≤ m := by assumption
        rw[this]
        calc (5:ℤ) * 3 ^ Nat.succ (m - 2) = 5 * (3 ^ (m-2)*3) := by rfl
          _ = (3:ℤ) * (5* 3 ^ (m-2)) := by ring
          _ ≥ (3:ℤ) * 100 := by rel[ih hm]
          _ ≥ 100 := by numbers
  use 5
  intro m hm
  specialize thm3 (m) (by exact le_of_add_le_right hm)
  have : m-1+1 = m := by refine tsub_add_cancel_of_le (by exact Nat.one_le_of_lt hm)
  have that : 3^(m-1-1)*3 =3^(m-1-1+1) := by rfl
  have : m-1-1+1 = m-1 := by apply? 
  calc
    (3:ℤ) ^ m = 3 ^ m - 2 ^ m + 2^m := by ring
    _ ≥ 5 * 3 ^ (m - 1) + 2^m := by rel[thm3]
    _ = 5 * 3 ^ (m-1-1)*3 +  2^m := by apply?
    _ ≥ 2 ^ m + 100 := by sorry






    example (a:ℕ) (ha: a>0) : a-1+1 = a := by exact Nat.sub_add_cancel ha


  use 100


theorem problem? : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 100
  intro x hx
  have h_lemma : 3^x ≥ x + 2^x
  have := calc  3 ^ x ≥  

  sorry



def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2 

/- 4 points -/
theorem problem6 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry
