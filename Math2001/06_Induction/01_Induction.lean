/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option linter.unusedVariables false

namespace Nat

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left; use 0; ring
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right; use x; addarith[hx]
    · left; use x+1; rw [hx]; ring
    
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with n ih
  · calc a^0 = b^0 := by ring
    _ ≡ b^0 [ZMOD d] := by exact Int.ModEq.refl (b ^ 0) 
  · calc
    a ^ (n + 1) = a ^ n * a := rfl
    _ ≡ b^n *b [ZMOD d] := by rel[ih, h]
    _ = b^(n+1) := rfl
    
example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by  
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers 
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc  2^(k+1) = 2^k*2 := rfl
      _ ≥ k^2*2 := by rel[IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel[hk]
      _ = k^2 + 2*k+2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel[hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra



/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with n ih
  numbers
  calc 3 ^ (n + 1) = 3^n*3 := rfl
    _ ≥ (n ^ 2 + n + 1)*3 := by rel[ih]
    _ = (n + 1) ^ 2 + (n + 1) + 1 + 2*n^2:= by ring
    _ ≥ (n + 1) ^ 2 + (n + 1) + 1 := by extra
  
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with n ih
  · ring; numbers
  · have ha : 0 ≤ 1+a := by addarith [ha]

    exact calc 
      (1 + a) ^ (n + 1) = (1+a) * (1+a)^n  := by rfl
      _ ≥ (1+a) * (1+n*a) := by rel[ih]
      _ = 1+ (n+1)*a + n*a^2 := by ring
      _ ≥ 1 + (n+1)*a := by extra

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by  
  simple_induction n with n ih
  · left
    numbers
  · obtain (ih|ih) := ih
    · right
      exact calc (5:ℤ)^(n+1) = 5^n*5 := by rfl
        _ ≡ 1*5 [ZMOD 8] := by rel[ih]
        _ = 5 := by numbers
    · left
      exact calc (5:ℤ)^(n+1) = 5^n*5 := by rfl
        _ ≡ 5*5 [ZMOD 8] := by rel[ih]
        _ = 1 + 8*3 := by numbers
        _ ≡ 1  [ZMOD 8]:= by extra

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by  
  simple_induction n with n ih
  · left
    numbers
  · obtain (ih|ih) := ih
    · right
      exact calc (6:ℤ)^(n+1) = 6^n*6 := by rfl
        _ ≡ 1*6 [ZMOD 7] := by rel[ih]
        _ = 6 := by numbers
    · left
      exact calc (6:ℤ)^(n+1) = 6^n*6 := by rfl
        _ ≡ 6*6 [ZMOD 7] := by rel[ih]
        _ = 1 + 7*5 := by numbers
        _ ≡ 1  [ZMOD 7]:= by extra

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with n ih
  · left
    numbers
  · obtain (ih|ih|ih) := ih
    · right; right
      exact calc (4:ℤ)^(n+1) = 4^n*4 := by rfl
        _ ≡ 1*4 [ZMOD 7] := by rel[ih]
        _ = 4 := by numbers
    · left
      exact calc (4:ℤ)^(n+1) = 4^n*4 := by rfl
        _ ≡ 2*4 [ZMOD 7] := by rel[ih]
        _ = 1 + 7*1 := by numbers
        _ ≡ 1  [ZMOD 7]:= by extra
    · right; left
      exact calc (4:ℤ)^(n+1) = 4^n*4 := by rfl
        _ ≡ 4*4 [ZMOD 7] := by rel[ih]
        _ = 2 + 7*2 := by numbers
        _ ≡ 2  [ZMOD 7]:= by extra
  
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
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
  

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5; intro n; simple_induction n with n ih; intro ih; numbers at ih
  intro hn; have hn : 4≤n := by addarith[hn]
  rw[le_iff_eq_or_lt] at hn
  rcases hn with hn|hn; rw[← hn]; numbers
  have hn : n≥5 := by addarith [hn]
  exact calc
    2 ^ (n + 1) = 2^n*2 := by ring
    _ ≥ (n^2+4)*2 := by rel[ih hn]
    _ = n^2 + n*n + 8 := by ring
    _ ≥ n^2 +5*n+8 := by rel[hn]
    _ = (n + 1) ^ 2 + 4 + (3*n + 3):= by ring
    _ ≥ (n + 1) ^ 2 + 4 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10; intro n; simple_induction n with n ih; intro ih; numbers at ih
  intro hn; have hn : 9≤n := by addarith[hn]
  rw[le_iff_eq_or_lt] at hn
  rcases hn with hn|hn; rw[← hn]; numbers
  have hn : n≥10 := by addarith [hn]
  exact calc
    2 ^ (n + 1) = 2^n*2 := by ring
    _ ≥ (n ^ 3)*2 := by rel[ih hn]
    _ = n^3 + n*n^2 := by ring
    _ ≥ n^3 + 10*n^2 := by rel [hn]
    _ = n^3 + 3*n^2 + 7*n*n := by ring
    _ ≥ n^3 + 3*n^2 + 7*10*n := by rel[hn]
    _ = n^3 + 3*n^2 + 3*n + 67*n := by ring
    _ ≥ n^3 + 3*n^2 + 3*n + 67*10 := by rel[hn]
    _ = (n + 1) ^ 3 + 669 := by ring
    _ ≥ (n + 1) ^ 3 := by extra

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with n ih
  use 0; ring 
  have hn: a^(n+1) = a^n *a := by ring
  rw[hn]
  obtain ⟨k, hk⟩ := ih
  obtain ⟨l, hl⟩ := ha
  rw[hk, hl]
  use (k  + k * l * 2 + l ) 
  ring


theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  obtain (h|h) := even_or_odd a
  · exact h
  · have h:= Odd.pow h n
    rw[odd_iff_not_even] at h
    contradiction

