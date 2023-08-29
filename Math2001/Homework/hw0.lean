/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Tactic.Numbers
import Library.Tactic.Extra

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/-! # Homework 0 -/


/- 5 points -/
theorem problem1 {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := calc
  n^2 = n * n := by ring
  _ ≥ 5*n := by rel[hn]
  _ = 2*n + 3*n := by ring
  _ ≥ 2 * n + 3 * 5 := by rel[hn]
  _ = 2 * n + 11 + 4:= by ring
  _ >  2 * n + 11 := by extra
