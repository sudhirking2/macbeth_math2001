/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  rcases hn with ⟨k, hk⟩
  rw[hk]
  use 7*k+1
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw[ha, hb]
  use 2*a*b+3*b+a+1
  ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨k, hm⟩ := hm
  rw[hm]
  use 3*k-1
  ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hn⟩ := hn
  rw[hn]
  use 2*k^2+2*k-3
  ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, hm⟩ := hm
  obtain ⟨b, hn⟩ := hn
  rw[hm,hn]
  use a+b
  ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, hp⟩ := hp
  obtain ⟨b, hq⟩ := hq
  rw[hp,hq]
  use a-b-2
  ring


example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x, ha⟩ := ha
  obtain ⟨y, hb⟩ := hb
  rw [ha, hb]
  use 3*x + y - 1
  ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨x, hr⟩ := hr
  obtain ⟨y, hs⟩ := hs
  rw[hr,hs]
  use 3*x -5*y-1 
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨a, hx⟩ := hx
  rw[hx]
  use 4*a^3 + 6*a^2 + 3*a
  ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨a, hn⟩ := hn
  rw[hn]
  use 2*a^2-a
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨x, ha⟩ := ha
  rw[ha]
  use 2*x^2 + 4*x -1
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨x, hp⟩ := hp
  rw[hp]
  use 2*x^2 + 5*x -1
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, hx⟩ := hx
  obtain ⟨b, hy⟩ := hy
  rw[hx,hy]
  use 2*a*b + a + b 
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain (⟨x, h⟩ | ⟨x, h⟩) := Int.even_or_odd n
  · rw[h]
    use 6*x^2 +3*x -1
    ring
  · rw[h]
    use 6*x^2 +9*x +2
    ring
  
example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain (⟨x, h⟩ | _) := Int.even_or_odd n
  · use n+1
    constructor
    extra
    use x
    rw[h]
  · use n
    constructor
    rfl
    assumption


  
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain (ha | ha) := Int.even_or_odd a
  obtain (hb | hb) := Int.even_or_odd b
  obtain (hc | hc) := Int.even_or_odd c
  · --even, even, even
    left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x-y
    rw[hx,hy]
    ring
  · -- even, even, odd
    left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x-y
    rw[hx,hy]
    ring
  obtain (hc | hc) := Int.even_or_odd c
  · -- even, odd, even
    right; left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hc
    use x+y
    rw[hx,hy]
    ring
  · -- even, odd, odd
    right; right
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hc
    use x-y
    rw[hx,hy]
    ring

  obtain (hb | hb) := Int.even_or_odd b
  obtain (hc | hc) := Int.even_or_odd c
  · --odd, even, even
    right; right
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hc
    use x-y
    rw[hx,hy]
    ring
  · -- odd, even, odd
    right; left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hc
    use x+y+1
    rw[hx,hy]
    ring
  obtain (hc | hc) := Int.even_or_odd c
  · -- odd, odd, even
    left;
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x-y
    rw[hx,hy]
    ring
  · -- odd, odd, odd
    right; right
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hc
    use x-y
    rw[hx,hy]
    ring

