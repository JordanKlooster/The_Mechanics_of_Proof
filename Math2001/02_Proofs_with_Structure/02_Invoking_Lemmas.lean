/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.2.1
example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers


-- 2.2.2
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    0 = 0 := by ring
    _ < 0 + y^2 + 1 := by extra
    _ = y^2 + 1 := by ring




-- 2.2.3
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a^2 + b^2 := by extra
    _     = 0   := h1 --a ^ 2 ≤ 0  goal 1
  extra               --0 ≤ a ^ 2  goal 2


/-! # Exercises -/

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by

rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]




example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have h1 :=
  calc
    m = m := by ring
    _ = m := by ring
    _ = m + 1 -1 := by ring
    _ = 5 -1 := by rw[hm]
    _ = 4 := by ring
  -- have h2 :=
  -- calc
  --   0 = 0 := by ring
  --   _ < 0 + m := by extra
  --   _ < 0 + m := by extra


    -- _ = 4 := by ring
    -- _ = m := by rw[← h1]

  -- calc
  --   12 = 3*4 := by ring
  --   12 = 3*m := by rw[<- h1]
  calc
    3*m = 3*m := by ring
    _ = 3*4 := by rw[h1]
    _ = 12 := by ring
    _ > 6 := by numbers


    -- 6 = 6 := by ring
    -- _ = 6 := by ring
    -- _ = 4 + 2 := by ring
    -- _ < 4 + 2 + 6 := by extra
    -- _ = 12 := by ring
    -- _ = 3*4 := by ring
    -- _ = 3*m := by rw [← h1]

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  -- have h3 :=
  calc
    -- s = s := by ring
    -- _ = s := by ring
    -- _ = (2 * s)/2 := by ring
    -- _ ≤ (-4)/2 := by rw[h2]
    -- _ = -2 := by ring



    s = s := by ring
    _ = s := by ring
    _ = (3 * s)/3 := by ring
    _ ≤ (-6)/3 := by rel[h1]
    _ = -2 := by ring
  calc
    s = s := by ring
    _ = s := by ring
    _ = (2 * s)/2 := by ring
    _ ≥ (-4)/2 := by rel[h2]
    _ = -2 := by ring

    -- _ = s + 2* s - 2 * s := by ring
    -- _ = (3 * s)     - 2 * s := by ring
    -- _ ≥ (-6)     - 2 * s := by rw[h1]



-- trying to prove the sum of
-- example {x a y b c : Nat} (h1 : x = 2*a + 1) (h2 : y = 2*b + 1) : x + y = 2*c := by
--   sorry -- c can be any Nat

-- TODO: look at definitions again

-- nat ¬ ℕ ℕAT
-- my attempt to set up a thing asking you to prove that   odd * odd = odd
example {m n a b c : Nat} (h1 : m = 2*a + 1) (h2 : n = 2*b + 1) : m*n = 2*c + 1 := by
  sorry
  -- c can be any Nat







--   example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
--   apply ne_of_lt
--   calc
--     x = 3 * x / 3 := by ring
--     _ = 2 / 3 := by rw [hx]
--     _ < 1 := by numbers

-- example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
--   sorry

-- example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
--   apply le_antisymm
--   calc
--     a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
--     _ = 0 := h1
--   extra


-- /-! # Exercises -/


-- example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
--   sorry

-- example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
--   sorry
