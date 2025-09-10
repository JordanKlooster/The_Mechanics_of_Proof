/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--Let a and b be real numbers and suppose that a-5b = 4 and b+2 = 3
-- Show that a = 9
-- example 2.1.1
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4         + 5 * b := by rw [h1]
    _ = 4         + 5 * 1 := by rw [hb]
    -- _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


-- 2.1.2
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1] -- just h1
    _ =     2 * n - 1 := by ring
    _ ≤     2 * 5 - 1 := by rel [h2] --swap n for 5
    _ =     10  - 1 := by ring
    _ = 9 := by numbers
  calc
    m = m := by ring
    _ = m := by ring
    _ = m + 3 -3 := by ring
    _ ≤ 9 -3 := by rel[h3]
    _ = 6 := by ring


-- example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
--   have h3 :=
--   calc
--     m + 3 ≤ 2 * n - 1 := by rel [h1] -- just h1
--     _ ≤ 2 * 5 - 1 := by rel [h2]
--     _ = 9 := by numbers
--   addarith [h3]  -- m + 3 ≤ 9  means m ≤ 6 done

-- 2.1.3
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith[h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith[h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3,h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic


--2.1.4
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3 -- goes from t*t = 3*t  to t = 3
  addarith [h3]


--2.1.5
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  -- have h3 :=

  -- b^2 = a^2 -1 --JK: Here's my process
  -- _ = 0 -1 rel[h2]
  -- _ = -1 ring but b^2 is squared so it's positive, so a^2 has to be at least 1
  -- and this  a  has to be at least 1

  have h3 :=
  calc
    a ^ 2 = a ^ 2  := by rfl
    _ = a^2  := by ring

    _ = b^2 + 1 := by rw [h1]
    _ ≥ 1 := by extra  -- a^2 >= b^2 +1  so  a^2 >= b^2 +1 - b^2 because b^2 is >=0
    _ = 1 ^ 2 := by ring -- 1 == 1^2
  cancel 2 at h3 --cancel the squares

  -- OK, I think I got a better grasp of extra
  -- can take away from the smaller side or add to the bigger side
  -- if you know the sign, (>=0 or <=0) and x^2 is a way to do that









--2.1.6 -- completed by Jordan Kloosterman
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h1 :=
  calc
    x = x := by ring
    _ = x + 3 - 3 := by ring
    _ ≤ 2 -3 := by rel[hx]
    _ = -1 := by ring
  -- have h2 :=
  -- calc
  --   y = y := by ring
  calc
    y = y := by ring
    _ = y := by ring
    _ = y - 2    + 2 := by ring
    _ = y + 2*-1 + 2 := by ring
    _ >= y + 2*x + 2:= by rel[h1]
    _ >= 3       + 2 := by rel[hy]
    _ = 5 := by ring
    _ > 3 := by numbers




--2.1.7 -- magnitude of a is smaller than or = to magnitude of b, and b is > 0
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 :=
  calc
    0 = 0 := by ring
    _ = 0 + b - b := by ring
    _ = b + (-b) := by ring
    _ ≤ b + a := by rel[h1]
  have h4 :=
  calc
    0 = 0 := by ring
    _ = 0 + a - a := by ring
    _ = (a) - a := by ring
    _ ≤ b - a := by rel[h2]
  calc
    a ^ 2 = a ^ 2 := by ring
    _ ≤     a ^ 2 + (b + a) * (b - a):= by extra
    _ =     a ^ 2 + b^2 - a^2:= by ring -- difference of squares
    _ = b^2 := by ring -- cancel a^2


--2.1.8
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h2 :=
  calc
    0 = 0 := by ring
    _ = 0 + b - b := by ring
    _ = b - b := by ring
    _ ≤ b - a := by rel[h]
  -- have h3 :=
  -- calc
  --   0 = 0 := by ring
  --   _ = 0 := by ring
  calc
    a^3 = a^3 := by ring
    _ = a^3 := by ring
    _ ≤ a^3 + ((b-a)*((b-a)^2 + 3*(b+a)^2 ))/4:= by extra --it's non negative so I can add it to RS of <=
    _ = a^3 + ((b-a)*((b-a)*(b-a) + 3*(b+a)*(b+a) ))/4:= by ring
    _ = a^3 + ((b-a)*((b^2 -2*a*b + a^2) + 3*(b^2 + 2*a*b + a^2 ) ))/4 := by ring
    _ = a^3 + ((b-a)*(b^2 -2*a*b + a^2 + 3*b^2 + 6*a*b + 3*a^2 ))/4 := by ring
    _ = a^3 + ((b-a)*(4*b^2 + 4*a*b + 4*a^2 ))/4 := by ring
    _ = a^3 + (4*b^3 + 4*a*b^2 + 4*a^2*b   -   4*b^2*a - 4*a^2*b - 4*a^3)/4 := by ring
    _ = a^3 + (4*b^3 - 4*a^3)/4 := by ring
    _ = a^3 + b^3 - a^3 := by ring
    _ = b^3 := by ring




/-! # Exercises -/

--2.1.9
--1.
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
  calc
    x* (x+2) = x* (x+2) := by ring
    _ =        x* (x+2) := by ring
    _ =        x*x + 2*x := by ring
    _ =        x^2 + 2*x := by ring
    _ =        4 + 2*x := by rw[h1]
    _ =        2*(2) + 2*x := by ring
    _ =        2*(x + 2) := by ring
  -- calc
  --   x = x := by ring
  --   _ = x := by ring
  --   _ = x + 2 - 2:= by ring
  --   _ = x*(x + 2)/x - 2:= by ring
  --   _ = 2*(x + 2)/x - 2:= by rw[h3]
  --   _ = 2*(x + 2)/x - 2:= by ring
  cancel (x+2) at h3

--2.
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 :=
  calc
    (n-2)^2 = (n-2)^2 := by ring
    _ = (n-2)^2 := by ring
    _ = (n-2)*(n-2) := by ring
    _ = n^2 -2*n - 2*n +4 := by ring
    _ = n^2 -4*n +4 := by ring
    _ = n^2 +4 -4*n := by ring
    _ = 4*n -4*n := by rw[hn]
    _ = 0 := by ring
    -- _ = 0^2 := by ring
  -- have h2 :=
  cancel (↑2) at h1 -- now   n-2 = 0
  addarith[h1]
  -- d ')', '_', '↑', '↥', '⇑'
  -- have h2 :=
  -- calc

--3.                    y = 1/x   x = 1/y
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have h3 :=
  calc
    0 = 0 := by ring
    _ < 0 + x * y := by extra
    _ = x * y := by ring
  cancel x at h3 --y cannot be zero, it's +
  calc
    y = y := by ring
    _ = y * 1 := by ring
    _ ≤ y * x := by rel[h2]
    _ = x * y := by ring
    _ = 1 := by rw[h]


    -- y = y := by ring
    -- _ = y := by ring
    -- -- _ ≤ y*x := by rel[h2,h3]
    -- _ ≤ y*x := by extra
    -- -- _ ≤ y*x := by tac
    -- _ = x * y := by ring
    -- _ = 1 := by rw[h]

    -- 1 = 1 := by ring
    -- _ = (1) := by ring
    -- _ = x * y := by rw[<- h]


  -- process
  -- y=y
  -- _ ≤ y + 3    or _ ≤ y -3    it's       y ≤ y + 3

    -- _ = y





-- example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
--   have h3 :=
--   calc t * t = t ^ 2 := by ring
--     _ = 3 * t := by rw [h1]
--   cancel t at h3
--   addarith [h3]


-- example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
--   have h3 :=
--   calc
--     a ^ 2 = b ^ 2 + 1 := by rw [h1]
--     _ ≥ 1 := by extra
--     _ = 1 ^ 2 := by ring
--   cancel 2 at h3


-- example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
--   sorry

-- example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
--   sorry

-- example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
--   sorry

-- /-! # Exercises -/


-- example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
--   sorry

-- example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
--   sorry

-- example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
--   sorry
