/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--TRYING to find a proof before hearing the answer
--  When a complicated proof simplifies everything https://www.youtube.com/watch?v=MhJN9sByRS0
-- example {b n k : ℕ} : b ^ n - 1 = (b-1) * k := by
--   have hn := le_or_succ_le n 1
--   obtain hn | hn := hn
--   apply ne_of_lt
--   calc
--     n ^ 2 ≤ 1 ^ 2 := by rel [hn]
--     _ < 2 := by numbers
--   sorry


  --3^2 -1 = 9-1 = 8 = 2*4
  --3^3 -1 = 27-1 = 26 = 2*13                          13 is 4 * 3 + 1
  --3^4 -1 = 81-1 = 80 = 2*40, 4*20, 8*10
  --3^5 -1 = 243-1 = 242 = 2*121, 2*11*11

  --4^2 -1 = 16-1 = 15      = 3 * 5 , 3 = 4-1
  --4^3 -1 = 64-1 = 63      = 3 * 21, 9 * 7 , 3 = 4-1         21 is 4 * 5 + 1
  --4^4 -1 = 256-1 = 255    = 3 * 85, 3 * 5 * 17 , 3 = 4-1    85 is 4 * 21 + 1
  --4^5 -1 = 1024-1 = 1023  = 3 * 341, 3 * 11 * 31 , 3 = 4-1  341 = 4 * 85 + 1

  --5^2 -1 = 25-1 = 24 = 4*6 , 3 = 4-1
  --5^3 -1 = 125-1 = 124 = 4 * 31,                       31 is 5*6 + 1
  --5^4 -1 = 625-1 = 624 = 4 * 156, 3 * 5 * 17 , 3 = 4-1      156 is 31 * 5 + 1
  --5^5 -1 = 3125-1 = 3124 = 4 * 781, 3 * 11 * 31 , 3 = 4-1    781 is 5 * 156 + 1




--2.3.1
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
obtain hx | hy := h
calc
  x*y + x = x*y + x := by rfl
  _ = x*y + x := by rfl
  _ = 1*y + 1 := by rw[hx]
  _ = y + 1 := by ring
calc
  x*y + x = x*y + x := by rfl
  _ = x*y + x := by rfl
  _ = x*(-1) + x := by rw[hy]
  _ = -x + x := by ring
  _ = 0 := by ring
  _ = -1 + 1 := by ring
  _ = y + 1 := by rw[hy]



-- lemma le_or_succ_le (a b : ℕ) : a ≤ b ∨ b + 1 ≤ a :=



--2.3.2
example {n : ℕ} : n ^ 2 ≠ 2 := by -- natural number, check smaller and bigger than 2
  have hn := le_or_succ_le n 1
  obtain h1 | h2 := hn
  apply ne_of_lt
  calc
    n^2 = n^2 := by rfl
    _ ≤ 1^2 := by rel[h1]
    _ = 1 := by ring
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n^2 = n^2 := by rfl
    _ ≥ 2^2 := by rel[h2]
    _ = 4 := by ring
    _ > 2 := by numbers

    -- 2^2 = 2^2 := by rfl
    -- _ ≤ n^2 := by rel[h2]
    -- _ ≤ n^2 := by rel[h2]


-- 2.3.3
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  -- left
  -- calc
  --   x = x := by rfl
  --   _ = (2*x)/2 := by ring
  --   _ = (2*x +1 -1)/2 := by ring
  --   _ = (5 -1)/2 := by rw[hx]
  --   _ = 4/2 := by ring
  --   _ = 2 := by ring
  right
  calc
    x = x := by rfl
    _ = (2*x)/2 := by ring
    _ = (2*x +1 -1)/2 := by ring
    _ = (5 -1)/2 := by rw[hx]
    _ = 4/2 := by ring
    _ = 2 := by ring


-- -- 2.3.4
-- example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
--   have h1 :=
--   calc
--     x ^ 2 - 3 * x + 2 = x ^ 2 - 3 * x + 2 := by rfl
--     _ = (x-2)*(x-1) := by ring -- this was my first thought, idk if I could make it work
--   have h3 :=
--   calc
--     (x-2)*(x-1) = (x-2)*(x-1) := by rfl
--     _ = x ^ 2 - 3 * x + 2 := by ring
--     _ = 0 := by rw[hx]
--   have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h3
--   -- left
--   have h4 :=
--   calc

  -- addarith h2

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hk | hr := h2
  left
  calc
    x = x := by rfl
    _ = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw[hk]
    _ = 1 := by ring
  right
  calc
    x = x := by rfl
    _ = x - 2 + 2 := by ring
    _ = 0 + 2 := by rw[hr]
    _ = 2 := by ring





-- -- 2.3.5
-- example {n : ℤ} : n ^ 2 ≠ 2 := by
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]









-- --2.3.1
-- example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
--   obtain hx | hy := h
--   calc
--     x * y + x = 1 * y + 1 := by rw [hx]
--     _ = y + 1 := by ring
--   calc
--     x * y + x = x * -1 + x := by rw [hy]
--     _ = -1 + 1 := by ring
--     _ = y + 1 := by rw [hy]

-- --2.3.2
-- example {n : ℕ} : n ^ 2 ≠ 2 := by
--   have hn := le_or_succ_le n 1
--   obtain hn | hn := hn
--   apply ne_of_lt
--   calc
--     n ^ 2 ≤ 1 ^ 2 := by rel [hn]
--     _ < 2 := by numbers
--   sorry
-- -- 2.3.3
-- example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
--   right
--   calc
--     x = (2 * x + 1 - 1) / 2 := by ring
--     _ = (5 - 1) / 2 := by rw [hx]
--     _ = 2 := by numbers

-- -- 2.3.4
-- example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
--   have h1 :=
--     calc
--     (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
--     _ = 0 := by rw [hx]
--   have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
--   sorry
-- -- 2.3.5
-- example {n : ℤ} : n ^ 2 ≠ 2 := by
--   have hn0 := le_or_succ_le n 0
--   obtain hn0 | hn0 := hn0
--   · have : 0 ≤ -n := by addarith [hn0]
--     have hn := le_or_succ_le (-n) 1
--     obtain hn | hn := hn
--     · apply ne_of_lt
--       calc
--         n ^ 2 = (-n) ^ 2 := by ring
--         _ ≤ 1 ^ 2 := by rel [hn]
--         _ < 2 := by numbers
--     · apply ne_of_gt
--       calc
--         (2:ℤ) < 2 ^ 2 := by numbers
--         _ ≤ (-n) ^ 2 := by rel [hn]
--         _ = n ^ 2 := by ring
--   · have hn := le_or_succ_le n 1
--     obtain hn | hn := hn
--     · apply ne_of_lt
--       calc
--         n ^ 2 ≤ 1 ^ 2 := by rel [hn]
--         _ < 2 := by numbers
--     · apply ne_of_gt
--       calc
--         (2:ℤ) < 2 ^ 2 := by numbers
--         _ ≤ n ^ 2 := by rel [hn]


-- /-! # Exercises -/

--1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hx | hy := h
  calc
    x ^ 2 + 1 = x ^ 2 + 1 := by rfl
    _ = x ^ 2 + 1 := by rfl
    _ = 4 ^ 2 + 1 := by rw[hx]
    _ = 16 + 1 := by ring
    _ = 17 := by ring
  calc
    x ^ 2 + 1 = x ^ 2 + 1 := by rfl
    _ = x ^ 2 + 1 := by rfl
    _ = (-4) ^ 2 + 1 := by rw[hy]
    _ = 16 + 1 := by ring
    _ = 17 := by ring

--2
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hx | hy := h
  calc
    x^2 -3*x + 2 = x^2 -3*x + 2 := by rfl
    _ = x^2 -3*x + 2 := by rfl
    _ = (x-1)*(x-2) := by ring
    _ = (1-1)*(1-2) := by rw[hx]
    _ = (0)*(1-2) := by ring
    _ = 0 := by ring
  calc
    x^2 -3*x + 2 = x^2 -3*x + 2 := by rfl
    _ = x^2 -3*x + 2 := by rfl
    _ = (x-1)*(x-2) := by ring
    _ = (2-1)*(2-2) := by rw[hy]
    _ = (2-1)*(0) := by ring
    _ = 0 := by ring


--3
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain hx | hy := h
  calc
    t ^ 2 - t - 6 = t ^ 2 - t - 6 := by rfl
    _ = t ^ 2 - t - 6 := by rfl
    _ = (t-3)*(t+2) := by ring
    _ = (-2-3)*(-2+2) := by rw[hx]
    _ = (-2-3)*0 := by ring
    _ = 0 := by ring
  calc
    t ^ 2 - t - 6 = t ^ 2 - t - 6 := by rfl
    _ = t ^ 2 - t - 6 := by rfl
    _ = (t-3)*(t+2) := by ring
    _ = (3-3)*(3+2) := by rw[hy]
    _ = 0*(3+2) := by ring
    _ = 0 := by ring


--4
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  calc
    x*y + 2*x = x*y + 2*x := by rfl
    _ = x*y + 2*x := by rfl
    _ = 2*y + 2*2 := by rw[hx]
    _ = 2*y + 4 := by ring
  calc
    x*y + 2*x = x*y + 2*x := by rfl
    _ = x*y + 2*x := by rfl
    _ = x*-2 + 2*x := by rw[hy]
    _ = 0 := by ring
    _ = -4 + 4 := by ring
    _ = 2*(-2) + 4 := by ring
    _ = 2*y + 4 := by rw[hy]

--5
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = s + t := by rfl
    _ = s + t := by rfl
    _ = 3 -t + t := by rw[h]
    _ = 3 := by ring


--6
example {a b : ℚ} (h : a + 2*b < 0) : b < a/2 ∨ b < -a/2 := by
  left
  calc
    b = b := by rfl
    _ = b := by rfl
    _ = (2*b)/2 := by ring
    _ = (2*b - 0)/2 := by ring
    _ = (2*b - 0)/2 := by ring

--7
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  sorry

--8
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

--9
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry

--10
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

--11
example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

--12
example {x : ℤ} : 2 * x ≠ 3 := by
  sorry

--13
example {t : ℤ} : 5 * t ≠ 18 := by
  sorry

--14
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
