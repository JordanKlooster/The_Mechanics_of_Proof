/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.2: Proving equalities in Lean

This file should be worked through in parallel with the corresponding section of the book:
https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#proving-equalities-in-lean

I recommend splitting your screen to display the code and the book side by side! -/




-- Example 1.2.1
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) :
  (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a + b) ^ 2 := by ring
    _ = (a + b) ^ 2   := by ring -- did nothing so far
    _ = (a + b) * (a + b)   := by ring  --expand
    _ = a*a + a*b + a*b + b*b   := by ring -- multiply
    _ = a*a + 2*a*b + b*b   := by ring --combine like terms
    _ = a*a - 2*a*b + 2*a*b + 2*a*b + b*b   := by ring -- pulled +- 2*a*b out of zero
    _ = a*a - 2*a*b + 4*a*b + b*b   := by ring -- combined + terms
    _ = a*a - 2*a*b + b*b  + 4*a*b  := by ring -- moved + to right
    -- NOTE: (a-b)^2  ==  a^2 -ab -ab + b^2
    _ = (a-b)^2  + 4*a*b  := by ring
    _ = (a-b)^2  + 4*(a*b)  := by ring --bracket a*b
    _ = (4)^2  + 4*(1)  := by rw[h1, h2] -- swap things out
    _ = 16  + 4   := by ring
    _ = 20  := by ring


  --   example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) :(a + b) ^ 2 = 20 :=
  -- calc
  --   (a + b) ^ 2 = (a + b) ^ 2
  --   _ = (a + b) ^ 2
  --   _ = (a + b) ^ 2



-- -- Example 1.2.2.
-- -- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    -- r = r   := by ring
    -- _ = r   := by ring -- did nothing so far
    -- _ = r + 1 - 1  := by ring
    -- _ = r -(-1) - 1  := by ring
    -- _ = r -(r + 2 * s) - 1  := by rw[h2] -- doing it like this to cancel out r
    -- _ = r -r - 2*s - 1  := by ring
    -- _ = -2*s -1  := by ring
    -- _ = -2*(3) -1  := by rw[h1]
    -- _ = -6 -1  := by ring
    -- _ = -7  := by ring

  -- -- Their example
    r = r     +2*s  -2*s   := by ring -- +- 2s
    _ = -1          -2*s := by rw[h2]
    _ = -1 - 2*3 := by rw[h1]
    _ = -7 := by ring




-- -- Example 1.2.3
-- -- Exercise: replace the words "sorry" with the correct Lean justification.
-- example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
--     (2 * a * n + b * m) ^ 2 = 2 :=
--   calc

-- -- Example 1.2.4.
-- -- Exercise: type out the whole proof printed in the text as a Lean proof.
-- example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
--     d * (a * f - b * e) = 0 :=
--     calc







-- -- Example 1.2.1
-- example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
--   calc
--     (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
--     _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
--     _ = 20 := by ring

-- -- Example 1.2.2.
-- -- Exercise: replace the words "sorry" with the correct Lean justification.
-- example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
--   calc
--     r = r + 2 * s - 2 * s := by ring
--     _ = -1        - 2 * s := by rw[h2]
--     _ = -1        - 2 * 3 := by rw[h1]
--     _ = -7 := by ring

-- -- Example 1.2.3
-- -- Exercise: replace the words "sorry" with the correct Lean justification.
-- example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
--     (2 * a * n + b * m) ^ 2 = 2 :=
--   calc
--     (2 * a * n + b * m) ^ 2
--       = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2     * a ^ 2) := by ring
--     _ = 2 * 1               ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
--     _ = 2 := by ring                      --      (x) * (0)

-- -- Example 1.2.4.
-- -- Exercise: type out the whole proof printed in the text as a Lean proof.
-- example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
--     d * (a * f - b * e) = 0 :=
--     calc
--       d * (a * f - b * e)
--       _ = (a*d)*f - d*b*e := by ring
--       _ = (b*c)*f - d*b*e := by rw[h1]
--       _ = b*(c*f) - d*b*e := by ring
--       _ = b*(d*e) - d*b*e := by rw[h2]
--       _ = d*b*e   - d*b*e := by ring
--       _ = 0 := by ring
