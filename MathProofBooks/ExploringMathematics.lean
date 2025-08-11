import Mathlib.Data.Real.Basic
import Library.Basic

--following along in the book by Daniel Grieser


/- Problem 1.1 Cutting Up a Log
you have a log which is 7 meters long
how long does it take to cut it assuming each cut takes a minute?
1m peices

how about for log of size n

-/

example {w : ℚ} (h1 : c = 1) (h2 : l = 7)(h3 : t = (l-1)*c ) :
 t = 6 :=
  calc
    t = t := by ring
    _ = t := by ring

    _ = (l-1)*c := by rw[h3]
    _ = (7-1)*(1) := by rw[h1,h2]
    _ = (6)*(1) := by ring
    _ = 6 := by ring




/- Problem 1.2 A Problem with Zeros
how many zeros are at the end of: 1 * 2 * 3 * 4 *... * 99 * 100


-/




/- Problem 1.3 A Problem about lines in the plane
draw n non-parallel lines where no more that 2 meet at a single point.

How many regions to they cut the plane into?


-/
