import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


--6a
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ ≥ -1 := by numbers


--6b
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = ((a + 2 * b) + a) / 2 := by ring
    _ ≥ (4 + 3) / 2 := by rel[h2,h1]
    _ ≥ 3 := by numbers
    

--6c
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
     (x ^ 3) - 8 * (x ^ 2) + 2 * x = x * (x ^ 2) - 8 * (x ^ 2) + 2 * x := by ring
     _ ≥ 9 * (x ^ 2) - 8 * (x ^ 2) + 2 * x := by rel [hx]
     _ = (x ^ 2) + 2 * x := by ring
     _ ≥ (9 ^ 2) + 2 * 9 := by rel [hx]
     _ ≥ 3 := by numbers


