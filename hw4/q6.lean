import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use




-- q6.1
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro hf
    have h1: (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x^2 + x - 6 := by ring
        _ = 0 := by rw [hf]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain hm | hn := h2
    left
    . calc
        x = (x + 3) - 3 := by ring
        _ = 0-3 := by rw [hm]
        _ = -3 := by numbers
    right
    . calc
        x = (x - 2) + 2 := by ring
        _ = 0 + 2 := by rw [hn]
        _ = 2 := by numbers
  . intro h
    obtain hp | hq := h
    . calc
        x ^ 2 + x - 6 = (x + 3) * (x - 2) := by ring
        _ = (-3+3) * (x - 2) := by rw [hp]
        _ = 0 := by ring
    . calc 
        x ^ 2 + x - 6 = (x - 2) * (x + 3) := by ring
        _ = (2-2) * (x + 3) := by rw [hq]
        _ = 0 := by ring




-- q6.2
-- example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by


