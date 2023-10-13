
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


-- q5.1
-- example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
--   sorry

--q5.2
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  simp
  constructor
  . numbers
  intro x hx
  calc
      x = (4 * x ) / 4 := by ring
      _ = (4 * x - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4 := by rw[hx]
      _ = 3 := by ring


--q5.3
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro n
    addarith
  intro n hn
  have hx : n ≥ 0 := by extra
  have hy := by apply hn 0
  apply le_antisymm 
  apply hy
  apply hx


