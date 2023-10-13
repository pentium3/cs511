
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


--q4.1
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  dsimp [(· ∣ ·)]
  constructor
  · intro h_l
    obtain ⟨a, ha⟩ := h_l
    constructor
    · use 9 * a
      calc
        n = 63*a := by rw [ha]
        _ = 7*(9*a) := by ring
    · use 7 * a
      calc
        n = 63*a := by rw [ha]
        _ = 9*(7*a) := by ring
  · intro h_r
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h_r
    use (4 * b - 3 * a)
    calc
      n = 4 * 7 * n - 3 * 9 * n := by ring
      _ = 28 * n - 27 * n := by ring
      _ = 28 * (9 * b) - 27 * n := by rw [hb]
      _ = 28 * (9 * b) - 27 * (7 * a) := by rw [ha]
      _ = 63 * 4 * b - 63 * 3 * a := by ring
      _ = 63 * (4 * b - 3 * a) := by ring


--q4.2
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry



