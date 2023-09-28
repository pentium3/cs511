import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p


-- 5a
-- example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
--   have h := le_or_gt x 0


-- 5b
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hx⟩ := h
  intro ht
  rw [ht] at hx
  apply ne_of_lt hx
  ring



-- 5c
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h2a⟩ := h
  obtain hl2 | hg2 := le_or_gt a 2
  . apply ne_of_lt
    calc
      m = 2 * a := by rw[h2a]
      _ ≤ 2 * 2 := by rel[hl2]
      _ < 5 := by numbers
  . apply ne_of_gt
    have hg3: a ≥ 3 := by addarith[hg2]
    calc
      m = 2 * a := by rw[h2a]
      _ ≥ 2 * 3 := by rel[hg3]
      _ > 5 := by numbers

