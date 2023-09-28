import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p


-- 4a
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have htx : 0 < (-t) * x := by
      calc
        0 < (-x) * t := by addarith [hxt']
        _ = (-t) * x := by ring
    cancel x at htx
    have ht : (t < 0) := by addarith [htx]
    apply ne_of_lt
    apply ht


-- 4b
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring


-- 4c
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use ( p + q ) / 2
  have h1 : p < (p + q) / 2 := by 
    calc
      p = (p + p)/2 := by ring
      _ < (p + q)/2 := by addarith[h]
  have h2 : (p + q) / 2 < q := by
    calc
      (p + q) / 2 < (q + q) / 2 := by addarith[h]
      _ = q := by ring
  exact ⟨h1, h2⟩

