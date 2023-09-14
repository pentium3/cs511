import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


example {p q r : Prop} (h : p → (q → r)) : p ∧ q → r := by
  intro h_pq
  obtain ⟨ h_p, h_q ⟩ := h_pq
  have h_qr : q → r := by apply h h_p
  apply h_qr h_q


-- page21
example {p q r : Prop} (h : p ∧ q → r) : p → (q → r) := by
  intro h_p
  intro h_q
  have h_pq : p ∧ q := ⟨h_p, h_q⟩
  have h_r : r := h h_pq
  apply h_r 


-- page 23
example {p q r : Prop} (h : p → (q → r) ) : (p → q) → (p → r) := by
  intro h_p
  intro h_pq
  have h_q : q := h_p h_pq
  have h_qr : q → r := h h_pq
  have h_r : r := h_qr h_q
  apply h_r




