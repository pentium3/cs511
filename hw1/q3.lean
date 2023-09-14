import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

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


-- page 24
example {p q r : Prop} (h1 : p ∧ ¬q → r) (h2 : ¬r) (h3 : p ) : q := by
  have h_nnq : ¬¬q := by
    intro h_nq
    have h_pnq : p ∧ ¬q := And.intro h3 h_nq
    have h_r : r := h1 h_pnq
    contradiction
  apply  notnotE h_nnq

