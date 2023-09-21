import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


--5c
example {p q : Prop} : ¬p ∧ ¬q → ¬(p ∨ q) := by
  intros h_np_a_nq h_p_o_q
  have h_np : ¬p := by apply And.left h_np_a_nq
  have h_nq : ¬q := by apply And.right h_np_a_nq
  cases h_p_o_q with
  | inr h_p => contradiction
  | inl h_q => contradiction

--5d
example {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q)  := by
  intros h_np_o_nq h_p_a_q
  have h_p : p := by apply And.left h_p_a_q
  have h_q : q := by apply And.right h_p_a_q
  cases h_np_o_nq with 
  | inr h_np => contradiction
  | inl h_nq => contradiction




