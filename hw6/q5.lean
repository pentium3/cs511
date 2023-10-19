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


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two



example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h : Tribalanced 1
  · use 1
    constructor
    · apply h
    · ring
      simp [Tribalanced] at h
      intro hx
      have hx2 := hx 2
      simp at hx2
      have: 4<3 :=  by
        calc
          4 = (1 + 2/2 )^2 := by ring
          _ < 3 := by addarith[hx2]
      contradiction
  · use 0
    constructor
    · intro h
      simp [Tribalanced] 
      numbers
    · intro hy
      simp at hy
      exact h hy



example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one
  . intro h
    simp [Superpowered] at h
    have hp : Prime ( 2^(2^5) + 1 )  := h 5 
    have hnp : ¬ Prime ( 2^(2^5) + 1 )  := by 
      apply not_prime 641 6700417
      numbers
      numbers
      numbers
    contradiction

