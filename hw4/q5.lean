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

-- lemma abs_le_of_sq_le_sq' (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r



-- q5.1
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have hf: (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain hx | hy := hf
  · calc
    b = 2 * (( a + b ) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [hx]
    _ = a := by ring
  · calc
    a = 2 * (( a + b ) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [hy]
    _ = b := by ring




-- q5.2
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  have hxy := calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ 3 ^ 2 := by numbers
  have hf : (0 : ℝ) ≤ 3 := by numbers
  exact And.left (abs_le_of_sq_le_sq' hxy hf)



-- q5.3
-- example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
--  ss


-- q5.4
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 7
  intro x hf
  calc
    x ^ 3 + 3 * x  = x * ( x ^ 2  + 3 ) := by ring
    _ ≥ 7 * ( x ^ 2  + 3 ) := by rel[hf]
    _ = 7 * x ^ 2 + 21 := by ring  
    _ = 7 * x ^ 2 + 12 + 9 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra


