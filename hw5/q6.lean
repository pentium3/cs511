
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



--q6.1
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  -- the case `m = 1`
  left
  addarith [hm]
  -- the case `1 < m`
  have hlemp : m ≤ p := Nat.le_of_dvd hp' hmp
  obtain hem | hlm := Nat.eq_or_lt_of_le hlemp
  -- the case `m=p`
  right
  apply hem
  -- the case `m<p`
  have h2 : ¬m∣p := by  apply H m hm_left hlm
  contradiction




-- q6.2
-- example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--     (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
--   sorry


-- q6.3
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  cancel n at h


-- q6.4
-- example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
--   sorry



