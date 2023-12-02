import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function

/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp [Surjective]
  push_neg
  use fun x ↦ x
  constructor
  . intro k
    use k
    extra
  . use 1
    intro x
    have hx := le_or_succ_le x 0
    obtain h0 | h1 := hx
    · apply ne_of_lt
      calc
        2 * x ≤ 2 * 0 := by rel[h0]
        _ < 1 := by ring
    · apply ne_of_gt
      calc
        2 * x ≥ 2 * 1 := by rel[h1]
        _ > 1 := by ring



/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp[Surjective]
  push_neg
  use 0
  use 1
  intro x
  ring
  numbers



/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp[Injective]
  intro x y h
  have hx := lt_trichotomy x y
  obtain  hl | he | hg := hx
  . have h := ne_of_lt (hf x y hl)
    contradiction
  . apply he
  . have h := ne_of_gt (hf y x hg)
    contradiction



/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp[Surjective]
  intro y
  simple_induction y with k IH
  · use x0
    apply h0
  · obtain ⟨x, hx⟩ := IH
    use i x
    rw[hi]
    rw[hx]



/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  dsimp [Bijective, Injective, Surjective]
  constructor
  · intro x y h
    calc
      x = ((4 - 3*x) - 4) / (-3)  := by ring
      _ = ((4 - 3*y) - 4) / (-3)  := by addarith[h]
      _ = y := by ring
  · intro y
    use (4 - y) / 3
    ring



/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  dsimp[Injective]
  dsimp[Surjective]
  push_neg
  constructor
  · use 1
    use -3
    constructor
    · ring
    · numbers



def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

/- 3 points -/
theorem problem5c : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    calc
      v (u x) = ((u x) - 1) / 5 := by rw[v]
      _ = (5 * x + 1 - 1) / 5 := by rw[u]
      _ = x := by ring
  · ext x
    calc
      u (v x) = (5 * (v x) + 1) := by rw[u,v]
      _ = 5 * ((x - 1) / 5) + 1 := by rw[v]
      _ = x := by ring



/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective]
  intro x y h
  apply hf (hg h)
