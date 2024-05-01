
import Mathlib.Tactic

def test_def (a : ℝ) (h: a > 5) : a > 5 := by apply h
theorem test_theorem (a : ℝ) (h: a > 5) : a > 5 := by apply h

def above_five (a: ℝ) : Prop := a > 5

--def above_four (a: ℝ) (h: a > 5) : a > 4 := by
--  apply gt_trans
--  . show a > 5
--    exact h
--  . linarith


theorem above_four_t (a: ℝ) (h: a > 5) : a > 4 := by
  apply gt_trans
  . show a > 5
    exact h
  . linarith

theorem above_four_t2 : ∀ a : ℝ, ∀ _: a > 5, a > 4 := by
  intro a h
  apply gt_trans
  . show a > 5
    exact h
  . linarith

def test_def_2 (a : ℝ) (h: a > 5) : ∃ r: ℝ, r > 5 := by

  use a
